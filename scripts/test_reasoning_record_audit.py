#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Offline unit and real-corpus mutation tests for native long-record assembly."""
from __future__ import annotations

import copy
import json
from pathlib import Path
import shutil
import sys
import tempfile
import unittest
import subprocess
import contextlib
import io

import reasoning_record_audit as audit


class SpanTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.rel = 'paper/reasoning-parts/erdos269/core.tex'
        self.path = self.root / self.rel
        self.path.parent.mkdir(parents=True)

    def read(self, text, spec):
        self.path.write_text(text)
        return audit.support_span(audit.Inputs(self.root), {'path': self.rel, **spec})

    def test_named_closed_proof_selected(self):
        loc, text = self.read(r'\begin{proof}[Proof of \ref{a}]A reason.\end{proof}',
                              {'selector': 'proof_of', 'label': 'a'})
        self.assertEqual(loc['line'], 1)
        self.assertIn('A reason.', text)

    def test_missing_named_proof_refused(self):
        with self.assertRaisesRegex(audit.RecordInputError, 'got 0'):
            self.read(r'\begin{proof}[Proof of \ref{other}]A reason.\end{proof}',
                      {'selector': 'proof_of', 'label': 'a'})

    def test_duplicate_named_proof_refused(self):
        block = r'\begin{proof}[Proof of \ref{a}]A reason.\end{proof}'
        with self.assertRaisesRegex(audit.RecordInputError, 'got 2'):
            self.read(block + '\n' + block, {'selector': 'proof_of', 'label': 'a'})

    def test_commented_proof_cannot_satisfy(self):
        with self.assertRaisesRegex(audit.RecordInputError, 'got 0'):
            self.read('% ' + r'\begin{proof}[Proof of \ref{a}]Fake.\end{proof}',
                      {'selector': 'proof_of', 'label': 'a'})

    def test_unclosed_proof_refused(self):
        with self.assertRaises(audit.RecordInputError):
            self.read(r'\begin{proof}[Proof of \ref{a}]No end.', {'selector': 'proof_of', 'label': 'a'})

    def test_adjacent_proof_does_not_steal_next_theorem(self):
        with self.assertRaisesRegex(audit.RecordInputError, 'another'):
            self.read(r'\begin{theorem}\label{a}A\end{theorem}'
                      r'\begin{theorem}B\end{theorem}\begin{proof}B proof\end{proof}',
                      {'selector': 'adjacent_proof', 'label': 'a'})

    def test_adjacent_proof_skips_nested_display_end(self):
        loc, text = self.read(r'\begin{theorem}\label{a}'
                              r'\begin{equation*}A\end{equation*}'
                              r'\begin{equation*}B\end{equation*}\end{theorem}'
                              r'\begin{proof}Whole argument.\end{proof}',
                              {'selector': 'adjacent_proof', 'label': 'a'})
        self.assertIn('Whole argument.', text)
        self.assertNotIn('equation*', text)

    def test_bounded_span_requires_both_delimiters(self):
        with self.assertRaisesRegex(audit.RecordInputError, 'closing'):
            self.read('Start reason', {'selector': 'between', 'start': 'Start', 'end': 'End'})

    def test_bounded_span_start_must_be_unique(self):
        with self.assertRaisesRegex(audit.RecordInputError, 'exactly once'):
            self.read('Start End Start End', {'selector': 'between', 'start': 'Start', 'end': 'End'})

    def test_numbers_and_quantifiers_survive_normalization(self):
        self.assertNotEqual(audit.normalized('for every n > 2'), audit.normalized('for some n > 3'))

    def test_labels_and_whitespace_do_not_hide_exact_duplicates(self):
        self.assertEqual(audit.normalized(r'\label{a} P  implies Q'),
                         audit.normalized(r'\label{b} P implies Q'))

    def test_path_traversal_absolute_and_dotgit_refused(self):
        for p in ('../outside', '/absolute', 'paper/../outside', '.git/config', 'paper\\x'):
            with self.subTest(path=p), self.assertRaises(audit.RecordInputError):
                audit.safe_path(self.root, p)

    def test_symlink_refused(self):
        (self.root/'link').symlink_to(self.path)
        with self.assertRaisesRegex(audit.RecordInputError, 'symlink'):
            audit.safe_path(self.root, 'link')

    def test_declaration_partial_overlap_is_not_full_match(self):
        def row(*names):
            return {'lean': {'declarations': [{'file': 'a.lean', 'name': n} for n in names]}}
        self.assertNotEqual(audit.declaration_set(row('A', 'B')), audit.declaration_set(row('A')))

    def short_disposition(self):
        path = 'paper/269/short.tex'
        target = self.root/path
        target.parent.mkdir(parents=True, exist_ok=True)
        body = r'\begin{proof}A complete retained argument.\end{proof}'
        target.write_text(body)
        row = {'statement_sha256': 'sha256:statement', 'problem': 269}
        disposition = {'action': 'explained_in_short', 'rationale': 'The proof is retained here.',
                       'review_status': 'Type A source-reading; no independent mathematical review.',
                       'short_statement_sha256': row['statement_sha256'],
                       'support': {'path': path, 'selector': 'between', 'start': r'\begin{proof}',
                                   'end': r'\end{proof}', 'sha256': audit.digest(body)}}
        return path, row, disposition

    def test_retained_short_proof_does_not_certify_long_correspondence(self):
        path, row, disposition = self.short_disposition()
        support = audit.short_proof_support(audit.Inputs(self.root), disposition, row, [path])
        self.assertTrue(support['long_correspondence'].startswith('open;'))
        self.assertIn('proof_correctness_not_checked', support['validation'])

    def test_changed_short_proof_refused(self):
        path, row, disposition = self.short_disposition()
        (self.root/path).write_text(r'\begin{proof}Unreviewed changed argument.\end{proof}')
        with self.assertRaisesRegex(audit.RecordInputError, 'stale short proof'):
            audit.short_proof_support(audit.Inputs(self.root), disposition, row, [path])

    def test_changed_short_statement_refused(self):
        path, row, disposition = self.short_disposition()
        row['statement_sha256'] = 'sha256:changed'
        with self.assertRaisesRegex(audit.RecordInputError, 'short statement changed'):
            audit.short_proof_support(audit.Inputs(self.root), disposition, row, [path])

    def test_short_proof_cannot_come_from_another_problem(self):
        path, row, disposition = self.short_disposition()
        row['problem'] = 251
        with self.assertRaisesRegex(audit.RecordInputError, 'another problem'):
            audit.short_proof_support(audit.Inputs(self.root), disposition, row, [path])

    def test_statement_removal_remains_in_delta(self):
        c = {'short_claim': 'a', 'state': 'unresolved', 'statement_sha256': 'x', 'long_locations': []}
        d = audit.report_delta({'pairs': [{'claims': [c]}]}, {'pairs': [{'claims': []}]})
        self.assertEqual(d['removed_short_claims_requires_review'], ['a'])


class CorpusTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.base = audit.report()
        if cls.base['status'] == 'refusal':
            raise RuntimeError(cls.base['reason'])
        cls.links = json.loads((audit.ROOT/audit.LINKS).read_text())
        cls.link = next(x for x in cls.links['links'] if x['short_id'].endswith('#res:strict-mixed-supports'))

    def clone_inputs(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        root = Path(tmp.name)
        for rel in self.base['input_sha256']:
            path = root/rel
            path.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(audit.ROOT/rel, path)
        return root

    def test_all_eight_pairs_are_examined(self):
        self.assertEqual({p['problem'] for p in self.base['pairs']}, {68,243,249,251,257,269,1041,1049})
        self.assertEqual(self.base['summary']['short_claims'] + self.base['summary']['long_claims'],
                         len(json.loads((audit.ROOT/'docs/paper_lean_coverage.json').read_text())['rows']))

    def test_real_gaps_are_not_turned_into_success(self):
        self.assertGreater(self.base['summary']['long_correspondence_open'], 0)
        self.assertNotEqual(self.base['status'], 'refusal')
        for pair in self.base['pairs']:
            for c in pair['claims']:
                if c['state'] in ('unresolved', 'short_proof_explained_long_link_open'):
                    self.assertEqual(c['matches'], [])
                    self.assertIsNotNone(c['short_location'])

    def test_no_compilation_claim_from_source_presence(self):
        for p in self.base['pairs']:
            for c in p['claims']:
                for m in c['matches']:
                    if m['support']['kind'] == 'registered_lean_evidence':
                        self.assertIn('UNRUN', m['support']['validation'])

    def test_ordinary_authored_status_not_upgraded(self):
        p = next(p for p in self.base['pairs'] if p['problem']==257)
        c = next(c for c in p['claims'] if c['short_claim']==self.link['short_id'])
        self.assertEqual(c['state'], 'authored_proof_text_linked')
        self.assertEqual(c['ledger_lean_status'], 'none')
        self.assertEqual(c['ledger_comparator_status'], 'not_applicable')

    def test_real_missing_proof_is_reported(self):
        root = self.clone_inputs()
        loc, _ = audit.support_span(audit.Inputs(root), self.link['support'])
        path = root/loc['path'];lines=path.read_text().splitlines(keepends=True)
        del lines[loc['line']-1:loc['end_line']]
        path.write_text(''.join(lines))
        value = audit.report(root, [257])
        self.assertNotEqual(value['status'], 'refusal', value.get('reason'))
        findings = value['pairs'][0]['findings']
        self.assertTrue(any(x['code']=='stale_or_missing_proof' and x['short_claim']==self.link['short_id'] for x in findings))
        self.assertEqual(value['status'], 'findings')
        with contextlib.redirect_stderr(io.StringIO()):
            rc = audit.main(['--root', str(root), '--problem', '257', '--output', str(root/'mutant.json')])
        self.assertEqual(rc, 1)

    def test_real_changed_proof_does_not_get_rehashed_away(self):
        root = self.clone_inputs()
        loc, _ = audit.support_span(audit.Inputs(root), self.link['support'])
        path=root/loc['path'];lines=path.read_text().splitlines(keepends=True)
        lines[loc['line']] += 'Unreviewed change.\n';path.write_text(''.join(lines))
        value=audit.report(root,[257])
        self.assertTrue(any(x['code']=='stale_or_missing_proof' and 'stale support' in x['detail']
                            for x in value['pairs'][0]['findings']))

    def test_real_duplicate_assertion_outside_ledger_is_detected(self):
        root=self.clone_inputs();path=root/'paper/reasoning-parts/erdos269/core.tex'
        text=path.read_text()
        label=r'\label{long269:res:distinct-height-235}'
        self.assertEqual(text.count(label), 1)
        anchor=text.index(label)
        start=text.rfind(r'\begin{theorem}[',0,anchor)
        self.assertGreaterEqual(start, 0)
        self.assertNotIn(r'\end{theorem}',text[start:anchor])
        end=text.index(r'\end{theorem}',anchor)+len(r'\end{theorem}')
        statement=text[start:end]
        self.assertIn(label, statement)
        duplicate=statement.replace(label,r'\label{seed:duplicate}')
        self.assertNotEqual(duplicate,statement)
        path.write_text(text+'\n\n'+duplicate+'\n')
        value=audit.report(root,[269])
        self.assertTrue(any(x['code']=='duplicate_statement' for x in value['pairs'][0]['findings']))
        self.assertGreater(value['summary']['global_findings'],0)

    def test_real_duplicate_prose_is_detected(self):
        root=self.clone_inputs();path=root/'paper/reasoning-parts/erdos269/core.tex'
        paragraph=' '.join(['This passage records the scope of the route and its hypotheses.']*6)
        path.write_text(path.read_text()+'\n\n'+paragraph+'\n\n'+paragraph+'\n')
        value=audit.report(root,[269])
        self.assertTrue(any(x['code']=='duplicate_passage' for x in value['pairs'][0]['findings']))

    def test_missing_required_manifest_refuses(self):
        root=self.clone_inputs();(root/audit.LINKS).unlink()
        value=audit.report(root,[269]);self.assertEqual(value['status'],'refusal')
        self.assertIn('record_links.json', value['reason'])

    def test_changed_input_invalidates_saved_navigation(self):
        root=self.clone_inputs();path=root/'paper/reasoning-parts/erdos269/core.tex'
        path.write_text(path.read_text()+'\n% changed source\n')
        self.assertTrue(any('stale record audit input' in e for e in audit.freshness_errors(root,self.base)))

    def test_portable_checker_can_recompute_without_scripts_on_path(self):
        code = ("import sys; from pathlib import Path; "
                "sys.path.insert(0, str(Path.cwd()/'docs/papers')); "
                "import check_paper_corpus as c; "
                "errors=c.record_navigation_errors(Path.cwd(),require_links=True); "
                "import reasoning_record_audit as records; "
                "import json; print(json.dumps({'errors':errors,'live_status':records.report()['status']}))")
        result=subprocess.run([sys.executable, '-c', code], cwd=audit.ROOT,
                              capture_output=True, text=True, timeout=20)
        self.assertEqual(result.returncode, 0, result.stderr)
        value = json.loads(result.stdout)
        self.assertEqual(value['live_status'], self.base['status'])
        self.assertFalse(any('unreadable' in e for e in value['errors']))

    def test_authored_hash_bound_alias_difference_is_accounted_for(self):
        p=next(p for p in self.base['pairs'] if p['problem']==257)
        self.assertFalse(any(f['code']=='possible_stale_passage' and
                             f.get('short_claim')==self.link['short_id'] for f in p['findings']))

    def test_unknown_selection_refuses(self):
        self.assertEqual(audit.report(problems=[999])['status'],'refusal')

    def test_renderer_marks_unresolved_matches_and_contains_support_path(self):
        sys.path.insert(0,str(audit.ROOT/'docs/papers'))
        try:
            import paper_corpus_renderer as renderer
        finally:
            sys.path.pop(0)
        pair=next(p for p in self.base['pairs'] if p['problem']==257)
        text=renderer.render_record_navigation(pair,audit.BOUNDARY)
        self.assertIn('No accepted correspondence',text)
        self.assertIn('paper/reasoning-parts/erdos257/a257_front.tex',text)
        self.assertIn('correctness of ordinary proofs',text)
        self.assertIn('Retained short-paper argument:',text)
        self.assertIn('No accepted long-record correspondence is established by this disposition.',text)


if __name__ == '__main__':
    unittest.main()
