#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Offline v2 paper-contract regression tests, active under python -O.

The fixtures test enforcement and traceability, not independent semantic truth.
Invoked by the existing counts/architecture test entrypoints in release checks.
"""
from __future__ import annotations
import copy
import re
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
import build_systems_paper_counts as counts
import systems_paper_evidence as evidence

ROOT=Path(__file__).resolve().parent.parent
PAPER=ROOT/'paper/systems/claim-faithful-publication-systems-paper.tex'

class EvidenceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.text=PAPER.read_text();cls.ledger=evidence.read_json(ROOT/'docs/systems_paper_sentences.json')
    def check(self,text=None,ledger=None):
        return evidence.validate_bound_paper(self.text if text is None else text,ROOT,self.ledger if ledger is None else ledger)
    def test_real_paper(self): self.assertEqual(self.check(),[])
    def test_changed_sentence(self):
        a=self.ledger['sentences'][0]['text'];self.assertTrue(self.check(self.text.replace(a,a+' Unsupported claim.',1)))
    def test_missing_row(self):
        v=copy.deepcopy(self.ledger);v['sentences'].pop();self.assertTrue(self.check(ledger=v))
    def test_extra_row(self):
        v=copy.deepcopy(self.ledger);v['sentences'].append(dict(v['sentences'][0],id='orphan'));self.assertTrue(self.check(ledger=v))
    def test_duplicate_row(self):
        v=copy.deepcopy(self.ledger);v['sentences'].append(v['sentences'][0]);self.assertTrue(self.check(ledger=v))
    def test_duplicate_source(self):
        v=copy.deepcopy(self.ledger);v['sources'].append(v['sources'][0]);self.assertTrue(self.check(ledger=v))
    def test_bad_source_hash(self):
        v=copy.deepcopy(self.ledger);v['sources'][0]['sha256']='0'*64;self.assertTrue(self.check(ledger=v))
    def test_bad_span_hash(self):
        v=copy.deepcopy(self.ledger);v['sources'][0]['excerpt_sha256']='0'*64;self.assertTrue(self.check(ledger=v))
    def test_bad_range(self):
        for a,b in [(0,1),(2,1),(1,10**9)]:
            with self.subTest(a=a,b=b):
                v=copy.deepcopy(self.ledger);v['sources'][0].update(start_line=a,end_line=b);self.assertTrue(self.check(ledger=v))
    def test_missing_source(self):
        v=copy.deepcopy(self.ledger);v['sources'][0]['path']='docs/no-such-source';self.assertTrue(self.check(ledger=v))
    def test_unsafe_source(self):
        for path in ['../secret','/etc/passwd','docs/../README.md']:
            with self.subTest(path=path):
                v=copy.deepcopy(self.ledger);v['sources'][0]['path']=path;self.assertTrue(self.check(ledger=v))
    def test_symlink_source(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d);(p/'a').write_text('test');(p/'b').symlink_to(p/'a')
            with self.assertRaises(ValueError):evidence.safe_source(p,'b')
    def test_missing_binding(self):
        v=copy.deepcopy(self.ledger);v['sentences'][0]['evidence_refs']=['nonexistent'];self.assertTrue(self.check(ledger=v))
    def test_missing_warrant(self):
        v=copy.deepcopy(self.ledger);v['sentences'][0]['warrant']=' ';self.assertTrue(self.check(ledger=v))
    def test_unknown_status(self):
        v=copy.deepcopy(self.ledger);v['sentences'][0]['class']='verified-by-vibes';self.assertTrue(self.check(ledger=v))
    def test_proposal_cannot_be_relabelled_code(self):
        v=copy.deepcopy(self.ledger);r=v['sentences'][0]
        r['class']='proposed';r['evidence_refs']=['round10-contract']
        self.assertEqual(self.check(ledger=v),[])
        r['class']='implemented';self.assertTrue(self.check(ledger=v))
    def test_measurement_requires_receipt(self):
        v=copy.deepcopy(self.ledger);v['sentences'][0]['class']='measured';self.assertTrue(self.check(ledger=v))
    def test_unbound_prose_locations(self):
        for anchor in [evidence.AUDIT_BEGIN,evidence.AUDIT_END,r'\maketitle',r'\end{thebibliography}']:
            with self.subTest(anchor=anchor):self.assertTrue(self.check(self.text.replace(anchor,anchor+'\nAn unsupported claim.\n',1)))
    def test_unbound_include(self):
        self.assertTrue(self.check(self.text.replace(evidence.AUDIT_END,r'\input{hidden}'+ '\n'+evidence.AUDIT_END)))
    def test_boundary_mutations(self):
        end=re.search(r'% END SENTENCE (\S+)',self.text).group()
        for text in [self.text.replace(end,end+'-renamed',1),self.text.replace(evidence.AUDIT_END,''),self.text.replace(evidence.AUDIT_BEGIN,evidence.AUDIT_BEGIN+'\n'+evidence.AUDIT_BEGIN),self.text.replace(r'\end{document}',r'\end{document}\end{document}')]:
            with self.subTest(text=text[:20]):self.assertTrue(self.check(text))
    def test_duplicate_markers(self):
        m=evidence.SENTENCE.search(self.text);self.assertTrue(self.check(self.text.replace(m.group(),m.group()+'\n'+m.group(),1)))
    def test_invalid_ledger(self):
        self.assertTrue(self.check(ledger=[]));self.assertTrue(self.check(ledger={'schema':'bad'}))
    def test_duplicate_json_keys(self):
        with tempfile.TemporaryDirectory() as d:
            p=Path(d)/'a.json';p.write_text('{"schema":1,"schema":2}')
            with self.assertRaises(ValueError):evidence.read_json(p)
    def test_native_release_dispatch(self):
        self.assertEqual(evidence.validate_systems_paper_evidence(),[])
        self.assertEqual(evidence.mutation_fixture_failures(),[])
    def test_architecture_guards(self):
        import check_architecture_guide as architecture
        architecture.validate_systems_paper(self.text)
        for bad in [self.text.replace(r"\label{sec:short}",r"\label{missing}"),
                    self.text.replace("https://github.com/wcook04/plectis-erdos","https://invalid.example/old"),
                    self.text+"x"*110000]:
            with self.subTest(sample=bad[-20:]):
                with self.assertRaises(AssertionError):architecture.validate_systems_paper(bad)
    def test_checker_does_not_call_commands(self):
        # No subprocess import/invocation is permitted on this native evidence path.
        with patch('subprocess.run',side_effect=AssertionError('execution forbidden')):
            self.assertEqual(self.check(),[])
    def test_authored_warrants_are_not_entailment_proofs(self):
        # A coordinated, newly approved false prose+ledger edit is NOT detected.
        # Preserve this passing limitation test rather than claiming semantic verification.
        v=copy.deepcopy(self.ledger);row=v['sentences'][0];old=row['text'];new='Plectis has proven every mathematical proposition.'
        row['text']=new;row['statement_sha256']=evidence.sha256(new.encode())
        self.assertEqual(self.check(self.text.replace(old,new,1),v),[])

class CountTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.text=PAPER.read_text();cls.values=counts.pipeline_values(ROOT)
    def test_real_inventory(self):self.assertEqual(counts.pipeline_errors(self.text,ROOT),[])
    def test_counts_are_snapshot_owned(self):
        snap=counts.pipeline_snapshot(ROOT);self.assertEqual(snap['values'],self.values)
        self.assertTrue(snap['inputs']);self.assertTrue(snap['limits'])
    def test_mutated_counts(self):
        for key in ['LedgerRows','LeanModules','LedgerCompared','Rounds','HistoricalEdits']:
            if key not in self.values:continue
            rendered=counts.pipeline_render({key:self.values[key]}).splitlines()[1]
            self.assertIn(rendered,self.text)
            with self.subTest(key=key):self.assertTrue(counts.pipeline_errors(self.text.replace(rendered,rendered.replace('}{','}{999',1),1),ROOT))
    def test_missing_count(self):
        line=counts.pipeline_render({'LedgerRows':self.values['LedgerRows']}).splitlines()[1]
        self.assertTrue(counts.pipeline_errors(self.text.replace(line,''),ROOT))
    def test_extra_count(self):
        self.assertTrue(counts.pipeline_errors(self.text.replace(counts.PIPELINE_END,r'\newcommand{\Invented}{999}'+'\n'+counts.PIPELINE_END),ROOT))
    def test_duplicate_count(self):
        line=counts.pipeline_render({'LedgerRows':self.values['LedgerRows']}).splitlines()[1]
        self.assertTrue(counts.pipeline_errors(self.text.replace(line,line+'\n'+line,1),ROOT))
    def test_no_stale_legacy_cache(self):
        # Same root and journal head, changed source calculation: must change output.
        with patch.object(counts,'expected_values',side_effect=[{'A':1},{'A':2}]):
            first=counts._expected_region(str(ROOT),'head');second=counts._expected_region(str(ROOT),'head')
        self.assertNotEqual(first,second)
    def test_bad_partition(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);(root/'docs').mkdir();ledger=json.loads((ROOT/'docs/paper_lean_coverage.json').read_text())
            ledger['summary']['comparator']['pending']+=1
            (root/'docs/paper_lean_coverage.json').write_text(json.dumps(ledger))
            with self.assertRaises(counts.CountError):counts.ledger_values(root)

def run_suite(suite):
    result=unittest.TextTestRunner(verbosity=2).run(suite)
    return 0 if result.wasSuccessful() else 1

def run_counts():return run_suite(unittest.defaultTestLoader.loadTestsFromTestCase(CountTests))
def run_all():
    suite=unittest.TestSuite([unittest.defaultTestLoader.loadTestsFromTestCase(c) for c in [EvidenceTests,CountTests]])
    return run_suite(suite)
if __name__=='__main__':raise SystemExit(run_all())
