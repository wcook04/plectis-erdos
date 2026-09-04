#!/usr/bin/env python3
"""Regression tests for web-only discovery and stale proof custody."""
import hashlib
import json
import tempfile
import unittest
from pathlib import Path

import build_semantic_corpus as builder
import check_research_browser as browser

class BrowserTests(unittest.TestCase):
    def test_structural_modules_are_named_in_menu_and_heading(self):
        node = {"id": "structural::opaque", "zone": "structural", "problem": "1041",
                "source_module": "ErdosProblems/Erdos1041/CriticalTwoRootProximity.lean",
                "canonical_statement": "Exact proposition", "evidence": []}
        surfaces = builder.browser_surfaces({"statement_nodes": [node], "relations": [], "zones": []})
        self.assertIn("CriticalTwoRootProximity", surfaces[builder.SEMANTIC_DIR / "BROWSER.md"])
        self.assertIn("## CriticalTwoRootProximity", surfaces[builder.SEMANTIC_DIR / "BROWSER_structural_1.md"])

    def test_bounded_machine_route_preserves_every_field(self):
        import query_corpus
        packet = {f"result_{i}": {"statement": "x" * 80, "hypotheses": ["a", "b"]}
                  for i in range(550)}
        pretty = json.dumps(packet, ensure_ascii=False, indent=2)
        self.assertGreater(len(pretty.encode()), query_corpus.OUTPUT_BUDGET_BYTES)
        encoded = query_corpus.encode_packet(packet)
        self.assertLessEqual(len(encoded.encode()), query_corpus.OUTPUT_BUDGET_BYTES)
        self.assertEqual(json.loads(encoded), packet)

    def test_complete_graph_is_chunked_without_truncating_late_nodes(self):
        statement = 'All quantifiers and hypotheses survive. ' * 100
        nodes = [{'id': f'Z01::r{i}', 'local_id': f'r{i}', 'zone': 'Z01',
                  'problem': '249', 'canonical_statement': statement,
                  'interpretation_tier': 'authored_statement', 'evidence': []} for i in range(70)]
        surfaces = builder.browser_surfaces({'statement_nodes': nodes,
             'relations': [{'from':'Z01::r0','to':'Z01::r69','relation':'implies','basis':'Exact stated implication.'}],
             'zones':[{'zone_id':'Z01','title':'Test'}]})
        text = '\n'.join(surfaces.values())
        self.assertEqual(text.count(statement),70)
        self.assertIn('## r69', text)
        self.assertIn('BROWSER_Z01_3.md#node-', text)
        self.assertIn('Exact stated implication.',text)

    def test_mutated_source_and_omitted_late_statement_are_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root=Path(tmp);base=root/'research_corpus'/'Erdos249';base.mkdir(parents=True)
            packet=base/'research_packet.json';packet.write_text(json.dumps({'exact_results':[{'statement':'late theorem'}]}))
            front=base/'FRONTIER.md';front.write_text('late theorem')
            sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
            manifest={'files':[{'public_path':str(packet.relative_to(root)),'published_sha256':sha(packet)}],
                      'browser_frontier':{'path':str(front.relative_to(root)),'sha256':sha(front)}}
            mp=base/'CORPUS_MANIFEST.json';mp.write_text(json.dumps(manifest))
            self.assertEqual(browser.check(root),[])
            front.write_text('short incomplete summary');manifest['browser_frontier']['sha256']=sha(front);mp.write_text(json.dumps(manifest))
            self.assertTrue(any('statement absent' in e for e in browser.check(root)))
            packet.write_text('{}')
            self.assertTrue(any('changed exported source' in e for e in browser.check(root)))

if __name__ == '__main__':
    unittest.main()
