import importlib.util
import json
import os
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
HERE=Path(__file__).resolve().parent
PUBLIC=Path(os.environ.get('SEMANTIC_CORPUS_TEST_ROOT', str(HERE.parent)))
sys.path[:0]=[str(HERE),str(PUBLIC/'scripts')]
import query_corpus as q
import query_semantic as query
import check_semantic_corpus as checker
import check_theory_lab as theory
import build_semantic_corpus as builder

class Transport(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.text=q.read_json_transport(PUBLIC/'docs/semantic_corpus.json')
        cls.obj=json.loads(cls.text)
        cls.encoded=q.encode_json_transport(cls.text)
    def test_full_roundtrip_and_determinism(self):
        self.assertEqual(q.decode_json_transport(self.encoded),self.text)
        self.assertEqual(self.encoded,q.encode_json_transport(self.text))
        self.assertEqual(json.loads(q.decode_json_transport(self.encoded)),self.obj)
        print('compressed bytes:',len(self.encoded))
    def test_query_and_release_safe_loaders(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);(root/'docs').mkdir();p=root/'docs/semantic_corpus.json.gz';p.write_bytes(self.encoded)
            with patch.object(q,'ROOT',root):
                q.load.cache_clear();self.assertEqual(q.load('docs/semantic_corpus.json'),self.obj)
            with patch.object(query,'CORPUS',p),patch.object(query,'semantic_input_fingerprint',return_value=self.obj['semantic_input_fingerprint']):
                query.load.cache_clear();self.assertEqual(query.load(),self.obj)
            for module in [checker,theory,builder]:
                with patch.object(module,'ROOT',root):
                    self.assertEqual(json.loads(module.safe_read_text(root/'docs/semantic_corpus.json')),self.obj)
            p.unlink();plain=root/'docs/semantic_corpus.json';plain.write_text(self.text)
            self.assertEqual(q.read_json_transport(p),self.text)
    def test_receipt_distinguishes_logical_and_transport_hash(self):
        import hashlib
        receipt=builder.check_receipt(self.obj,self.text,{})
        self.assertEqual(receipt['output_digest'],'sha256:'+hashlib.sha256(self.text.encode()).hexdigest())
        self.assertEqual(receipt['output_transport_digest'],'sha256:'+hashlib.sha256(self.encoded).hexdigest())
        self.assertNotEqual(receipt['output_digest'],receipt['output_transport_digest'])
    def test_safe_loader_rejects_compressed_symlink(self):
        with tempfile.TemporaryDirectory() as d:
            root=Path(d);(root/'docs').mkdir();outside=root/'payload';outside.write_bytes(self.encoded)
            (root/'docs/semantic_corpus.json.gz').symlink_to(outside)
            with patch.object(checker,'ROOT',root):
                with self.assertRaises(checker.UnsafeSemanticCorpusInput):
                    checker.safe_read_text(root/'docs/semantic_corpus.json')
    def test_corruption_and_missing_rejected(self):
        with self.assertRaises(Exception):q.decode_json_transport(self.encoded[:30])
        with tempfile.TemporaryDirectory() as d:
            with self.assertRaises(FileNotFoundError):q.read_json_transport(Path(d)/'semantic_corpus.json.gz')

if __name__=='__main__':unittest.main()
