#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
"""Offline mutation tests for the native editorial exchange."""

import _test_bootstrap  # noqa: F401
import json
from pathlib import Path
import tempfile
import unittest
import zipfile

import paper_refinement as r
import build_short_paper_demo as demo
import short_paper_writer as writer

class RefinementTests(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup)
        self.root=Path(self.temp.name)/'root';self.root.mkdir()
        pairs,issues=writer.source_tree(demo.FIXTURE_ROOT,demo.PAPER)
        self.assertFalse(issues)
        for name,text in pairs:
            p=self.root/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(text)
        p=self.root/'docs/paper_lean_coverage.json';p.parent.mkdir(exist_ok=True)
        p.write_bytes((demo.FIXTURE_ROOT/'docs/paper_lean_coverage.json').read_bytes())
        self.packet=Path(self.temp.name)/'packet.zip'
        r.freeze(self.root,'fixture',[demo.PAPER],self.packet)
        self.original=r.read_archive(self.packet)
        self.contract=json.loads(self.original['RETURN.template.json'])
        self.files={'RETURN.json':json.dumps(self.contract).encode(),demo.PAPER:self.original[demo.PAPER]}
    def check(self):
        path=Path(self.temp.name)/'return.zip'
        self.files['RETURN.json']=json.dumps(self.contract).encode()
        with zipfile.ZipFile(path,'w') as z:
            for name,data in self.files.items():z.writestr(name,data)
        return r.check_return(self.packet,path)
    def test_round_trip_and_checkout_unchanged(self):
        before=(self.root/demo.PAPER).read_bytes()
        self.assertEqual(self.check()['status'],'transport_and_static_audit_pass')
        self.assertEqual((self.root/demo.PAPER).read_bytes(),before)
    def test_stale_identity(self):
        self.contract['input_manifest_sha256']='0'*64
        with self.assertRaisesRegex(ValueError,'identity'):self.check()
    def test_stale_edit(self):
        self.contract['edited_files'][0]['original_sha256']='0'*64
        with self.assertRaisesRegex(ValueError,'Stale'):self.check()
    def test_unscoped_edit(self):
        self.contract['edited_files'][0]['path']='docs/claims.json'
        self.files['docs/claims.json']=b'{}'
        with self.assertRaisesRegex(ValueError,'Unscoped'):self.check()
    def test_audit_program_is_inert(self):
        self.files['validation/check.py']=b'raise RuntimeError("never execute me")'
        self.check()
    def test_lost_label(self):
        self.files[demo.PAPER]=self.files[demo.PAPER].replace(b'\\label{res:distinct-height-all}',b'')
        with self.assertRaisesRegex(ValueError,'Undeclared statement|lost labels'):self.check()
    def test_statement_change_requires_review(self):
        self.files[demo.PAPER]=self.files[demo.PAPER].replace(b'\\label{res:distinct-height-all}',b'\\label{res:distinct-height-all} False claim.')
        self.contract['statement_changes']=[{'path':demo.PAPER,'label':'res:distinct-height-all','relation':'changed','reason':'Requires mathematical review'}]
        self.assertEqual(self.check()['status'],'native_review_required')
    def test_undeclared_statement_change_refused(self):
        self.files[demo.PAPER]=self.files[demo.PAPER].replace(b'\\label{res:distinct-height-all}',b'\\label{res:distinct-height-all} False claim.')
        with self.assertRaisesRegex(ValueError,'Undeclared statement'):self.check()
    def test_return_program_cannot_be_applied(self):
        self.files['scripts/check_release.py']=b'print("pass")'
        with self.assertRaisesRegex(ValueError,'Unexpected'):self.check()
    def test_traversal(self):
        self.files['validation/../../escape.json']=b'{}'
        with self.assertRaisesRegex(ValueError,'Unsafe'):self.check()
    def test_duplicate_zip_member(self):
        path=Path(self.temp.name)/'duplicate.zip'
        with zipfile.ZipFile(path,'w') as z:
            z.writestr('same',b'a');z.writestr('same',b'b')
        with self.assertRaisesRegex(ValueError,'Duplicate'):r.read_archive(path)
    def test_frozen_packet_not_overwritten(self):
        with self.assertRaisesRegex(ValueError,'overwrite'):r.freeze(self.root,'fixture',[demo.PAPER],self.packet)

if __name__=='__main__':unittest.main()
