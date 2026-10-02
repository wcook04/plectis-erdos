#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Real consumer regressions for the native-proof and transitive-axiom gates."""
from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

import check_axiom_audit as audit
import check_release


class AxiomAuditTests(unittest.TestCase):
    def run_cli(self, text: str, *, config: object | None = None,
                source: str | None = None) -> subprocess.CompletedProcess:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            (root / "audit.log").write_text(text, encoding="utf-8")
            (root / "config.json").write_text(json.dumps(
                config if config is not None else {"permitted_axioms": sorted(audit.ALLOWED_AXIOMS)}
            ), encoding="utf-8")
            source_args = []
            if source is not None:
                (root / "Audit.lean").write_text(source, encoding="utf-8")
                source_args = ["--audit-source", str(root / "Audit.lean")]
            return subprocess.run(
                [sys.executable, *(["-O"] if not __debug__ else []),
                 str(Path(audit.__file__)), str(root / "audit.log"),
                 "--config", str(root / "config.json"), *source_args],
                env={**os.environ, "PYTHONDONTWRITEBYTECODE": "1"},
                capture_output=True, text=True, timeout=10,
            )

    def test_actual_cli_accepts_standard_and_axiom_free_reports(self):
        result = self.run_cli(
            "=== first audit ===\n'Theorem.one' depends on axioms: "
            "[propext, Classical.choice, Quot.sound]\n"
            "'Theorem.two' does not depend on any axioms\n"
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("PASS 2 declaration reports", result.stdout)

    def test_wrapped_and_located_lean_output(self):
        result = self.run_cli("Audit.lean:3:0: info: 'Theorem.one' depends on axioms: "
                              "[propext,\n Classical.choice, Quot.sound]\n")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_prime_and_unicode_declaration_names(self):
        result = self.run_cli("'Theorem.lemma'' depends on axioms: [propext]\n"
                              "'Theorem.«α β»' does not depend on any axioms\n")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("PASS 2 declaration reports", result.stdout)

    def test_every_report_is_checked_after_a_valid_report(self):
        for name in ("sorryAx", "Lean.ofReduceBool", "Lean.trustCompiler",
                     "Theorem._native.native_decide.ax_1",
                     "Theorem._native.bv_decide.ax_1", "Custom.assumption"):
            with self.subTest(name=name):
                result = self.run_cli("'Valid' depends on axioms: [propext]\n"
                                      f"'Bad' depends on axioms: [Classical.choice, {name}]\n")
                self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
                self.assertIn("Bad: forbidden axiom " + name, result.stdout)

    def test_missing_empty_or_malformed_reports_are_refused(self):
        for text in ("", "=== audit ===\n", "'Bad' depends on axioms: []\n",
                     "'Bad' depends on axioms: [propext,]\n",
                     "'Bad' depends on axioms: [propext\n",
                     "'Bad' depends on axioms: [propext] extra\n",
                     "'Valid' depends on axioms: [propext]\n"
                     "'Bad' depends on axioms: not-a-list\n"):
            with self.subTest(text=text):
                result = self.run_cli(text)
                self.assertEqual(result.returncode, 1, result.stdout + result.stderr)

    def test_budget_cannot_be_widened_or_malformed(self):
        names = sorted(audit.ALLOWED_AXIOMS)
        for config in ({}, [], {"permitted_axioms": names + ["Custom.assumption"]},
                       {"permitted_axioms": names + [names[0]]},
                       {"permitted_axioms": names[:-1]},
                       {"permitted_axioms": [1, 2, 3]}):
            with self.subTest(config=config):
                result = self.run_cli("'Valid' depends on axioms: [propext]\n", config=config)
                self.assertEqual(result.returncode, 1, result.stdout + result.stderr)

    def test_unknown_axiom_rejected_even_if_its_spelling_resembles_allowed_name(self):
        for name in ("propextExtra", "Lean.Classical.choice", "Quot.sound.extra"):
            with self.subTest(name=name):
                result = self.run_cli(f"'Bad' depends on axioms: [{name}]\n")
                self.assertEqual(result.returncode, 1)

    def test_source_bound_roster_and_missing_extra_duplicate_reports(self):
        source = "namespace Example\nsection\n#print axioms first\nend\n" \
                 "#print axioms second\nend Example\n"
        valid = "'Example.first' depends on axioms: [propext]\n" \
                "'Example.second' does not depend on any axioms\n"
        self.assertEqual(self.run_cli(valid, source=source).returncode, 0)
        for text in (valid.splitlines()[0] + "\n",
                     valid + "'Other' does not depend on any axioms\n",
                     valid + valid.splitlines()[0] + "\n",
                     valid.replace("Example.second", "Foreign.second")):
            with self.subTest(text=text):
                self.assertEqual(self.run_cli(text, source=source).returncode, 1)

    def test_audit_owner_commands_ignore_comments_and_strings_fail_unsupported(self):
        with tempfile.TemporaryDirectory() as raw:
            p = Path(raw) / "Audit.lean"
            p.write_text('/- #print axioms falseOwner -/\n'
                         'def hint := "#print axioms falseOwner"\n'
                         'namespace Real\n#print axioms owner\nend Real\n')
            self.assertEqual(audit.expected_declarations([p]), {"Real.owner"})
            for text in ("-- #print axioms fake\n", "#print axioms\n",
                         "#print axioms real\n#print axioms real\n"):
                p.write_text(text)
                with self.assertRaises(ValueError):
                    audit.expected_declarations([p])

    def test_wrapped_literal_source_roster_preserves_scopes_and_comments(self):
        source = ('namespace Outer\nsection\n'
                  '/- #print axioms hidden -/\n'
                  'def hint := "#print axioms fake"\n'
                  '#print axioms -- explanatory comment\n'
                  '  wrapped -- name comment\nend\n'
                  '#print axioms\nsecond\nend Outer\n')
        valid = "'Outer.wrapped' depends on axioms: [propext]\n" \
                "'Outer.second' does not depend on any axioms\n"
        self.assertEqual(self.run_cli(valid, source=source).returncode, 0)
        for text in (valid.splitlines()[0] + "\n",
                     valid + "'Foreign' does not depend on any axioms\n",
                     valid + valid.splitlines()[0] + "\n"):
            with self.subTest(text=text):
                self.assertEqual(self.run_cli(text, source=source).returncode, 1)

    def test_wrapped_source_refuses_truncation_scope_and_nonliteral_continuations(self):
        for source in ('#print axioms\n', '#print axioms\n\nowner\n',
                       'namespace Outer\n#print axioms\nend Outer\n',
                       'namespace Outer\n#print axioms\n  end\n',
                       '#print axioms\nnamespace Foreign\n',
                       '#print axioms\n  "fake"\n',
                       '#print axioms\n  owner extra\n',
                       '#print axioms\n#print axioms other\n',
                       '#print axioms\nowner\n#print axioms owner\n'):
            with self.subTest(source=source):
                self.assertEqual(self.run_cli("'owner' does not depend on any axioms\n", source=source).returncode, 1)

        # A valid wrapped root-qualified prime name is the positive control:
        # blanket refusal must not make the adversarial checks pass.
        self.assertEqual(self.run_cli(
            "'Elsewhere.owner'' does not depend on any axioms\n",
            source="namespace Outer\n#print axioms\n  _root_.Elsewhere.owner'\nend Outer\n",
        ).returncode, 0)

    def test_actual_three_workflow_audit_owners_resolve_complete_roster(self):
        paths = [audit.ROOT / "verification" / name / "AxiomAudit.lean" for name in
                 ("ExternalVerification", "ExternalVerification1049", "ExternalVerification1041SolvedFamilies")]
        names = audit.expected_declarations(paths)
        self.assertEqual(len(names), 23)
        self.assertIn("Erdos249257.ExternalVerification1049.comparator_sevenHalves_numericalHeight", names)
        self.assertIn("Erdos249257.ExternalVerification1041SolvedFamilies.cubic_safeRootSpoke", names)
        log = "".join(f"'{name}' depends on axioms: [propext]\n" for name in sorted(names))
        count, errors = audit.audit_errors(log, audit.ALLOWED_AXIOMS, names)
        self.assertEqual((count, errors), (23, []))
        self.assertTrue(audit.audit_errors(log.rsplit("\n", 2)[0] + "\n", audit.ALLOWED_AXIOMS, names)[1])

    def test_actual_source_scanner_rejects_native_bitvector_tactic(self):
        text = "theorem bad : (0 : BitVec 8) = 0 := by\n  bv_decide\n"
        self.assertTrue(check_release.proof_trust_candidate(text))
        self.assertTrue(check_release.proof_trust_candidate_bytes(text.encode()))
        self.assertEqual(check_release.proof_trust_violation(text), "bv_decide")
        self.assertEqual(check_release.proof_trust_violation_bytes(text.encode()), "bv_decide")

    def test_nested_comments_strings_and_neighbor_identifiers_remain_harmless(self):
        for text in ("/- outer /- bv_decide -/ native_decide -/\ntheorem ok : True := by trivial\n",
                     'def message := "bv_decide and native_decide"\n',
                     "def «bv_decide» : Nat := 0\n",
                     "def «native_decide» : Nat := 0\n",
                     "def «contains bv_decide token» : Nat := 0\n",
                     "def bv_decide_helper : Nat := 0\n",
                     "def native_decide_helper : Nat := 0\n"):
            with self.subTest(text=text):
                self.assertIsNone(check_release.proof_trust_violation(text))
                self.assertIsNone(check_release.proof_trust_violation_bytes(text.encode()))

    def test_quoted_identifier_cannot_hide_a_following_native_invocation(self):
        text = "def «bv_decide» : Nat := 0\ntheorem bad : True := by native_decide\n"
        self.assertEqual(check_release.proof_trust_violation(text), "native_decide")
        self.assertEqual(check_release.proof_trust_violation_bytes(text.encode()), "native_decide")

    def test_existing_native_decide_variants_stay_blocking(self):
        for text in ("theorem bad : True := by native_decide\n",
                     "theorem bad : True := by decide +native\n",
                     "theorem bad : True := by decide (native := true)\n"):
            with self.subTest(text=text):
                self.assertIsNotNone(check_release.proof_trust_violation(text))
                self.assertIsNotNone(check_release.proof_trust_violation_bytes(text.encode()))


if __name__ == "__main__":
    unittest.main()
