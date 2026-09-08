#!/usr/bin/env python3
import unittest
from build_problem_index import claim_registration


class RegistryJoinTest(unittest.TestCase):
    row = {"directory": "ErdosProblems/Erdos1041", "principal_module": "ErdosProblems.Erdos1041.Basic", "companion_modules": ["Shared.Bridge"]}

    def test_absent_is_not_unknown(self):
        self.assertEqual(claim_registration(self.row, None)["status"], "unknown_registry_unavailable")
        self.assertEqual(claim_registration(self.row, {"claims": []})["status"], "no_registered_declaration_bindings")

    def test_exact_directory_and_explicit_module_only(self):
        declarations = [{"module": "ErdosProblems/Erdos1041/New.lean", "name": "new_result"},
                        {"module": "Shared.Bridge", "name": "shared"},
                        {"module": "ErdosProblems/Erdos10410/Wrong.lean", "name": "wrong"}]
        result = claim_registration(self.row, {"claims": [{"id": "selected", "declarations": declarations}]})
        self.assertEqual(result["status"], "partially_registered")
        self.assertEqual(result["claim_ids"], ["selected"])
        self.assertEqual({r["name"] for r in result["declarations"]}, {"new_result", "shared"})
        self.assertNotIn("verified", result)

    def test_open_claim_without_declarations_does_not_register_modules(self):
        result = claim_registration(self.row, {"claims": [{"id": "erdos_1041", "status": "open", "declarations": []}]})
        self.assertEqual(result["status"], "no_registered_declaration_bindings")


if __name__ == "__main__":
    unittest.main()
