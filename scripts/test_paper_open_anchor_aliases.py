"""Integration regression: repeated paper objectives retain one registry identity."""
import unittest
import query_corpus as corpus


class OpenAnchorAliases(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.claims = corpus.load("docs/claims.json")
        cls.anchors = corpus.paper_anchor_inventory()

    def test_aliases_bind_the_existing_objective_in_both_papers(self):
        rows = self.claims["remaining_open_propositions"]
        self.assertEqual(len(rows), len({r["id"] for r in rows}))
        aliases = [r for r in rows if r.get("additional_paper_anchors")]
        self.assertTrue(aliases)
        for row in aliases:
            for anchor in [row["paper_anchor"], *row["additional_paper_anchors"]]:
                key = corpus.canonical_paper_anchor_key(anchor["source"], anchor["environment"], anchor["title"])
                observed = [a for a in self.anchors if corpus.canonical_paper_anchor_key(a["paper"]["source"], a["environment"], a["title"]) == key]
                self.assertEqual(len(observed), 1, key)
                self.assertEqual([r["id"] for r in observed[0]["attached_open_propositions"]], [row["id"]])

    def test_no_authored_problem_environment_is_untyped(self):
        problems = [a for a in self.anchors if a["environment"] == "problem"]
        self.assertTrue(problems)
        for anchor in problems:
            self.assertEqual(len(anchor["attached_open_propositions"]), 1, anchor["canonical_handle"])


if __name__ == "__main__":
    unittest.main()
