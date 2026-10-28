"""Regression and rejection controls for the axiom audit's CI log parser."""
import unittest
from axiom_log import parse_axioms, check_axioms


class AxiomLogTests(unittest.TestCase):
    def test_apostrophes_and_multiline_axiom_list(self):
        text = ("info: Audit.lean:1:0: 'E8Leech.name'_suffix' depends on axioms: "
                "[propext,\n Classical.choice,\n Quot.sound]\n"
                "'E8Leech.other'' does not depend on any axioms\n")
        observed = parse_axioms(text)
        self.assertEqual(observed, {"E8Leech.name'_suffix":
            {'propext', 'Classical.choice', 'Quot.sound'}, "E8Leech.other'": set()})

    def test_missing_apostrophe_target_is_rejected(self):
        with self.assertRaisesRegex(ValueError, 'Missing axiom reports'):
            check_axioms(parse_axioms("'Other' depends on axioms: [propext]"),
                         {"Required'"}, {'propext'})

    def test_forbidden_axiom_on_apostrophe_target_is_rejected(self):
        with self.assertRaisesRegex(ValueError, 'Unexpected axioms'):
            check_axioms(parse_axioms("'Required'' depends on axioms: [sorryAx]"),
                         {"Required'"}, {'propext', 'Classical.choice', 'Quot.sound'})

    def test_conflicting_duplicate_is_rejected(self):
        with self.assertRaisesRegex(ValueError, 'Conflicting axiom reports'):
            parse_axioms("'T' depends on axioms: [propext]\n"
                         "'T' does not depend on any axioms\n")


if __name__ == '__main__':
    unittest.main()
