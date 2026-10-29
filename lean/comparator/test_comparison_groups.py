#!/usr/bin/env python3
"""Rejection controls for complete, disjoint Comparator target coverage."""
from copy import deepcopy
from pathlib import Path
import json
import unittest
from comparison_groups import GROUPS, split_config


class ComparisonGroupsTest(unittest.TestCase):
    def setUp(self):
        self.config = json.loads((Path(__file__).resolve().parents[1] / 'comparator.json').read_text())

    def test_exact_coverage_and_unchanged_settings(self):
        original = deepcopy(self.config)
        groups = split_config(self.config)
        self.assertEqual([n for g in GROUPS for n in groups[g]['theorem_names']], self.config['theorem_names'])
        self.assertEqual(self.config, original)
        for cfg in groups.values():
            self.assertEqual({k: v for k, v in cfg.items() if k != 'theorem_names'},
                             {k: v for k, v in original.items() if k != 'theorem_names'})

    def test_missing_target_rejected(self):
        self.config['theorem_names'].pop()
        with self.assertRaises(ValueError):
            split_config(self.config)

    def test_duplicate_target_rejected(self):
        self.config['theorem_names'][-1] = self.config['theorem_names'][0]
        with self.assertRaises(ValueError):
            split_config(self.config)

    def test_unassigned_target_rejected(self):
        self.config['theorem_names'][-1] = 'E8LeechFC.unassigned'
        with self.assertRaises(ValueError):
            split_config(self.config)

    def test_wrong_group_sizes_rejected(self):
        self.config['theorem_names'][5] = 'E8LeechFC.leech_unexpected'
        with self.assertRaises(ValueError):
            split_config(self.config)

    def test_extra_axiom_rejected(self):
        self.config['permitted_axioms'].append('sorryAx')
        with self.assertRaises(ValueError):
            split_config(self.config)

    def test_definition_hole_rejected(self):
        self.config['definition_names'] = ['E8Leech.e8Set']
        with self.assertRaises(ValueError):
            split_config(self.config)


if __name__ == '__main__':
    unittest.main()
