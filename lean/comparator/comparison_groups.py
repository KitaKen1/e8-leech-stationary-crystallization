#!/usr/bin/env python3
"""Partition the canonical targets without changing any verification settings."""
from copy import deepcopy
from pathlib import Path
import argparse
import hashlib
import json

GROUPS = ('e8', 'leech', 'lattice-law')
PERMITTED_AXIOMS = ['propext', 'Classical.choice', 'Quot.sound']


def split_config(config):
    if (config.get('challenge_module') != 'Challenge' or
            config.get('solution_module') != 'FCSolution' or
            config.get('permitted_axioms') != PERMITTED_AXIOMS or
            config.get('enable_nanoda') is not False or
            config.get('definition_names')):
        raise ValueError('Canonical comparison settings changed')
    targets = config['theorem_names']
    if len(targets) != 13 or len(set(targets)) != 13:
        raise ValueError('Expected 13 distinct canonical targets')
    selected = {
        'e8': [n for n in targets if n.startswith('E8LeechFC.e8_')],
        'leech': [n for n in targets if n.startswith('E8LeechFC.leech_')],
        'lattice-law': [n for n in targets if n == 'E8LeechFC.stationary_exact_lattice_law'],
    }
    if ([len(selected[g]) for g in GROUPS] != [6, 6, 1] or
            [n for g in GROUPS for n in selected[g]] != targets):
        raise ValueError('Comparison groups do not exactly partition the canonical targets')
    result = {}
    for group in GROUPS:
        result[group] = deepcopy(config)
        result[group]['theorem_names'] = selected[group]
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('group', choices=GROUPS)
    parser.add_argument('--receipt-dir', required=True, type=Path)
    args = parser.parse_args()
    source = Path(__file__).resolve().parents[1] / 'comparator.json'
    canonical = json.loads(source.read_text())
    groups = split_config(canonical)
    args.receipt_dir.mkdir(parents=True, exist_ok=True)
    output = args.receipt_dir / 'comparator.json'
    output.write_text(json.dumps(groups[args.group], indent=2) + '\n')
    receipt = dict(group=args.group, canonical_config_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
                   canonical_target_count=13, target_count=len(groups[args.group]['theorem_names']),
                   groups={g: groups[g]['theorem_names'] for g in GROUPS},
                   exact_partition=True, other_config_fields_unchanged=True,
                   builtin_kernel_replay_required=True)
    (args.receipt_dir / 'target-partition.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(output.resolve())


if __name__ == '__main__':
    main()
