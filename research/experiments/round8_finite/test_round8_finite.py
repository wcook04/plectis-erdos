#!/usr/bin/env python3
"""Focused exact finite tests for four historical Round 8 return controls."""
from __future__ import annotations
from fractions import Fraction
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parents[3]
COMMIT = '0268dd8bfb2a556a0c93078337d42c6d07138fa2'
FILES = {
    'p1': 'research/experiments/chain_transcendence/round8_finite_cut.py',
    'p2': 'research/experiments/erdos269/round8_affine_collision.py',
    'p3': 'research/experiments/erdos1049/round8_calibrated_denominators.py',
    'p4': 'research/experiments/erdos249/round8_signed_pulse.py',
}


def load_case(name: str):
    path = ROOT / FILES[name]
    spec = importlib.util.spec_from_file_location(f'round8_{name}_finite', path)
    if spec is None or spec.loader is None:
        raise RuntimeError(f'cannot load {path}')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class FiniteReturnControls(unittest.TestCase):
    def test_each_direct_cli_is_exact_and_bounded(self):
        manifest = json.loads((ROOT / 'research/experiments/round8_finite/manifest.json').read_text())
        self.assertEqual(manifest['historical_source_commit'], COMMIT)
        for name, relative in FILES.items():
            with self.subTest(packet=name):
                argv = [sys.executable] + (['-O'] if sys.flags.optimize else []) + [
                    '-B', str(ROOT / relative)]
                proc = subprocess.run(argv,
                                      capture_output=True, text=True, timeout=10)
                self.assertEqual(proc.returncode, 0, proc.stderr)
                result = json.loads(proc.stdout)
                recorded = manifest['staged_programs'][relative]
                self.assertEqual(hashlib.sha256((ROOT / relative).read_bytes()).hexdigest(),
                                 recorded['sha256'])
                self.assertEqual(hashlib.sha256(proc.stdout.encode()).hexdigest(),
                                 recorded['direct_stdout_sha256'])
                self.assertEqual(result['source_commit'], COMMIT)
                self.assertTrue(result['evidence_class'].startswith('exact_finite'))
                self.assertEqual(result, load_case(name).report())

    def test_p1_separated_cut_and_lattice_loss(self):
        p1 = load_case('p1')
        result = p1.report()
        self.assertEqual(result['rational_displacement']['J'], '5/2')
        self.assertLess(Fraction(result['separated_cut']['remainder']),
                        Fraction(result['separated_cut']['upper_bound']))
        with self.assertRaises(ValueError):
            p1.displacement({1: 1}, 3, 2, 33)

    def test_p2_collision_does_not_imply_swap(self):
        p2 = load_case('p2')
        first = p2.word_map((5, 7, 3, 2))
        second = p2.word_map((7, 2, 3, 5))
        self.assertNotEqual((5, 7, 3, 2), (7, 2, 3, 5))
        self.assertEqual(first, second)
        self.assertEqual(p2.report()['contextual_swap_defect'], '1/420')
        with self.assertRaises(ValueError):
            p2.word_map((1, 3))

    def test_p3_denominator_trap_is_finite(self):
        p3 = load_case('p3')
        result = p3.report()
        self.assertEqual(len(result['finite_rows']), 5)
        self.assertEqual(result['rank_two_bad_clearer']['remaining_denominator'], 625)
        self.assertEqual(Fraction(result['rank_two_bad_clearer']['cleared_value']).denominator, 625)
        with self.assertRaises(ValueError):
            p3.moment(9)

    def test_p4_signed_packet_has_real_totient_room(self):
        p4 = load_case('p4')
        result = p4.report()
        self.assertEqual(result['low_progression_moment_checks'], 139)
        self.assertTrue(all(0 <= row['modified'] <= row['n']
                            for row in result['genuine_totient_rows']))
        self.assertEqual(p4.moment(p4.pulse(1000, 2), 2), 64)
        with self.assertRaises(ValueError):
            p4.pulse(1000, 20)


if __name__ == '__main__':
    unittest.main(verbosity=2)
