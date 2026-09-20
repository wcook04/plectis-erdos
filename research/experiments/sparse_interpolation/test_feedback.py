#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Behavioural checks against independent bounded specifications."""
import itertools
import unittest
from fractions import Fraction as Q

from feedback import (Step, check_trace, demo_request, explore, lean_certificate,
                      merge_residues, read_request, shrink_trace)


class FeedbackTests(unittest.TestCase):
    def test_compiled_support_equals_direct_predicate(self):
        # Exhaustively exercise endpoints, empty intervals, residues and CRT;
        # the oracle tests the original inequalities, not the bound formula.
        cases = 0
        for a, m, c, numerator, denominator in itertools.product(
                range(5), range(1, 5), range(4), range(9), (1, 2, 3)):
            r = Q(numerator, denominator)
            for extra in ((), ((1, 2),), ((0, 2), (1, 4))):
                step = Step(a, m, Q(2, 3), Q(1, 3), Q(5, 3), extra)
                expected = [d for d in range(a + 1) if step.check(c, r, d)]
                self.assertEqual(list(step.choices(c, r)), expected)
                cases += 1
        self.assertEqual(cases, 6480)

    def test_crt_non_coprime_and_empty(self):
        self.assertEqual(merge_residues(2, 4, 4, 6), (10, 12))
        self.assertIsNone(merge_residues(0, 4, 1, 2))

    def test_exact_inputs_only(self):
        request = demo_request(1)
        request['steps'][0]['weight'] = 0.5
        with self.assertRaises(ValueError):
            read_request(request)
        request = demo_request(1)
        request['steps'][0]['modulus'] = 0
        with self.assertRaises(ValueError):
            read_request(request)

    def test_freedom_and_baseline_same_optimum(self):
        request = demo_request(5)
        direct = explore(request, budget=100000)
        baseline = explore(request, budget=100000, backend='filter')
        self.assertEqual(direct['status'], 'finite_optimum')
        self.assertEqual(direct['best'], baseline['best'])
        self.assertEqual(direct['distinct_complete_traces'], baseline['distinct_complete_traces'])
        self.assertEqual(direct['complete_trace_set_sha256'], baseline['complete_trace_set_sha256'])
        self.assertGreater(direct['distinct_complete_traces'], 1)
        self.assertLess(direct['proposals'], baseline['proposals'])

    def test_budget_is_not_impossibility_or_optimality(self):
        result = explore(demo_request(5), budget=1)
        self.assertEqual(result['status'], 'budget_exhausted')
        self.assertFalse(result['exhausted'])

    def test_actual_boolean_support_witness(self):
        request = demo_request(8, 'divisor-count')
        result = explore(request, budget=100000)
        self.assertIsNotNone(result['best'])
        digits = result['best']['digits']
        bits = result['best']['check']['support_bits']
        self.assertTrue(all(b in (0, 1) for b in bits))
        for n, d in enumerate(digits, 1):
            self.assertEqual(d, sum(bits[k-1] for k in range(1, n+1) if n % k == 0))

    def test_separately_satisfiable_constraints_can_conflict(self):
        # Feedback permits precisely digit 2; a Boolean support at index one
        # permits 0 or 1. Their conjunction has no witness.
        request = {'target': '2', 'steps': [{'allowance': 2, 'modulus': 2,
                   'weight': '1', 'lower': '0', 'upper': '0'}]}
        self.assertEqual(explore(request)['best']['digits'], [2])
        request['support'] = 'divisor-count'
        self.assertEqual(explore(request)['status'], 'finite_incompatible')
        self.assertFalse(check_trace(request, [2])['valid'])

    def test_valid_prefix_can_have_no_extension(self):
        request = {'target': '2', 'steps': [
            {'allowance': 2, 'modulus': 1, 'weight': '1', 'lower': '0', 'upper': '2'},
            {'allowance': 0, 'modulus': 1, 'weight': '1', 'lower': '1', 'upper': '1'}]}
        self.assertTrue(check_trace(request, [2])['valid'])
        self.assertFalse(check_trace(request, [2, 0])['valid'])
        self.assertEqual(explore(request)['best']['digits'], [1, 0])

    def test_runners_reproducible_and_shrink_preserves_both(self):
        request = demo_request(5)
        for runner in ('random', 'targeted'):
            result = explore(request, runner=runner, budget=100, seed=19)
            self.assertEqual(result, explore(request, runner=runner, budget=100, seed=19))
            self.assertTrue(result['best']['check']['complete'])
            self.assertFalse(result['exhausted'])
        digits = explore(request)['best']['digits']
        predicate = lambda ds: sum(d*d for d in ds) >= 60
        shrunk = shrink_trace(request, digits, predicate)
        self.assertTrue(shrunk['check']['complete'])
        self.assertTrue(predicate(shrunk['digits']))
        self.assertLessEqual(sum(shrunk['digits']), sum(digits))

    def test_trace_rejection_and_finite_lean_obligations(self):
        request = demo_request(3)
        digits = explore(request)['best']['digits']
        self.assertFalse(check_trace(request, [-1] + digits[1:])['valid'])
        self.assertFalse(check_trace(request, ['2'] + digits[1:])['valid'])
        self.assertFalse(check_trace(request, digits + [0])['valid'])
        source = lean_certificate(request, digits)
        self.assertIn('theorem step_2 : Admissible', source)
        self.assertNotIn('HasSum', source)
        self.assertNotIn('sorry', source)

    def test_evolved_programme_replays_on_another_request(self):
        training = demo_request(5)
        learned = explore(training, runner='evolve', budget=120, seed=5)
        self.assertLessEqual(learned['proposals'], 120)
        self.assertGreater(learned['evaluated_programmes'], 1)
        self.assertEqual(learned, explore(training, runner='evolve', budget=120, seed=5))
        replay = explore(training, runner='policy', policy=learned['policy'])
        self.assertEqual(replay['best'], learned['best'])
        transfer = demo_request(7)
        transfer['target'] = '7/2'
        reused = explore(transfer, runner='policy', policy=learned['policy'])
        self.assertTrue(reused['best']['check']['complete'])
        self.assertFalse(reused['exhausted'])
        with self.assertRaises(ValueError):
            explore(transfer, runner='policy', policy=['execute arbitrary Python'])

    def test_all_runners_terminate_on_empty_root(self):
        request = demo_request(1)
        request['target'] = '0'
        for runner in ('enumerate', 'random', 'targeted', 'evolve'):
            self.assertIsNone(explore(request, runner=runner, budget=10)['best'])


if __name__ == '__main__':
    unittest.main()
