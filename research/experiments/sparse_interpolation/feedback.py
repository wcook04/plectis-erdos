#!/usr/bin/env python3
# SPDX-FileCopyrightText: 2026 Will Cook
# SPDX-License-Identifier: Apache-2.0
"""Exact finite checks of residue feedback, in scaled-tail coordinates.

These are checks of the selector and sharpness examples, not proofs of
infinite convergence, nullity, or the support classification.
"""
from fractions import Fraction
from math import factorial, gcd, isqrt
from dataclasses import dataclass
from pathlib import Path
import argparse
import hashlib
import json
import random


def exact(value):
    """Accept exact JSON integers/strings; never silently rationalise floats."""
    if type(value) not in (int, str, Fraction):
        raise ValueError('rational inputs must be integers or fraction strings')
    return Fraction(value)


def natural(value, label):
    if type(value) is not int or value < 0:
        raise ValueError(f'{label} must be a nonnegative integer')
    return value


@dataclass(frozen=True)
class Progression:
    """A finite arithmetic progression, including the empty progression."""
    first: int
    stride: int
    count: int

    def __bool__(self):
        return self.count > 0

    def __iter__(self):
        return iter(range(self.first, self.first + self.stride * self.count,
                          self.stride))

    def contains(self, d):
        return (self.count > 0 and self.first <= d < self.first + self.stride * self.count
                and (d - self.first) % self.stride == 0)

    def at(self, index):
        if not 0 <= index < self.count:
            raise IndexError(index)
        return self.first + index * self.stride


def merge_residues(a, m, b, n):
    """Generalised CRT; None means an exactly empty intersection."""
    if m <= 0 or n <= 0:
        raise ValueError('moduli must be positive')
    g = gcd(m, n)
    if (b - a) % g:
        return None
    q = n // g
    k = 0 if q == 1 else ((b - a) // g * pow(m // g, -1, q)) % q
    return ((a + m * k) % (m * q), m * q)


@dataclass(frozen=True)
class Step:
    allowance: int
    modulus: int
    weight: Fraction
    lower: Fraction
    upper: Fraction
    congruences: tuple = ()

    @classmethod
    def read(cls, row):
        allowed = {'allowance', 'modulus', 'weight', 'lower', 'upper', 'congruences'}
        if set(row) - allowed:
            raise ValueError('unsupported step fields: ' + str(sorted(set(row) - allowed)))
        a = natural(row['allowance'], 'allowance')
        m = natural(row['modulus'], 'modulus')
        w, lo, hi = (exact(row[k]) for k in ('weight', 'lower', 'upper'))
        cs = []
        for pair in row.get('congruences', []):
            if len(pair) != 2 or type(pair[0]) is not int:
                raise ValueError('congruence must be [integer residue, positive modulus]')
            n = natural(pair[1], 'congruence modulus')
            if n == 0:
                raise ValueError('congruence modulus must be positive')
            cs.append((pair[0] % n, n))
        if m == 0 or w <= 0 or lo < 0 or lo > hi:
            raise ValueError('need positive modulus/weight and 0 <= lower <= upper')
        return cls(a, m, w, lo, hi, tuple(cs))

    def check(self, cumulative, remainder, digit):
        """Independent direct predicate, also used to replay every output."""
        if type(digit) is not int:
            return False
        r = remainder - digit * self.weight
        return (0 <= digit <= self.allowance
                and (cumulative + digit) % self.modulus == 0
                and self.lower <= r <= self.upper
                and all((digit - a) % m == 0 for a, m in self.congruences))

    def digit_lattice(self, cumulative):
        """The contract's bounded digit set before imposing remainder bounds."""
        residue, modulus = -cumulative % self.modulus, self.modulus
        for a, m in self.congruences:
            merged = merge_residues(residue, modulus, a, m)
            if merged is None:
                return Progression(0, 1, 0)
            residue, modulus = merged
        return Progression(residue, modulus, max(0, (self.allowance - residue) // modulus + 1))

    def choices(self, cumulative, remainder):
        """Compile interval + congruences without generate-and-filter."""
        lowq = (remainder - self.upper) / self.weight
        highq = (remainder - self.lower) / self.weight
        low = max(0, -(-lowq.numerator // lowq.denominator))
        high = min(self.allowance, highq.numerator // highq.denominator)
        residue, modulus = -cumulative % self.modulus, self.modulus
        for a, m in self.congruences:
            merged = merge_residues(residue, modulus, a, m)
            if merged is None:
                return Progression(0, 1, 0)
            residue, modulus = merged
        first = low + (residue - low) % modulus
        return Progression(first, modulus, max(0, (high - first) // modulus + 1))


def remainder_cover(step, cumulative, *, bits=(), support='free'):
    """Exact union of translated continuation intervals, compressed as a lattice.

    When at least two digits survive, the hull is covered iff stride * weight
    <= upper - lower. No statement about a later stage is inferred.
    """
    digits = step.digit_lattice(cumulative)
    if support == 'divisor-count':
        if any(type(bit) is not int or bit not in (0, 1) for bit in bits):
            raise ValueError('support history must contain Boolean integers')
        if cumulative != sum(sum(bits[k-1] for k in range(1, n+1) if n % k == 0)
                             for n in range(1, len(bits)+1)):
            raise ValueError('cumulative state disagrees with the support history')
        base = divisor_base(bits)
        selected = [d for d in (base, base + 1) if digits.contains(d)]
        digits = Progression(selected[0], 1, len(selected)) if selected else Progression(0, 1, 0)
    elif support != 'free':
        raise ValueError('unsupported support relation')
    if not digits:
        return {'nonempty': False, 'count': 0, 'hull_covered': False,
                'evidence': 'exact_one_step_cover', 'infinite_continuation': 'not_checked'}
    gap = max(Fraction(0), digits.stride * step.weight - (step.upper - step.lower)) if digits.count > 1 else Fraction(0)
    return {'nonempty': True, 'first_digit': digits.first, 'stride': digits.stride,
            'count': digits.count,
            'first_interval': [str(digits.first * step.weight + step.lower),
                               str(digits.first * step.weight + step.upper)],
            'translation': str(digits.stride * step.weight),
            'hull': [str(digits.first * step.weight + step.lower),
                     str(digits.at(digits.count - 1) * step.weight + step.upper)],
            'hull_covered': gap == 0, 'gap_width': str(gap),
            'uncovered_length': str((digits.count - 1) * gap),
            'evidence': 'exact_one_step_cover', 'infinite_continuation': 'not_checked'}


def request_digest(request):
    return hashlib.sha256(json.dumps(request, sort_keys=True).encode()).hexdigest()


def verify_result(request, result):
    """Check a submitted candidate against the receiver's request, never its own.

    Search scores, completeness of exploration and embedded verdicts are not
    trusted. The certificate emitter takes this same independent request.
    """
    read_request(request)
    if not isinstance(result, dict) or not isinstance(result.get('best'), dict):
        return {'valid': False, 'reason': 'no candidate trace'}
    if result.get('request_sha256') != request_digest(request) or result.get('request') != request:
        return {'valid': False, 'reason': 'candidate is bound to a different request'}
    digits = result['best'].get('digits')
    if not isinstance(digits, list):
        return {'valid': False, 'reason': 'candidate digits must be a list'}
    checked = check_trace(request, digits)
    return {**checked, 'valid': bool(checked.get('valid') and checked.get('complete')),
            'request_sha256': request_digest(request),
            'optimality': 'not_checked', 'kernel_status': 'not_run'}


def read_request(request):
    if set(request) - {'target', 'steps', 'support', 'label'}:
        raise ValueError('unsupported request fields')
    target = exact(request['target'])
    steps = tuple(Step.read(row) for row in request['steps'])
    support = request.get('support', 'free')
    if target < 0 or not steps or support not in ('free', 'divisor-count'):
        raise ValueError('need nonnegative target, nonempty steps, supported relation')
    return target, steps, support


def divisor_base(bits):
    """Proper-divisor contribution at the next positive index."""
    n = len(bits) + 1
    return sum(bit for k, bit in enumerate(bits, 1) if n % k == 0)


def available(step, cumulative, remainder, bits, support):
    choices = step.choices(cumulative, remainder)
    if support == 'free':
        return choices
    # d_n = sum_{k|n} x_k. Choosing x_n in {0,1} constructs a real support
    # prefix; arbitrary integer coefficients are never relabelled as support.
    base = divisor_base(bits)
    return tuple(d for d in (base, base + 1) if choices.contains(d))


def check_trace(request, digits):
    """Exact finite evidence only; a valid prefix need not extend infinitely."""
    target, steps, support = read_request(request)
    if len(digits) > len(steps):
        return {'valid': False, 'reason': 'trace exceeds supplied schedule'}
    c, r, bits = 0, target, []
    for n, digit in enumerate(digits):
        if not steps[n].check(c, r, digit):
            return {'valid': False, 'reason': f'step contract rejected at {n}'}
        if support == 'divisor-count':
            bit = digit - divisor_base(bits)
            if bit not in (0, 1):
                return {'valid': False, 'reason': f'no Boolean support witness at {n}'}
            bits.append(bit)
        c += digit
        r -= digit * steps[n].weight
    return {'valid': True, 'complete': len(digits) == len(steps),
            'cumulative': c, 'remainder': str(r), 'support_bits': bits,
            'evidence': 'exact_finite_arithmetic', 'infinite_continuation': 'not_checked'}


def score_trace(digits, objective):
    if objective == 'energy':
        return sum(d*d for d in digits)
    if objective == 'variation':
        return sum(abs(b-a) for a, b in zip(digits, digits[1:]))
    if objective == 'mass':
        return sum(digits)
    raise ValueError('unknown objective')


def explore(request, *, runner='enumerate', objective='energy', budget=10000,
            seed=0, backend='compiled', policy=None):
    """One specification, several runners; budgets count digit proposals.

    Enumeration uses DFS; random and targeted policies restart after dead ends.
    The baseline scans the allowance and directly checks the same relation.
    Finite exhaustion is reported only after the complete bounded tree closes.
    """
    target, steps, support = read_request(request)
    if type(budget) is not int or budget <= 0:
        raise ValueError('budget must be positive')
    if runner == 'evolve':
        if backend != 'compiled':
            raise ValueError('evolution uses compiled choices; compare filter enumeration separately')
        return evolve_policies(request, objective=objective, budget=budget, seed=seed)
    if runner not in ('enumerate', 'random', 'targeted', 'policy') or backend not in ('compiled', 'filter'):
        raise ValueError('unsupported runner/backend')
    if runner == 'policy':
        if (not isinstance(policy, (list, tuple)) or not 1 <= len(policy) <= 64
                or any(p not in ('min', 'max', 'middle', 'previous') for p in policy)):
            raise ValueError('policy must contain 1..64 supported choice instructions')
    score_trace((), objective)
    rng = random.Random(seed)
    proposals, transitions, dead_ends, completed, best = 0, 0, 0, 0, None
    seen = set()
    exhausted = False

    def candidates(n, c, r, bits, digits):
        if backend == 'filter':
            pool = Progression(0, 1, steps[n].allowance + 1)
        else:
            pool = available(steps[n], c, r, bits, support)
        count = pool.count if isinstance(pool, Progression) else len(pool)
        at = pool.at if isinstance(pool, Progression) else pool.__getitem__
        if runner == 'enumerate':
            return iter(pool)
        if not count:
            return iter(())
        if runner == 'random':
            return iter((at(rng.randrange(count)),))
        if runner == 'policy':
            instruction = policy[n % len(policy)]
            if instruction == 'min':
                index = 0
            elif instruction == 'max':
                index = count - 1
            elif instruction == 'middle':
                index = (count - 1) // 2
            else:
                previous = digits[-1] if digits else 0
                stride = pool.stride if isinstance(pool, Progression) else 1
                index = max(0, min(count - 1, (previous - at(0)) // stride))
            return iter((at(index),))
        # Convex objectives attain their maximum at an endpoint of this
        # progression (or the two-point Boolean-support intersection).
        ends = {at(0), at(count - 1)}
        return iter((max(ends, key=lambda d: (score_trace(digits + (d,), objective), -d)),))

    def initial():
        return (0, 0, target, (), (), candidates(0, 0, target, (), ()))

    stack = [initial()]
    while stack and proposals < budget:
        n, c, r, bits, digits, iterator = stack[-1]
        try:
            d = next(iterator)
        except StopIteration:
            stack.pop()
            if not stack and runner not in ('enumerate', 'policy') and proposals < budget:
                # A root without choices cannot be improved by restarting.
                if not available(steps[0], 0, target, (), support):
                    break
                if backend == 'compiled' and not steps[0].choices(0, target).count:
                    break
                stack = [initial()]
            continue
        proposals += 1
        if not steps[n].check(c, r, d):
            continue
        newbits = bits
        if support == 'divisor-count':
            bit = d - divisor_base(bits)
            if bit not in (0, 1):
                continue
            newbits = bits + (bit,)
        transitions += 1
        newdigits = digits + (d,)
        if n + 1 == len(steps):
            completed += 1
            seen.add(newdigits)
            score = score_trace(newdigits, objective)
            if best is None or score > best['score']:
                best = {'digits': list(newdigits), 'score': score}
        else:
            child = candidates(n + 1, c + d, r - d * steps[n].weight, newbits, newdigits)
            # Each empty continuation is a local dead end, never an
            # infinite impossibility certificate.
            pool = available(steps[n + 1], c + d, r - d * steps[n].weight, newbits, support)
            size = pool.count if isinstance(pool, Progression) else len(pool)
            if not size:
                dead_ends += 1
            stack.append((n + 1, c + d, r - d * steps[n].weight, newbits, newdigits, child))
    if runner == 'enumerate':
        # Check exhaustion without spending another proposal. Do not declare
        # an empty tree when the budget ended before an unexplored branch.
        exhausted = True
        for frame in stack:
            if next(frame[-1], None) is not None:
                exhausted = False
                break
    if best is not None:
        best['check'] = check_trace(request, best['digits'])
    return {'runner': runner, 'backend': backend, 'objective': objective, 'seed': seed,
            'policy': list(policy) if policy else None,
            'budget': budget, 'proposals': proposals, 'valid_transitions': transitions,
            'dead_ends': dead_ends, 'completed_traces': completed,
            'distinct_complete_traces': len(seen), 'exhausted': exhausted,
            'complete_trace_set_sha256': hashlib.sha256(json.dumps(sorted(seen)).encode()).hexdigest(),
            'status': ('finite_optimum' if best and exhausted else 'finite_candidate' if best
                       else 'finite_incompatible' if exhausted else 'budget_exhausted'),
            'best': best, 'evidence': 'exact_finite_arithmetic',
            'infinite_continuation': 'requires all-step admissibility and vanishing bounds'}


def evolve_policies(request, *, objective='energy', budget=10000, seed=0):
    """Bounded native policy evolution; no external code or model is executed.

    Keep a small diverse population, mutate/cross over choice programmes, and
    return the reusable programme with its complete derivation cost. This is
    inspired by programme evolution, not an implementation of AlphaEvolve.
    """
    rng = random.Random(seed)
    alphabet = ('min', 'max', 'middle', 'previous')
    length = min(8, len(request['steps']))
    population, proposals, evaluations, best, distinct = [], 0, 0, None, set()
    transitions = 0
    while proposals < budget and evaluations < budget:
        if evaluations < len(alphabet):
            genes = [alphabet[evaluations]] * length
        elif population:
            genes = list(rng.choice(population)[1])
            donor = rng.choice(population)[1]
            cut = rng.randrange(length)
            genes[cut:] = donor[cut:]
            genes[rng.randrange(length)] = rng.choice(alphabet)
        else:
            genes = [rng.choice(alphabet) for _ in range(length)]
        result = explore(request, runner='policy', policy=genes, objective=objective,
                         budget=budget-proposals, seed=seed)
        evaluations += 1
        proposals += result['proposals']
        transitions += result['valid_transitions']
        if result['best']:
            trace = tuple(result['best']['digits'])
            distinct.add(trace)
            fitness = result['best']['score']
            entry = (fitness, tuple(genes), trace)
            if entry not in population:
                population.append(entry)
            population.sort(key=lambda p: (-p[0], p[1]))
            # At most one representative per realised trace in the active
            # population; successful source and evidence are never deleted.
            seen, retained = set(), []
            for row in population:
                if row[2] not in seen:
                    retained.append(row)
                    seen.add(row[2])
            population = retained[:8]
            if best is None or fitness > best['best']['score']:
                best = result
        if result['proposals'] == 0:
            break
    return {'runner': 'evolve', 'backend': 'compiled', 'objective': objective,
            'seed': seed, 'budget': budget, 'proposals': proposals,
            'valid_transitions': transitions, 'evaluated_programmes': evaluations,
            'distinct_complete_traces': len(distinct), 'exhausted': False,
            'status': 'finite_candidate' if best else 'budget_exhausted',
            'best': best['best'] if best else None,
            'policy': best['policy'] if best else None,
            'evidence': 'exact_finite_arithmetic',
            'infinite_continuation': 'not_checked',
            'retention': 'candidate policy; rerun on the next request; no proof or novelty promotion'}


def shrink_trace(request, digits, predicate, budget=1000):
    """Simplify a counterexample only through replay of the same relation.

    The predicate remains researcher-supplied, and each accepted change must
    keep it true. This is a bounded greedy shrink, not a minimality theorem.
    """
    if type(budget) is not int or budget <= 0:
        raise ValueError('shrink budget must be positive')
    if not check_trace(request, digits).get('complete') or not predicate(digits):
        raise ValueError('shrinking needs a complete admissible counterexample')
    target, steps, support = read_request(request)
    result, checks = list(digits), 0
    for i in range(len(result)):
        c = sum(result[:i])
        r = target - sum((steps[j].weight * result[j] for j in range(i)), Fraction(0))
        bits = check_trace(request, result[:i])['support_bits']
        for d in available(steps[i], c, r, bits, support):
            if d >= result[i] or checks >= budget:
                break
            candidate = result[:i] + [d] + result[i + 1:]
            checks += 1
            check = check_trace(request, candidate)
            if check.get('complete') and predicate(candidate):
                result = candidate
                break
    return {'digits': result, 'checks': checks, 'check': check_trace(request, result)}


def lean_certificate(request, digits):
    """Translate a *finite* trace into independent real-arithmetic obligations.

    Reuse proof_workbench.py probe/replay for validation. Python output has no
    kernel status until that existing owner actually accepts these bytes.
    """
    check = check_trace(request, digits)
    if not check.get('complete'):
        raise ValueError('certificate requires a complete admissible trace')
    target, steps, support = read_request(request)
    def q(x):
        return f'({x.numerator} / {x.denominator} : ℝ)'
    lines = ['import ErdosProblems.Synthesis.FeedbackContinuation',
             'open ErdosProblems.Synthesis.FeedbackContinuation',
             'namespace FeedbackTrace']
    c, r, bits = 0, target, []
    for i, (step, d) in enumerate(zip(steps, digits)):
        lines += [f'theorem step_{i} : Admissible {step.allowance} {step.modulus} {c} {d}',
                  f'    {q(step.weight)} {q(step.lower)} {q(step.upper)} {q(r)} := by',
                  '  norm_num [Admissible]']
        for j, (a, m) in enumerate(step.congruences):
            lines += [f'example : ({d} : ℤ) % {m} = {a} := by norm_num']
        if support == 'divisor-count':
            bit = d - divisor_base(bits)
            bits.append(bit)
            summands = [str(b) for k, b in enumerate(bits, 1) if (i + 1) % k == 0]
            lines += [f'example : ({d} : ℕ) = ' + ' + '.join(summands) + ' := by norm_num']
        c += d
        r -= d * step.weight
    lines += ['end FeedbackTrace']
    return '\n'.join(lines) + '\n'


def demo_request(stages=8, support='free'):
    if support == 'free':
        return {'label': 'feedback-policy-development-control', 'target': '4',
                'steps': [{'allowance': 8, 'modulus': 2,
                           'weight': str(Fraction(1, 2 ** (n+1))),
                           'lower': str(Fraction(2, 2 ** (n+1))),
                           'upper': str(Fraction(6, 2 ** (n+1)))} for n in range(stages)]}
    return {'label': 'Boolean-divisor-support-composition', 'target': '1',
            'support': 'divisor-count',
            'steps': [{'allowance': n+1, 'modulus': 1,
                       'weight': str(Fraction(1, 2 ** (n+1))), 'lower': '0',
                       'upper': str(Fraction(n+3, 2 ** (n+1)))} for n in range(stages)]}


def run_request(args):
    request = json.loads(args.request.read_text()) if args.request else demo_request(support=args.support)
    policy = None
    if args.policy_result:
        policy = json.loads(args.policy_result.read_text())['policy']
        if args.runner != 'policy':
            raise ValueError('--policy-result requires --runner policy')
    result = explore(request, runner=args.runner, objective=args.objective,
                     budget=args.budget, seed=args.seed, backend=args.backend, policy=policy)
    if args.policy_result:
        result['policy_parent_sha256'] = hashlib.sha256(args.policy_result.read_bytes()).hexdigest()
    result['request'] = request
    result['request_sha256'] = request_digest(request)
    result['implementation_sha256'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    if args.lean:
        if result['best'] is None:
            raise ValueError('no complete trace to certify')
        args.lean.write_text(lean_certificate(request, result['best']['digits']))
        result['lean_candidate'] = str(args.lean)
        result['lean_status'] = 'not_run_use_proof_workbench_probe'
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


def evaluate():
    """Reproducible development controls; includes all policy derivation work."""
    free, support = demo_request(), demo_request(support='divisor-count')
    comparisons = []
    for label, request in [('feedback', free), ('support-composition', support)]:
        for backend in ('compiled', 'filter'):
            result = explore(request, backend=backend, budget=50000)
            comparisons.append({'case': label, **result})
    training = explore(free, runner='evolve', budget=2048, seed=17)
    transfer = demo_request(10)
    transfer['target'] = '7/2'
    reused = explore(transfer, runner='policy', policy=training['policy'])
    incompatible = {'target': '2', 'support': 'divisor-count', 'steps': [
        {'allowance': 2, 'modulus': 2, 'weight': '1', 'lower': '0', 'upper': '0'}]}
    return {'evidence': 'exact_finite_arithmetic',
            'experiment_role': 'development_controls_not_prospective_discovery',
            'implementation_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'requests': {'feedback': free, 'support-composition': support,
                         'transfer': transfer, 'incompatible': incompatible},
            'exhaustive_comparisons': comparisons,
            'matched_proposal_budget': [explore(free, runner=r, budget=2048, seed=17)
                                       for r in ('enumerate', 'random', 'targeted', 'evolve')]
                + [explore(free, backend='filter', budget=2048, seed=17)],
            'policy_training': training, 'policy_reuse': reused,
            'incompatible_composition': explore(incompatible),
            'cost_boundary': 'proposals count all derivation trials; timings, model tokens, literature reading and implementation cost are not measured',
            'research_gain': 'not_established; requires compute-matched agent and prose/lemma baselines on prospective tasks'}


def residue_step(u, cumulative, modulus):
    residue = (-cumulative) % modulus
    digit = residue + modulus * ((u - modulus - residue) // modulus)
    residual = u - digit
    assert digit >= 0
    assert modulus <= residual < 2 * modulus
    assert (cumulative + digit) % modulus == 0
    return digit, residual


def largest_factorial(limit):
    value, k = 1, 2
    while value * k <= limit:
        value *= k
        k += 1
    return value


def run_feedback(gap, exponent, stages=400):
    # Explicit finite admissibility checks, independent of asymptotic claims.
    # Working with n! times the residual avoids constructing giant factorials.
    n, modulus = 100, 1
    outputs = []
    for initial in (Fraction(1), Fraction(7, 6), Fraction(3, 2), Fraction(2)):
        n, modulus, total, residual = 100, 1, 0, initial
        maximum_modulus = 1
        for _ in range(stages):
            next_n = n + gap
            ratio = 1
            for k in range(n + 1, next_n + 1):
                ratio *= k
            cap = next_n ** exponent
            next_modulus = largest_factorial(min(isqrt(ratio) // 2,
                                                cap // (2 * ratio)))
            assert next_modulus % modulus == 0
            assert 2 * next_modulus <= modulus * ratio
            assert 2 * modulus * ratio <= cap
            digit, residual = residue_step(residual * ratio, total, next_modulus)
            assert digit <= cap and digit % modulus == 0
            total += digit
            maximum_modulus = max(maximum_modulus, next_modulus)
            n, modulus = next_n, next_modulus
        outputs.append({"initial_scaled_target": str(initial),
                        "stages": stages, "last_index": n,
                        "maximum_modulus": maximum_modulus,
                        "final_scaled_residual": str(residual)})
    return {"gap": gap, "allowance_exponent": exponent, "targets": outputs}


def rational_cantor_counterexample(stages=25):
    denominator, partial, cumulative = 1, Fraction(0), 0
    for n in range(1, stages + 1):
        correction = 2 if n == 1 else n * factorial(n)
        base = correction + 2
        denominator *= base
        partial += Fraction(correction + 1, denominator)
        cumulative += correction
        assert cumulative == factorial(n + 1)
        assert partial == 1 - Fraction(1, denominator)
        assert gcd(base, correction) <= 2
    return {"stages": stages, "identity": "partial = 1 - 1/Q_n",
            "cumulative_identity": "sum(e_k,k<=n) = (n+1)!",
            "gcd_bound": 2}


def support_density_trap(limit=4096):
    support = [n for n in range(1, limit + 1) if n & (n - 1)]
    gaps = [b-a for a,b in zip(support,support[1:])]
    assert max(gaps) == 2
    return {"description": "all positive integers except powers of two",
            "cutoff": limit, "permitted_positions": len(support),
            "gaps_of_length_two": gaps.count(2),
            "infinite_conclusion": "proved in paper, not inferred from this sample"}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--explore', action='store_true')
    parser.add_argument('--evaluate', action='store_true', help='replay development controls and matched proposal budgets')
    parser.add_argument('--request', type=Path)
    parser.add_argument('--runner', choices=('enumerate', 'random', 'targeted', 'evolve', 'policy'), default='enumerate')
    parser.add_argument('--policy-result', type=Path, help='reuse the candidate policy from an earlier result JSON')
    parser.add_argument('--backend', choices=('compiled', 'filter'), default='compiled')
    parser.add_argument('--objective', choices=('energy', 'variation', 'mass'), default='energy')
    parser.add_argument('--support', choices=('free', 'divisor-count'), default='free')
    parser.add_argument('--budget', type=int, default=10000)
    parser.add_argument('--verify-result', type=Path, help='replay returned digits against mandatory independent --request')
    parser.add_argument('--cover', action='store_true', help='inspect the exact one-step cover at the initial state')
    parser.add_argument('--seed', type=int, default=0)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--lean', type=Path)
    args = parser.parse_args()
    if args.verify_result or args.cover:
        if args.request is None:
            parser.error('--verify-result and --cover require an independent --request file')
        request = json.loads(args.request.read_text())
        target, steps, support = read_request(request)
        if args.verify_result:
            candidate = json.loads(args.verify_result.read_text())
            result = verify_result(request, candidate)
            if args.lean and result['valid']:
                args.lean.write_text(lean_certificate(request, candidate['best']['digits']))
        else:
            result = remainder_cover(steps[0], 0, support=support)
        if args.output:
            args.output.write_text(json.dumps(result, indent=2) + '\n')
        print(json.dumps(result, indent=2))
        raise SystemExit(0 if result.get('valid', True) else 1)
    if args.evaluate:
        result = evaluate()
        if args.output:
            args.output.write_text(json.dumps(result, indent=2) + '\n')
        print(json.dumps(result, indent=2))
        raise SystemExit(0)
    if args.explore or args.request:
        run_request(args)
        raise SystemExit(0)
    result = {"evidence": "exact finite arithmetic",
              "feedback": [run_feedback(1, 2), run_feedback(2, 3), run_feedback(3, 4)],
              "rational_counterexample": rational_cantor_counterexample(),
              "density_trap": support_density_trap()}
    print(json.dumps(result, indent=2))
