#!/usr/bin/env python3
"""Erdos #243: primitive-coordinate statistics and the (E_n, r_n) Diophantine map.

Two experiments on exact pseudo-greedy orbits (engine: erdos243_orbit_engine.py).

EXPERIMENT 2 -- primitive statistics.
  G_n = gcd(C_n, D_n), u_n = C_n/G_n, v_n = D_n/G_n, eps_n = E_n/G_n,
  w_n = u_n - eps_n, h_n = G_{n+1}/G_n, h_n u_{n+1} = w_n.
  Recorded: the multiset of CLEAN (h_n = 1) strict-rise sizes -eps_n; how often
  a rise >= 3 occurs; the record-setting jump sizes on the record subsequence of
  u; whether every orbit that reaches u >= 5 has a clean record jump >= 3 before
  terminating (r07 asserts a NONTERMINATING orbit must; on terminating orbits
  this is purely descriptive); and, per strict clean rise, the prime powers
  P = p^l || v_n with p <= 3u_n/2, split into PROTECTED (p^{l+1} > w_n, so the
  erasure condition p^{l+1} | w_n of r03/r07 is unsatisfiable at this step) and
  unprotected.

EXPERIMENT 3 -- the (E_n, r_n) Diophantine map.
  With r_n := D_n mod C_{n+1}, the exact identities are

      C_n * E_{n+1} = r_n^2   (mod C_{n+1}),
      E_n * E_{n+1} = r_n^2   (mod C_{n+1}),

  both UNCONDITIONAL (no coprimality needed).  Proof: D_{n+1} = D_n a_n and
  a_n C_n = D_n + C_{n+1}, so C_n D_{n+1} = D_n(D_n + C_{n+1}) = D_n^2 = r_n^2
  mod C_{n+1}; and C_{n+1} = C_n - E_n gives C_n = E_n mod C_{n+1}.  When
  gcd(C_n, C_{n+1}) = 1 this inverts to E_{n+1} = r_n^2 C_n^{-1} (mod C_{n+1}).
  So E_n E_{n+1} must be a square modulo C_{n+1} at every single step.
  Measured: how often that is satisfied TRIVIALLY (E_n E_{n+1} a perfect square
  in Z -- e.g. the flat run E = -1, -1 -- or E_{n+1} = 0) versus by a genuine
  arithmetic coincidence; and, as a cost measure, the density
      d_n = #{ f mod C_{n+1} : E_n f is a square mod C_{n+1} } / C_{n+1},
  i.e. the fraction of the centred-error alphabet the constraint leaves open.
  Also: the distribution of |E_n|/C_n along orbits surviving >= 15 steps.

Prime data for v_n is exact-phase-only (v_n is doubly exponential; the modular
phase carries D_n only modulo the shrinking suffix product).  Coverage of the
prime sub-experiment is reported explicitly.

Examples
--------
    ./repo-python .../erdos243_primitive_residue_lab.py --quick
    ./repo-python .../erdos243_primitive_residue_lab.py --qmax 2500 --out r.json
"""

from __future__ import annotations

import argparse
import json
import math
import random
import sys
import time
from collections import Counter, defaultdict
from math import gcd, isqrt
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from erdos243_orbit_engine import TERMINATED, run_orbit  # noqa: E402

QR_DENSITY_MAX_C = 3000


def primes_upto(n: int) -> list[int]:
    sieve = bytearray([1]) * (n + 1)
    sieve[0:2] = b"\x00\x00"
    for i in range(2, isqrt(n) + 1):
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(sieve[i * i::i]))
    return [i for i in range(n + 1) if sieve[i]]


def valuation(n: int, p: int) -> int:
    e = 0
    while n % p == 0:
        n //= p
        e += 1
    return e


def is_perfect_square(n: int) -> bool:
    if n < 0:
        return False
    r = isqrt(n)
    return r * r == n


_qr_cache: dict[int, frozenset] = {}


def squares_mod(m: int) -> frozenset:
    s = _qr_cache.get(m)
    if s is None:
        s = frozenset((x * x) % m for x in range(m))
        if len(_qr_cache) < 6000:
            _qr_cache[m] = s
    return s


def qr_open_density(E_n: int, m: int) -> float:
    """Fraction of f mod m with E_n * f a square mod m."""
    sq = squares_mod(m)
    a = E_n % m
    return sum(1 for f in range(m) if (a * f) % m in sq) / m


class Lab:
    def __init__(self, prime_bound: int, u_cap_for_primes: int):
        self.primes = primes_upto(prime_bound)
        self.prime_bound = prime_bound
        self.u_cap_for_primes = u_cap_for_primes
        self.orbits = 0
        self.steps = 0
        # identities
        self.id_checked = 0
        self.id_fail_Cn = 0
        self.id_fail_En = 0
        self.id_coprime_checked = 0
        self.id_coprime_fail = 0
        self.gcd_u_consec_fail = 0
        self.gcd_u_consec_checked = 0
        self.h_identity_fail = 0
        self.h_identity_checked = 0
        # primitive statistics
        self.clean_rise_sizes = Counter()
        self.dirty_rise_sizes = Counter()
        self.h_dist = Counter()
        self.record_jumps = Counter()
        self.clean_record_jumps = Counter()
        self.orbits_reaching_u5 = 0
        self.orbits_u5_with_clean_record_jump_ge3 = 0
        self.orbits_u5_without = []
        self.record_set_by_dirty_step = 0
        self.orbits_with_record_advance = 0
        self.orbits_all_record_jumps_le2 = 0
        self.examples_all_le2 = []
        self.max_record_jump_hist = Counter()
        self.longest_le2_climb = (0, None)
        self.highest_le2_climb = (0, None)
        # prime protection
        self.prime_cov_have = 0
        self.prime_cov_missing = 0
        self.protect_by_rise = defaultdict(lambda: {"n": 0, "protected": 0,
                                                    "unprotected": 0,
                                                    "protected_erasure_threshold": 0,
                                                    "unprotected_erasure_threshold": 0,
                                                    "maxpp_protected": 0})
        self.unprotected_examples = []
        # QR analysis
        self.qr_total = 0
        self.qr_zero_next = 0
        self.qr_perfect_square = 0
        self.qr_nontrivial = 0
        self.qr_negative_product = 0
        self.qr_density_stride = 31
        self.qr_density_stride_ctr = 0
        self.qr_nontrivial_density_sum = 0.0
        self.qr_nontrivial_density_n = 0
        self.qr_density_hist = Counter()
        self.qr_pair_counter = Counter()
        # long orbits
        self.long_orbits = 0
        self.long_absE_hist = Counter()
        self.long_absE_sum = 0.0
        self.long_absE_n = 0
        self.long_examples = []

    # ------------------------------------------------------------------
    def ingest(self, p: int, q: int, orb: dict, do_qr: bool = True) -> None:
        C, E, G, R, Dx = orb["C"], orb["E"], orb["G"], orb["R"], orb["Dexact"]
        L = len(E)
        self.orbits += 1
        self.steps += L
        u = [C[n] // G[n] for n in range(L)]
        eps = [E[n] // G[n] for n in range(L)]

        for n in range(L - 1):
            Cn1 = C[n + 1]
            if R[n] is not None:
                self.id_checked += 1
                if (C[n] * E[n + 1] - R[n] ** 2) % Cn1:
                    self.id_fail_Cn += 1
                if (E[n] * E[n + 1] - R[n] ** 2) % Cn1:
                    self.id_fail_En += 1
                if gcd(C[n] % Cn1, Cn1) == 1:
                    self.id_coprime_checked += 1
                    inv = pow(C[n] % Cn1, -1, Cn1)
                    if (E[n + 1] - R[n] ** 2 * inv) % Cn1:
                        self.id_coprime_fail += 1
            self.gcd_u_consec_checked += 1
            if gcd(u[n], u[n + 1]) != 1:
                self.gcd_u_consec_fail += 1
            h = G[n + 1] // G[n]
            self.h_dist[h] += 1
            self.h_identity_checked += 1
            if G[n + 1] % G[n] or h * u[n + 1] != u[n] - eps[n]:
                self.h_identity_fail += 1
            rise = u[n + 1] - u[n]
            if rise > 0:
                if h == 1:
                    self.clean_rise_sizes[rise] += 1
                else:
                    self.dirty_rise_sizes[rise] += 1
            # prime protection at a strict clean rise
            if rise > 0 and h == 1 and u[n] <= self.u_cap_for_primes:
                if Dx[n] is None:
                    self.prime_cov_missing += 1
                else:
                    self.prime_cov_have += 1
                    vn = Dx[n] // G[n]
                    w = u[n] - eps[n]
                    bound = 3 * u[n] // 2
                    prot = unprot = 0
                    prot2 = unprot2 = 0
                    maxpp = 0
                    for pr in self.primes:
                        if pr > bound:
                            break
                        if vn % pr:
                            continue
                        l = valuation(vn, pr)
                        pp = pr ** l
                        # DERIVED erasure threshold.  v_{n+1} = a_n v_n / h_n with
                        # h_n = gcd(w_n, a_n^2).  Put k = v_p(a_n); then
                        # v_p(h_n) = min(v_p(w_n), 2k), so v_p(v) can drop at all only
                        # when k >= 1 and v_p(w_n) > k, and can drop by the full l only
                        # when v_p(h_n) = k + l, which needs 2k >= k + l (k >= l) and
                        # v_p(w_n) >= k + l >= 2l.  Hence FULL erasure of p^l requires
                        # p^{2l} | w_n, not p^{l+1} | w_n.  The two agree at l = 1.
                        if pr ** (2 * l) > w:
                            prot2 += 1
                        else:
                            unprot2 += 1
                        if pr ** (l + 1) > w:
                            prot += 1
                            maxpp = max(maxpp, pp)
                        else:
                            unprot += 1
                            if len(self.unprotected_examples) < 25:
                                self.unprotected_examples.append(
                                    {"p": p, "q": q, "n": n, "u": u[n],
                                     "eps": eps[n], "w": w, "prime": pr,
                                     "l": l, "rise": rise})
                    rec = self.protect_by_rise[min(rise, 12)]
                    rec["n"] += 1
                    rec["protected"] += prot
                    rec["unprotected"] += unprot
                    rec["protected_erasure_threshold"] += prot2
                    rec["unprotected_erasure_threshold"] += unprot2
                    rec["maxpp_protected"] = max(rec["maxpp_protected"], maxpp)

        # record subsequence of u.  NOTE (exact): a record can only be set by a
        # CLEAN step.  u_{n} = w_{n-1}/h_{n-1} with w_{n-1} = u_{n-1} - eps_{n-1}
        # <= (3/2) u_{n-1}, so h_{n-1} >= 2 forces u_n <= (3/4) u_{n-1} <= the
        # running record.  The two histograms below therefore coincide, and this
        # is a proof, not a coincidence.
        recu = u[0]
        n_records = 0
        max_jump = 0
        prefix_le2_records = 0
        prefix_le2_maxu = u[0]
        prefix_le2_open = True
        for n in range(1, L):
            if u[n] > recu:
                jump = u[n] - recu
                n_records += 1
                max_jump = max(max_jump, jump)
                self.record_jumps[min(jump, 200)] += 1
                h = G[n] // G[n - 1] if G[n] % G[n - 1] == 0 else None
                if h == 1:
                    self.clean_record_jumps[min(jump, 200)] += 1
                else:
                    self.record_set_by_dirty_step += 1
                if prefix_le2_open:
                    if jump <= 2:
                        prefix_le2_records += 1
                        prefix_le2_maxu = u[n]
                    else:
                        prefix_le2_open = False
                recu = u[n]
        if n_records:
            self.orbits_with_record_advance += 1
            self.max_record_jump_hist[min(max_jump, 200)] += 1
            if max_jump <= 2:
                self.orbits_all_record_jumps_le2 += 1
                if len(self.examples_all_le2) < 20:
                    self.examples_all_le2.append(
                        {"p": p, "q": q, "u": u[:30], "eps": eps[:30],
                         "records": n_records, "status": orb["status"]})
            if prefix_le2_records > self.longest_le2_climb[0]:
                self.longest_le2_climb = (prefix_le2_records,
                                          {"p": p, "q": q, "u": u[:30],
                                           "max_u_in_prefix": prefix_le2_maxu})
            if prefix_le2_maxu - u[0] > self.highest_le2_climb[0]:
                self.highest_le2_climb = (prefix_le2_maxu - u[0],
                                          {"p": p, "q": q, "u": u[:30],
                                           "u_0": u[0], "top_u": prefix_le2_maxu,
                                           "records_in_prefix": prefix_le2_records})
        if max(u) >= 5 and n_records:
            self.orbits_reaching_u5 += 1
            if max_jump >= 3:
                self.orbits_u5_with_clean_record_jump_ge3 += 1
            elif len(self.orbits_u5_without) < 25:
                self.orbits_u5_without.append({"p": p, "q": q, "u": u[:30],
                                               "eps": eps[:30],
                                               "status": orb["status"]})

        # QR analysis
        if do_qr:
            for n in range(L - 1):
                Cn1 = C[n + 1]
                self.qr_total += 1
                prod = E[n] * E[n + 1]
                if E[n + 1] == 0:
                    self.qr_zero_next += 1
                elif is_perfect_square(prod):
                    self.qr_perfect_square += 1
                    self.qr_pair_counter[(E[n], E[n + 1])] += 1
                else:
                    self.qr_nontrivial += 1
                    if prod < 0:
                        self.qr_negative_product += 1
                    # the density is O(C) to evaluate, so subsample
                    self.qr_density_stride_ctr += 1
                    if (2 <= Cn1 <= QR_DENSITY_MAX_C
                            and self.qr_density_stride_ctr % self.qr_density_stride == 0):
                        d = qr_open_density(E[n], Cn1)
                        self.qr_nontrivial_density_sum += d
                        self.qr_nontrivial_density_n += 1
                        self.qr_density_hist[min(int(20 * d), 20)] += 1

        # long-orbit normalised error profile
        if L - 1 >= 15:
            self.long_orbits += 1
            if len(self.long_examples) < 12:
                self.long_examples.append(
                    {"p": p, "q": q, "steps": L - 1, "C": C[:40], "E": E[:40],
                     "u": u[:40], "eps": eps[:40]})
            for n in range(L):
                r = abs(E[n]) / C[n]
                self.long_absE_hist[min(int(20 * r), 10)] += 1
                self.long_absE_sum += r
                self.long_absE_n += 1

    # ------------------------------------------------------------------
    def report(self) -> dict:
        pbr = {str(k): dict(v) for k, v in sorted(self.protect_by_rise.items())}
        for k, v in pbr.items():
            v["mean_protected_per_rise"] = v["protected"] / v["n"] if v["n"] else None
            v["mean_unprotected_per_rise"] = v["unprotected"] / v["n"] if v["n"] else None
            tot = v["protected"] + v["unprotected"]
            v["protected_fraction"] = v["protected"] / tot if tot else None
            tot2 = v["protected_erasure_threshold"] + v["unprotected_erasure_threshold"]
            v["protected_fraction_erasure_threshold"] = (
                v["protected_erasure_threshold"] / tot2 if tot2 else None)
        return {
            "orbits": self.orbits,
            "steps": self.steps,
            "experiment_3_identities": {
                "pairs_checked": self.id_checked,
                "fail_C_n_E_{n+1}_eq_r_n^2_mod_C_{n+1}": self.id_fail_Cn,
                "fail_E_n_E_{n+1}_eq_r_n^2_mod_C_{n+1}": self.id_fail_En,
                "coprime_pairs_checked": self.id_coprime_checked,
                "fail_E_{n+1}_eq_r_n^2_invC_n_mod_C_{n+1}": self.id_coprime_fail,
                "general_case_note": "both congruences hold with NO coprimality "
                                     "hypothesis; the inverted form needs "
                                     "gcd(C_n, C_{n+1}) = 1, which fails on "
                                     f"{self.id_checked - self.id_coprime_checked} "
                                     "of the pairs checked",
                "gcd_u_n_u_{n+1}_eq_1_checked": self.gcd_u_consec_checked,
                "gcd_u_n_u_{n+1}_eq_1_failures": self.gcd_u_consec_fail,
                "h_n_u_{n+1}_eq_w_n_checked": self.h_identity_checked,
                "h_n_u_{n+1}_eq_w_n_failures": self.h_identity_fail,
            },
            "experiment_3_quadratic_residue_cost": {
                "step_pairs": self.qr_total,
                "trivial_because_E_{n+1}_zero": self.qr_zero_next,
                "trivial_because_E_n_E_{n+1}_perfect_square_in_Z": self.qr_perfect_square,
                "nontrivial": self.qr_nontrivial,
                "nontrivial_with_negative_product": self.qr_negative_product,
                "fraction_nontrivial": (self.qr_nontrivial / self.qr_total
                                        if self.qr_total else None),
                "top_perfect_square_pairs": [
                    {"E_n_E_np1": list(k), "count": v}
                    for k, v in self.qr_pair_counter.most_common(15)],
                "mean_open_density_on_nontrivial_steps": (
                    self.qr_nontrivial_density_sum / self.qr_nontrivial_density_n
                    if self.qr_nontrivial_density_n else None),
                "open_density_sampled_steps": self.qr_nontrivial_density_n,
                "open_density_histogram_twentieths": dict(sorted(self.qr_density_hist.items())),
                "definition_open_density": "#{f mod C_{n+1} : E_n f is a square mod "
                                           "C_{n+1}} / C_{n+1}",
            },
            "experiment_2_primitive": {
                "h_distribution": dict(sorted(self.h_dist.items())),
                "clean_rise_size_multiset": dict(sorted(self.clean_rise_sizes.items())),
                "dirty_rise_size_multiset": dict(sorted(self.dirty_rise_sizes.items())),
                "clean_rises_total": sum(self.clean_rise_sizes.values()),
                "clean_rises_ge_3": sum(v for k, v in self.clean_rise_sizes.items() if k >= 3),
                "clean_rises_ge_3_fraction": (
                    sum(v for k, v in self.clean_rise_sizes.items() if k >= 3)
                    / sum(self.clean_rise_sizes.values())
                    if self.clean_rise_sizes else None),
                "record_jump_sizes": dict(sorted(self.record_jumps.items())),
                "clean_record_jump_sizes": dict(sorted(self.clean_record_jumps.items())),
                "records_set_by_a_dirty_step": self.record_set_by_dirty_step,
                "records_set_by_dirty_step_lemma":
                    "u_n = w_{n-1}/h_{n-1} and w_{n-1} <= (3/2)u_{n-1}, so h_{n-1} >= 2 "
                    "gives u_n <= (3/4)u_{n-1} <= running record: EVERY record in u is set "
                    "by a clean (h = 1) step.  A proof, confirmed here by the zero count.",
                "orbits_with_a_record_advance": self.orbits_with_record_advance,
                "max_record_jump_histogram": dict(sorted(self.max_record_jump_hist.items())),
                "orbits_whose_record_jumps_are_all_le_2": self.orbits_all_record_jumps_le2,
                "examples_all_record_jumps_le_2": self.examples_all_le2,
                "longest_record_climb_with_all_jumps_le_2": {
                    "records": self.longest_le2_climb[0],
                    "witness": self.longest_le2_climb[1]},
                "largest_total_climb_with_all_record_jumps_le_2": {
                    "climb_u_minus_u0": self.highest_le2_climb[0],
                    "witness": self.highest_le2_climb[1]},
                "orbits_reaching_u_ge_5_with_a_record_advance": self.orbits_reaching_u5,
                "of_those_with_a_record_jump_ge_3":
                    self.orbits_u5_with_clean_record_jump_ge3,
                "of_those_without": self.orbits_reaching_u5
                    - self.orbits_u5_with_clean_record_jump_ge3,
                "examples_without": self.orbits_u5_without,
                "r07_r08_note": "r07/r08 assert that bounded record jumps (<= 2) force "
                                "Sylvester, i.e. NO nonterminating orbit can climb with "
                                "record jumps <= 2.  Every orbit here terminates, so the "
                                "discriminating number is how FAR a <= 2 record climb can "
                                "run on real data before a >= 3 jump is forced: "
                                "'longest_record_climb_with_all_jumps_le_2' and "
                                "'highest_u_reached_with_all_jumps_le_2'.",
            },
            "experiment_2_prime_protection": {
                "prime_bound": self.prime_bound,
                "u_cap": self.u_cap_for_primes,
                "clean_rises_with_exact_v_n": self.prime_cov_have,
                "clean_rises_without_exact_v_n_modular_phase": self.prime_cov_missing,
                "by_rise_size": pbr,
                "protected_definition": "p^l || v_n with p <= 3u_n/2 is PROTECTED at this "
                                        "step when p^{l+1} > w_n = u_n - eps_n, i.e. r07's "
                                        "stated valuation-loss threshold cannot be met",
                "erasure_threshold_correction":
                    "r07 states the threshold as w >= p^{l+1}.  The dynamics gives a "
                    "different exponent for FULL erasure: v_{n+1} = a_n v_n / h_n with "
                    "h_n = gcd(w_n, a_n^2), so with k = v_p(a_n), v_p(h_n) = min(v_p(w_n), 2k); "
                    "v_p(v) drops at all only when k >= 1 and v_p(w_n) > k (so p^2 | w_n is "
                    "needed for ANY loss, matching r03), and drops by the full l only when "
                    "v_p(h_n) = k + l, forcing k >= l and v_p(w_n) >= 2l, i.e. p^{2l} | w_n. "
                    "The two criteria coincide at l = 1 and diverge for l >= 2, where the "
                    "correct protection bound p^{2l} > w is STRICTLY STRONGER than p^{l+1} > w. "
                    "Both counts are reported.",
                "unprotected_examples": self.unprotected_examples,
            },
            "experiment_3_long_orbit_error_profile": {
                "orbits_with_at_least_15_steps": self.long_orbits,
                "mean_abs_E_over_C": (self.long_absE_sum / self.long_absE_n
                                      if self.long_absE_n else None),
                "histogram_abs_E_over_C_twentieths_capped_at_0.5":
                    dict(sorted(self.long_absE_hist.items())),
                "random_model_mean_abs_E_over_C": 0.25,
                "examples": self.long_examples,
            },
        }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--qmax", type=int, default=1600)
    ap.add_argument("--long-orbit-samples", type=int, default=40000)
    ap.add_argument("--long-orbit-qbits", type=int, default=64)
    ap.add_argument("--prime-bound", type=int, default=800)
    ap.add_argument("--u-cap-primes", type=int, default=400)
    ap.add_argument("--exact-bits", type=int, default=40000)
    ap.add_argument("--step-cap", type=int, default=400)
    ap.add_argument("--height-mult", type=int, default=10 ** 5)
    ap.add_argument("--quick", action="store_true")
    ap.add_argument("--out", type=str, default="")
    args = ap.parse_args()
    if args.quick:
        args.qmax = 300
        args.long_orbit_samples = 2000
        args.exact_bits = 12000

    t0 = time.perf_counter()
    lab = Lab(args.prime_bound, args.u_cap_primes)
    for q in range(2, args.qmax + 1):
        for p in range(1, q):
            if gcd(p, q) != 1:
                continue
            orb = run_orbit(p, q, height_cap=max(10 ** 9, args.height_mult * p),
                            step_cap=args.step_cap, exact_bits=args.exact_bits,
                            lean=False)
            lab.ingest(p, q, orb)
    t_sweep = time.perf_counter() - t0

    # dedicated long-orbit harvest at large q (short orbits dominate the sweep)
    t0 = time.perf_counter()
    harvest = Lab(args.prime_bound, args.u_cap_primes)
    rng = random.Random(2026243)
    lo, hi = 1 << (args.long_orbit_qbits - 1), 1 << args.long_orbit_qbits
    kept = 0
    for _ in range(args.long_orbit_samples):
        q = rng.randrange(lo, hi)
        p = rng.randrange(1, q)
        g = gcd(p, q)
        p //= g
        q //= g
        orb = run_orbit(p, q, height_cap=max(10 ** 9, args.height_mult * p),
                        step_cap=args.step_cap, exact_bits=args.exact_bits,
                        lean=False)
        if len(orb["E"]) - 1 >= 15:
            kept += 1
            harvest.ingest(p, q, orb)
    t_harvest = time.perf_counter() - t0

    payload = {
        "probe_id": "erdos243_primitive_residue_lab",
        "quick": args.quick,
        "options": vars(args),
        "exact_identity_statements": {
            "A": "C_n * E_{n+1} = r_n^2 (mod C_{n+1}), r_n := D_n mod C_{n+1} "
                 "-- proof: D_{n+1} = D_n a_n, a_n C_n = D_n + C_{n+1}, so "
                 "C_n D_{n+1} = D_n(D_n + C_{n+1}) = D_n^2 (mod C_{n+1})",
            "B": "E_n * E_{n+1} = r_n^2 (mod C_{n+1}) -- from A and C_n = E_n (mod C_{n+1})",
            "C": "if gcd(C_n, C_{n+1}) = 1 then E_{n+1} = r_n^2 * C_n^{-1} (mod C_{n+1})",
            "unconditional": "A and B need NO coprimality; only C does",
        },
        "full_sweep": lab.report(),
        "long_orbit_harvest": {
            "sampled": args.long_orbit_samples,
            "q_bit_range": [args.long_orbit_qbits - 1, args.long_orbit_qbits],
            "kept_orbits_with_ge_15_steps": kept,
            **harvest.report(),
        },
        "timings": {"sweep_seconds": t_sweep, "harvest_seconds": t_harvest},
    }
    text = json.dumps(payload, indent=1, ensure_ascii=False, default=str)
    if args.out:
        Path(args.out).write_text(text + "\n")
        print(f"wrote {args.out} ({len(text)} bytes) "
              f"in {t_sweep + t_harvest:.1f}s")
    else:
        print(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
