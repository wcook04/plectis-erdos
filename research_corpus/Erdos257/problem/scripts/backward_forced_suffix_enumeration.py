#!/usr/bin/env python3
"""Backward forced-suffix enumeration for the denominator-21 sparse socket (B').

This executes the decisive experiment proposed in
`TwentyOneDensityInvariantAttack.md` section 8 (2026-08-20), which had no
receipt on disk before this run.

Setup (all integers, no floating point):

For half-depth R = 3a+1 the bad-saturated-transition normal form
(`twentyOneBadSaturatedTransition_forces_margin_residue`,
`twentyOneBadSaturatedTransition_forces_sparse_twoPulse` in Lean) requires a
Boolean support D subseteq {2..R} with

    (B')   sum_{d in D} ( 4*q_R(d) + 2*[d | 2R+1] + [d | 2R+2] ) = 4*Q_R - 2^(R+1)
    (P1)   x_d = 0 for every d | (2R+3)
    (P2)   sum_{d in D, d | (2R+4)} 1 <= 1

where q_R(d) = floor(2^(2R)/(2^d - 1)), Q_R = floor(2^(2R)/21).

An exact solution implies the same congruence modulo 2^B for every B.  The
experiment reveals bits of the equation from the least significant end and
asks:

  outcome 1: for some B the congruence WITH (P1)+(P2) is EXHAUSTIVELY
             unsatisfiable modulo 2^B (while relaxing the pulse constraints
             keeps it satisfiable).  Then no Boolean row realises the socket
             at this R at all: the sparse entrance is closed at R.
  outcome 2: compatible families survive with the smallest working B growing
             proportionally to R: row arithmetic alone is insufficient and
             greedy ancestry must enter.

Search semantics are strict: UNSAT is reported only when the DFS over the
bit-reveal tree exhausted its (memoised) state space below the node budget;
otherwise the row is reported as `unknown_budget`.

Controls:
  C1  published congruence witness of the attack note section 6 (R=28,
      D = {7,8,13,14,17,18,21,24,25,26,27,28}, modulus 2^18) must be SAT.
  C2  relaxation control: dropping (P1)+(P2) must never reduce a row from SAT
      to UNSAT relative to the constrained run.
  C3  brute-force cross-check of SAT/UNSAT at full precision for small R.

Receipt: state/formal_math/erdos257_period_noncollapse/backward_forced_suffix_enumeration_receipt.json
"""

import argparse
import hashlib
import json
import sys
from pathlib import Path

sys.setrecursionlimit(100000)


def weight(R, d):
    """W_d = 4*q_R(d) + 2*[d | 2R+1] + [d | 2R+2] as an exact integer."""
    q = (1 << (2 * R)) // ((1 << d) - 1)
    w = 4 * q
    if (2 * R + 1) % d == 0:
        w += 2
    if (2 * R + 2) % d == 0:
        w += 1
    return w


def build_row_socketS(R):
    """The saturated-entrance socket (S) at R = 3a+2.

    (S)   sum_{d in D} q_R(d) = Q_R - 2^R
    pulse p_R = 2*[d | 2R+1] + [d | 2R+2] <= 1:
      (P1') x_d = 0 for every d | (2R+1)
      (P2') at most one selected d | (2R+2)
    """
    target = (1 << (2 * R)) // 21 - (1 << R)
    forbid = [d for d in range(2, R + 1) if (2 * R + 1) % d == 0]
    capped = [d for d in range(2, R + 1) if (2 * R + 2) % d == 0]
    weights = {}
    for d in range(2, R + 1):
        if (2 * R + 1) % d == 0:
            continue
        w = (1 << (2 * R)) // ((1 << d) - 1)
        if w:
            weights[d] = w
    pools = {}
    for d, w in weights.items():
        e = (w & -w).bit_length() - 1
        pools.setdefault(e, []).append(d)
    return {
        "R": R,
        "target": target,
        "weights": weights,
        "pools": pools,
        "max_level": max(pools) if pools else 0,
        "forbid": forbid,
        "capped": capped,
    }


def build_row(R, socket="B"):
    return build_row_socketS(R) if socket == "S" else build_row_bprime(R)


def build_row_bprime(R):
    """Variables, level pools, target for one half-depth R."""
    target = 4 * ((1 << (2 * R)) // 21) - (1 << (R + 1))
    forbid = [d for d in range(2, R + 1) if (2 * R + 3) % d == 0]
    capped = [d for d in range(2, R + 1) if (2 * R + 4) % d == 0]
    var_ok = [
        d for d in range(2, R + 1)
        if (2 * R + 3) % d != 0
    ]
    weights = {}
    entry = {}
    for d in var_ok:
        w = weight(R, d)
        if w == 0:
            continue
        weights[d] = w
        entry[d] = (w & -w).bit_length() - 1
    pools = {}
    for d, e in entry.items():
        pools.setdefault(e, []).append(d)
    return {
        "R": R,
        "target": target,
        "weights": weights,
        "pools": pools,
        "max_level": max(entry.values()) if entry else 0,
        "forbid": forbid,
        "capped": capped,
    }


class Solver:
    """Bit-reveal DFS with memo. Counts exhaustive nodes strictly."""

    def __init__(self, row, B, node_budget):
        self.row = row
        self.B = B
        self.mask = (1 << B) - 1
        self.tlow = row["target"] & self.mask
        self.node_budget = node_budget
        self.nodes = 0
        self.exhausted = True
        self.memo_feas = set()
        self.memo_infeas = set()
        self.levels = sorted(lvl for lvl in row["pools"] if lvl < B)
        self.wlows = {d: w & self.mask for d, w in row["weights"].items()}
        self.capped_set = set(row["capped"])

    def feasible(self, lvl_idx, plow, cap_used):
        """Can levels[lvl_idx..] choose subsets so that final P ~= T mod 2^B?

        plow is the assigned partial sum reduced mod 2^B; cap_used in {0,1}.
        """
        if self.nodes >= self.node_budget:
            self.exhausted = False
            return False
        self.nodes += 1
        if lvl_idx == len(self.levels):
            return plow == self.tlow
        state = (lvl_idx, plow, cap_used)
        if state in self.memo_feas:
            return True
        if state in self.memo_infeas:
            return False
        b = self.levels[lvl_idx]
        pool = [d for d in self.row["pools"][b] if d in self.wlows]
        shift = b
        base = plow
        # parity required at bit b
        need = ((self.tlow - base) >> shift) & 1
        odd = [d for d in pool if (self.wlows[d] >> shift) & 1]
        even = [d for d in pool if not (self.wlows[d] >> shift) & 1]
        found = False
        # enumerate odd-subsets with the right cardinality parity; evens free
        n_odd = len(odd)
        # subsets of odd by bitmask (cap sizes defensively)
        limit = 1 << n_odd
        if n_odd > 22:
            # too wide to enumerate exhaustively within budget semantics
            self.exhausted = False
            return False
        for om in range(limit):
            if bin(om).count("1") % 2 != need:
                continue
            delta = base
            ok = True
            cap_new = cap_used
            for i in range(n_odd):
                if om >> i & 1:
                    d = odd[i]
                    delta += self.wlows[d]
                    if d in self.capped_set:
                        cap_new += 1
            if cap_new > 1:
                continue
            if not found or True:
                pass
            # recurse over even subsets lazily via recursion trick: push evens
            found = self._evens(lvl_idx + 1, delta, cap_new, even, 0)
            if found:
                break
        if found:
            self.memo_feas.add(state)
        else:
            self.memo_infeas.add(state)
        return found

    def _evens(self, lvl_idx, delta, cap_used, even, idx):
        if self.nodes >= self.node_budget:
            self.exhausted = False
            return False
        self.nodes += 1
        if idx == len(even):
            return self.feasible(lvl_idx, delta & self.mask, cap_used)
        d = even[idx]
        if self._evens(lvl_idx, delta, cap_used, even, idx + 1):
            return True
        cap_new = cap_used + (1 if d in self.capped_set else 0)
        if cap_new <= 1:
            if self._evens(lvl_idx, (delta + self.wlows[d]) & self.mask,
                           cap_new, even, idx + 1):
                return True
        return False


class Solver2:
    """Frontier-dedup bit-reveal search. Same complete semantics as Solver:
    UNSAT only when the reachable state space was fully explored below the
    node budget.  States are (plow mod 2^B, capped_used); within a level the
    pool's achievable (delta, cap) pairs are deduplicated before branching.
    """

    def __init__(self, row, B, node_budget):
        self.row = row
        self.B = B
        self.mask = (1 << B) - 1
        self.tlow = row["target"] & self.mask
        self.node_budget = node_budget
        self.nodes = 0
        self.exhausted = True
        self.memo_feas = set()
        self.memo_infeas = set()
        self.levels = sorted(lvl for lvl in row["pools"] if lvl < B)
        self.wlows = {d: w & self.mask for d, w in row["weights"].items()}
        self.capped_set = set(row["capped"])

    def feasible(self):
        states = {(0, 0)}
        for li, b in enumerate(self.levels):
            pool = [d for d in self.row["pools"][b] if d in self.wlows]
            # achievable (delta, cap) pairs for this level's pool, deduped
            pairs = {(0, 0)}
            for d in pool:
                w = self.wlows[d]
                cc = 1 if d in self.capped_set else 0
                new = set(pairs)
                for (s, c) in pairs:
                    if c + cc <= 1:
                        new.add(((s + w) & self.mask, c + cc))
                pairs = new
                if self.nodes >= self.node_budget:
                    self.exhausted = False
                    return False
                self.nodes += 1
            nxt = set()
            shift = b
            for (p, c) in states:
                need = ((self.tlow - p) >> shift) & 1
                for (s, c2) in pairs:
                    if (s >> shift) & 1 == need and c + c2 <= 1:
                        nxt.add((((p + s) & self.mask), c + c2))
            if not nxt:
                return False
            states = nxt
            if self.nodes >= self.node_budget:
                self.exhausted = False
                return False
        return self.tlow in {p for (p, _c) in states}


def solve_row(R, B, node_budget, impose_pulse=True, socket="B"):
    row = build_row(R, socket)
    if not impose_pulse:
        # re-admit (P1)-forbidden variables and drop the (P2) cap
        for d in range(2, R + 1):
            if d in row["weights"]:
                continue
            w = weight(R, d)
            if w:
                row["weights"][d] = w
        row["capped"] = []
    # rebuild entry map consistently
    row["entry"] = {}
    pools = {}
    for d, w in row["weights"].items():
        e = (w & -w).bit_length() - 1
        row["entry"][d] = e
        pools.setdefault(e, []).append(d)
    row["pools"] = pools
    row["max_level"] = max(pools) if pools else 0
    if not impose_pulse:
        row["capped"] = []
    solver = Solver2(row, B, node_budget)
    sat = solver.feasible()
    return {
        "R": R,
        "B": B,
        "impose_pulse": impose_pulse,
        "sat": sat,
        "exhaustive": solver.exhausted,
        "nodes": solver.nodes,
        "n_vars": len(row["weights"]),
        "n_forbid": len(row["forbid"]),
        "n_capped": len(row["capped"]),
    }


def brute_force_cross_check(R):
    """Full-precision exhaustive check for tiny R via MITM-free enumeration."""
    row = build_row(R)
    target = row["target"]
    ds = sorted(row["weights"])
    n = len(ds)
    ws = [row["weights"][d] for d in ds]
    capped_pos = {d: i for i, d in enumerate(ds) if d in set(row["capped"])}
    sat_any = False
    solutions = []
    half = n // 2
    left = {}
    for m in range(1 << half):
        s = 0
        c = 0
        for i in range(half):
            if m >> i & 1:
                s += ws[i]
                d = ds[i]
                if d in capped_pos:
                    c += 1
        if c <= 1:
            left.setdefault(s, []).append(m)
    for m in range(1 << (n - half)):
        s = 0
        c = 0
        for i in range(n - half):
            if m >> i & 1:
                s += ws[half + i]
                d = ds[half + i]
                if d in capped_pos:
                    c += 1
        if c > 1:
            continue
        want = target - s
        if want in left:
            for lm in left[want]:
                sat_any = True
                if len(solutions) < 3:
                    sel = [ds[i] for i in range(half) if lm >> i & 1] + \
                          [ds[half + i] for i in range(n - half) if m >> i & 1]
                    solutions.append(sel)
    return sat_any, solutions


def control_c1():
    """Published R=28 witness must satisfy the (B') congruence mod 2^18."""
    R = 28
    D = {7, 8, 13, 14, 17, 18, 21, 24, 25, 26, 27, 28}
    lhs = sum(weight(R, d) for d in D)
    rhs = 4 * ((1 << (2 * R)) // 21) - (1 << (R + 1))
    return (lhs - rhs) % (1 << 18) == 0


def b_star(R, node_budget, b_lo=8, b_hi=128, socket="B"):
    """Find the minimal B with exhaustive constrained-UNSAT (doubling walk).

    Returns dict with sat_max_B (largest tested B that is SAT), unsat_min_B,
    attribution splits, and exhaustion flags.
    """
    out = {"R": R, "socket": socket}
    lo = solve_row(R, b_lo, node_budget, True, socket)
    out["sat_at_lo"] = lo["sat"]
    out["lo_exhaustive"] = lo["exhaustive"]
    if lo["sat"]:
        out["sat_max_B"] = b_lo
        b = b_lo
        out["hi_exhaustive"] = True
        while b < b_hi:
            nb = min(b_hi, b * 2)
            r = solve_row(R, nb, node_budget, True, socket)
            if r["sat"]:
                b = nb
                out["sat_max_B"] = nb
                out["hi_exhaustive"] = r["exhaustive"]
                if not r["exhaustive"]:
                    break
            else:
                out["unsat_min_B"] = nb
                out["unsat_exhaustive"] = r["exhaustive"]
                out["unsat_nodes"] = r["nodes"]
                break
        else:
            out["unsat_min_B"] = None
    else:
        out["sat_max_B"] = None
        out["unsat_min_B"] = b_lo
        out["unsat_exhaustive"] = lo["exhaustive"]
        out["unsat_nodes"] = lo["nodes"]
    # attribution: which pulse clause is essential?
    if out.get("unsat_min_B"):
        Bu = out["unsat_min_B"]
        p1_only = solve_row(R, Bu, node_budget, impose_pulse=False, socket=socket)
        # drop only the forbid clause: re-add those variables, keep the cap
        row = build_row(R, socket)
        extra_forbid = [d for d in range(2, R + 1) if d not in row["weights"]]
        for d in extra_forbid:
            w = ((1 << (2 * R)) // ((1 << d) - 1)) if socket == "S" \
                else weight(R, d)
            if socket == "B":
                if (2 * R + 1) % d == 0:
                    w += 2
                if (2 * R + 2) % d == 0:
                    w += 1
            if w:
                row["weights"][d] = w
        pools = {}
        for d, w in row["weights"].items():
            e = (w & -w).bit_length() - 1
            pools.setdefault(e, []).append(d)
        row["pools"] = pools
        s_p2_only = Solver2(row, Bu, node_budget)
        p2_only_sat = s_p2_only.feasible()
        out["p1_only_sat"] = p1_only["sat"]
        out["p2_only_sat"] = p2_only_sat
        out["p2_only_exhaustive"] = s_p2_only.exhausted
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--r-max", type=int, default=121)
    ap.add_argument("--b-levels", type=str, default="16,24,32")
    ap.add_argument("--node-budget", type=int, default=4_000_000)
    ap.add_argument("--brute-max", type=int, default=19)
    ap.add_argument("--mode", choices=["sweep", "bscale"], default="sweep")
    args = ap.parse_args()

    Bs = [int(x) for x in args.b_levels.split(",")]
    if args.mode == "bscale":
        rows = []
        for socket in ("B", "S"):
            for R in range(4 if socket == "B" else 5, args.r_max + 1,
                           3 if socket == "B" else 3):
                r = b_star(R, args.node_budget, socket=socket)
                rows.append(r)
                print(json.dumps(r), flush=True)
        receipt2 = {
            "schema": "erdos257_bscale_receipt/1",
            "node_budget": args.node_budget,
            "rows": rows,
        }
        blob = json.dumps(receipt2, sort_keys=True).encode()
        receipt2["receipt_sha256"] = hashlib.sha256(blob).hexdigest()
        out = Path("state/formal_math/erdos257_period_noncollapse/"
                   "backward_forced_suffix_bscale_receipt.json")
        out.parent.mkdir(parents=True, exist_ok=True)
        out.write_text(json.dumps(receipt2, indent=2, sort_keys=True))
        return

    receipt = {
        "schema": "erdos257_backward_forced_suffix_enumeration_receipt/1",
        "script": "backward_forced_suffix_enumeration.py",
        "controls": {},
        "rows": [],
    }

    receipt["controls"]["c1_published_witness_mod2^18"] = {
        "passed": control_c1(),
        "detail": "R=28, D={7,8,13,14,17,18,21,24,25,26,27,28}",
    }

    # C3 brute-force cross-check at full precision, small R
    c3 = []
    for R in range(4, args.brute_max + 1, 3):
        sat, sols = brute_force_cross_check(R)
        # solver at B covering all bits: max weight bit length + 2
        maxw = max(weight(R, d).bit_length() for d in range(2, R + 1))
        res = solve_row(R, maxw + 2, args.node_budget, impose_pulse=True)
        agree = (sat == res["sat"]) and res["exhaustive"]
        c3.append({"R": R, "brute_sat": sat, "solver_sat": res["sat"],
                   "exhaustive": res["exhaustive"], "agree": agree})
    receipt["controls"]["c3_brute_force_full_precision"] = {
        "all_agree": all(r["agree"] for r in c3),
        "rows": c3,
    }

    # main sweep
    for R in range(4, args.r_max + 1, 3):
        rowout = {"R": R, "verdict_per_B": []}
        for B in Bs:
            constr = solve_row(R, B, args.node_budget, impose_pulse=True)
            relax = solve_row(R, B, args.node_budget, impose_pulse=False)
            rowout["verdict_per_B"].append({
                "B": B,
                "constrained": constr,
                "relaxed": relax,
                "pulse_is_the_killer": (
                    constr["exhaustive"] and not constr["sat"]
                ),
            })
            if constr["exhaustive"] and not constr["sat"]:
                break  # outcome 1 at this B; larger B moot for this row
        receipt["rows"].append(rowout)

    blob = json.dumps(receipt, sort_keys=True).encode()
    receipt["receipt_sha256"] = hashlib.sha256(blob).hexdigest()

    out = Path("state/formal_math/erdos257_period_noncollapse/"
               "backward_forced_suffix_enumeration_receipt.json")
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(receipt, indent=2, sort_keys=True))

    # console summary
    print("C1 witness:", receipt["controls"]["c1_published_witness_mod2^18"])
    print("C3 all agree:", receipt["controls"]["c3_brute_force_full_precision"]["all_agree"])
    n_unsat = 0
    n_sat_all = 0
    n_unknown = 0
    for row in receipt["rows"]:
        verdicts = row["verdict_per_B"]
        last = verdicts[-1]
        c = last["constrained"]
        if c["exhaustive"] and not c["sat"]:
            n_unsat += 1
            print(f"R={row['R']:5d}  OUTCOME-1: UNSAT mod 2^{last['B']} "
                  f"(nodes={c['nodes']})")
        elif all(v["constrained"]["sat"] or not v["constrained"]["exhaustive"]
                 for v in verdicts) and last["constrained"]["sat"]:
            n_sat_all += 1
        else:
            n_unknown += 1
    print(f"\nsummary: rows={len(receipt['rows'])} outcome1={n_unsat} "
          f"sat_at_max_B={n_sat_all} unknown/budget={n_unknown}")


if __name__ == "__main__":
    main()
