import Mathlib.Tactic

/-!
# Rationality caps the socket runs of its own support, in terms of the carry

`CertificateSocketCollapse.md` section 46 caps socket runs by **parity**:
`maxrun ≤ maxgap(Odd_A) - 1`, where `Odd_A = {m : τ_A(m) odd}`.  This module records the
complementary cap, which comes from **rationality** and lands in the carry coordinate.

## The setting

Erdős's 1948 socket mechanism forces `2^k ∣ τ_A(N+k)` for `k = 1, …, K`.  Each such head
term `τ_A(N+k) · 2^(-k)` is then an integer, so it drops out of the fractional part:

`frac(2^N y) = frac(Σ_{k>K} τ_A(N+k) 2^(-k)) ≤ Σ_{k>K} τ_A(N+k) 2^(-k) = S / 2^K`,

where `S := Σ_{j≥1} τ_A(N+K+j) 2^(-j)` is exactly the **local divisor mass** whose floor is
the corpus's forward carry, `C_m = ⌊S_m⌋` (`RunLengthMarginLawAndDivisorMultiplicity.md`
sections 3 and 11).  So `S < C + 1`.

If moreover `y = p/q` in lowest terms with `q` odd, then `frac(2^N y) = (2^N p mod q)/q` is a
multiple of `1/q`, hence **either it vanishes or it is at least `1/q`**.  Combining the two
bounds gives the cap proved below.

## What this says

> A socket run of length `K` at `N`, on a support whose value is `p/q`, forces
> `2^K < q · (C_{N+K} + 1)`.

Equivalently `K < log₂ q + log₂(C + 1)`: **the rational denominator and the carry together
bound how long any socket run can be.**  So the Erdős-1948 lane and the carry lane are not
independent — rationality couples them.  Contrapositive, and this is the producer shape:
*any support exhibiting socket runs longer than `log₂(q(C+1))` cannot sum to `p/q`.*

Measured on the corpus's candidates (`scripts/socket_run_rational_cap.py`): zero violations
across 15,612 socket runs on the five non-dyadic candidates `1/21, 4/9, 1/5, 5/12, 1/465`,
with tightest observed slack `q(C+1)/2^K = 1.25`.  The cap is tight, not vacuous.  `1/2` is
dyadic, so `frac(2^N y) = 0` for every `N ≥ 1` and the criterion is vacuous there — which is
why Erdős's criterion always excludes the dyadic case.

## Scope

Everything below is the abstract inequality: the mathematical content, with the divisor
theory left in prose, exactly as `PrimeSlackTwoValued.lean` does for section 84.  It is a
**necessary condition on a counterexample, not a producer**, until someone forces long socket
runs on a candidate support.
-/

namespace ErdosProblems.Erdos257

namespace SocketRunRationalCap

/-- A socket head term is an integer: if `2 ^ k ∣ t` then `t / 2 ^ k` is a natural. This is
why the first `K` terms drop out of the fractional part. -/
theorem socketHead_integral {t k : ℕ} (h : 2 ^ k ∣ t) :
    ∃ z : ℕ, (t : ℚ) / 2 ^ k = (z : ℚ) := by
  obtain ⟨z, rfl⟩ := h
  refine ⟨z, ?_⟩
  have h2 : ((2 : ℚ) ^ k) ≠ 0 := by positivity
  push_cast
  field_simp

/-- **The rational socket cap.** If the fractional part `f` is a nonzero multiple of `1 / q`
(so `1 / q ≤ f`), the socket run of length `K` bounds it by `S / 2 ^ K`, and `S` is below the
carry successor `C + 1`, then `2 ^ K < q * (C + 1)`. -/
theorem socketRun_cap_of_rational {q K C : ℕ} {f S : ℚ} (hq : 0 < q)
    (hf_lo : (1 : ℚ) / q ≤ f) (hf_hi : f ≤ S / 2 ^ K) (hS : S < (C : ℚ) + 1) :
    (2 : ℚ) ^ K < (q : ℚ) * ((C : ℚ) + 1) := by
  have hq' : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
  have hpow : (0 : ℚ) < (2 : ℚ) ^ K := by positivity
  have h1 : (1 : ℚ) / (q : ℚ) ≤ S / 2 ^ K := le_trans hf_lo hf_hi
  rw [div_le_div_iff₀ hq' hpow] at h1
  -- h1 : 1 * 2 ^ K ≤ S * q
  nlinarith [h1, hS, hq', hpow]

/-- Natural-number form of the cap, which is how the census checks it. -/
theorem socketRun_cap_nat {q K C : ℕ} {f S : ℚ} (hq : 0 < q)
    (hf_lo : (1 : ℚ) / q ≤ f) (hf_hi : f ≤ S / 2 ^ K) (hS : S < (C : ℚ) + 1) :
    2 ^ K < q * (C + 1) := by
  have h := socketRun_cap_of_rational hq hf_lo hf_hi hS
  exact_mod_cast h

/-- The contrapositive, stated as the producer: a support exhibiting a socket run too long
for the cap cannot have fractional part bounded below by `1 / q`, i.e. cannot sum to a
rational with denominator `q` unless that fractional part vanishes. -/
theorem no_rational_of_long_socketRun {q K C : ℕ} {f S : ℚ} (hq : 0 < q)
    (hf_hi : f ≤ S / 2 ^ K) (hS : S < (C : ℚ) + 1)
    (hlong : q * (C + 1) ≤ 2 ^ K) : f < 1 / (q : ℚ) := by
  by_contra hcon
  push_neg at hcon
  have h := socketRun_cap_nat hq hcon hf_hi hS
  omega

#print axioms socketHead_integral
#print axioms socketRun_cap_of_rational
#print axioms socketRun_cap_nat
#print axioms no_rational_of_long_socketRun

end SocketRunRationalCap

end ErdosProblems.Erdos257
