import Erdos249257.TotientTailCarryPeriod
import Erdos249257.TotientCarryKernelRigidity
import ErdosProblems.Erdos249.ParityPerturbedRationalControl

/-! Paper-form restatement of `prop:D5cons` of the long #249 manuscript,
"The lower bound and a false proposed upper bound", including the clause the
earlier restatement left unstated: the `5/4` comparison sequence of
`sec:mahler-defect` is an explicit counterexample to the generic
rationality-driven carry-rank ceiling.

The environment asserts, in order:

(a) the canonical dyadic totient-kernel family is unconditionally
    `(2^e+1)`-dimensional at every level `e ≥ 1` (`prop:D4-inv`);

(b) rationality of `S` forces an associated tempered carry orbit with
    `ℚ`-rank at least `2^e - 1` at every level (`prop:CP-02`, `prop:rank`);

(c) hence any bound `g` applying to the actual carry under the hypothetical
    rationality of `S`, with `g e < 2^e - 1` at some level `e ≥ 1`, already
    contradicts the lower bound -- a bound merely growing with `e` need not;

(d) the generic assertion, for arbitrary rational coefficient series, is
    false: the `5/4` comparison sequence has an integer carry satisfying the
    growth condition and the same rank lower bound.

Clause (d) is what is proved here for the first time in paper form.  Its
witness is the centred base-four control sequence of `sec:mahler-defect`
(`ParityPerturbedRationalControl.control`): coefficients bounded by `n`,
equal to `φ` at every odd argument, within `2` of `φ` everywhere, binary
series exactly `5/4`, and a tempered integral carry whose canonical dyadic
sections have rank at least `2^e - 1` at every level.

The two sentences of the environment that are not propositions are left out:
the remark that the incompatible integer identity and the finite-shift
counterexample of `prop:B4b-kill` "remain separate counterexample results"
(a scope remark about other environments), and the evidence-label sentence.
Nothing below asserts a rank ceiling; `prop:D5cons` records that no such
ceiling follows from rationality and the listed coefficient hypotheses. -/

noncomputable section
namespace ErdosProblems.Erdos249.PaperCompleteR21

open Erdos249257
open Module

/-! ### The `5/4` comparison sequence and its carry -/

/-- **The `5/4` comparison sequence has the same rank lower bound**
(`prop:D5cons`, the counterexample clause; `sec:mahler-defect`).

The centred base-four construction `c(0)=0`, `c(2m-1)=φ(2m-1)`,
`c(2m)=φ(2m)+d_m` produces a coefficient sequence which

* satisfies the growth condition `c n ≤ n`;
* agrees with `φ` at every odd argument and lies within `2` of `φ` everywhere;
* has binary series exactly the rational number `5/4`;

and which therefore carries a tempered integral orbit `u` -- the exact
recurrence `u_{N+1} = 2u_N - v c(N+1)` together with `u_N / 2^N → 0` -- whose
canonical dyadic carry sections through level `e` have `ℚ`-rank at least
`2^e - 1` at every level `e`.  That is the very lower bound clause (b) derives
from rationality of `S`. -/
theorem fiveQuarter_comparison_rational_with_carryRank_floor :
    (∀ n : ℕ, ParityPerturbedRationalControl.control n ≤ n)
      ∧ (∀ n : ℕ, n % 2 = 1 →
          ParityPerturbedRationalControl.control n = Nat.totient n)
      ∧ (∀ n : ℕ,
          |(ParityPerturbedRationalControl.control n : ℤ) - Nat.totient n| ≤ 2)
      ∧ binaryCoeffSeries ParityPerturbedRationalControl.control = 5 / 4
      ∧ ¬ Irrational (binaryCoeffSeries ParityPerturbedRationalControl.control)
      ∧ ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
          IsTemperedBinaryOrbit ParityPerturbedRationalControl.control v u
            ∧ ∀ e : ℕ, 2 ^ e - 1 ≤
                finrank ℚ
                  (Submodule.span ℚ
                    (Set.range (canonicalCarryKernelFamily u e))) := by
  obtain ⟨v, hv, u, hu, hrank⟩ :=
    ParityPerturbedRationalControl.control_temperedOrbit_carryRank_unbounded
  exact ⟨ParityPerturbedRationalControl.control_le,
    fun _ hn => ParityPerturbedRationalControl.control_odd hn,
    ParityPerturbedRationalControl.abs_control_sub_totient_le,
    ParityPerturbedRationalControl.control_series,
    ParityPerturbedRationalControl.not_irrational_control,
    v, hv, u, hu, hrank⟩

/-- **The generic assertion is false** (`prop:D5cons`, the counterexample
clause, in refuting form).

No function `g` which falls strictly below `2^e - 1` at some level `e ≥ 1` can
bound the canonical carry-section ranks of every tempered orbit of every
coefficient sequence satisfying the growth condition `c n ≤ n` and having a
rational binary series.  The `5/4` comparison sequence is the witness.

This is the exact sense in which the proposed upper bound is false
*generically*: the hypotheses it would be deduced from -- the recurrence,
temperedness, the growth bound, and rationality of the series -- are all
satisfied by a sequence whose carry ranks already exceed the proposed
ceiling. -/
theorem no_generic_rationality_carryRank_ceiling :
    ¬ ∃ g : ℕ → ℕ,
        (∃ e : ℕ, 1 ≤ e ∧ g e < 2 ^ e - 1)
          ∧ ∀ (c : ℕ → ℕ) (v : ℕ) (u : ℕ → ℤ),
              (∀ n : ℕ, c n ≤ n) →
              ¬ Irrational (binaryCoeffSeries c) →
              0 < v →
              IsTemperedBinaryOrbit c v u →
              ∀ e : ℕ,
                finrank ℚ
                    (Submodule.span ℚ
                      (Set.range (canonicalCarryKernelFamily u e)))
                  ≤ g e := by
  rintro ⟨g, ⟨e, _he, hlt⟩, hbound⟩
  obtain ⟨v, hv, u, hu, hrank⟩ :=
    ParityPerturbedRationalControl.control_temperedOrbit_carryRank_unbounded
  have hup :=
    hbound ParityPerturbedRationalControl.control v u
      ParityPerturbedRationalControl.control_le
      ParityPerturbedRationalControl.not_irrational_control hv hu e
  have hlo := hrank e
  omega

/-! ### The whole environment -/

/-- **The lower bound and a false proposed upper bound** (`prop:D5cons`),
complete.

(a) the canonical dyadic totient-kernel family is unconditionally
`(2^e+1)`-dimensional at every level `e ≥ 1`;

(b) rationality of `S` forces an associated tempered carry orbit with
`ℚ`-rank at least `2^e-1` at every level;

(c) a bound `g` applying to the actual carry under the hypothetical
rationality of `S`, with `g e < 2^e-1` at some level `e ≥ 1`, would contradict
the lower bound and hence force irrationality; a bound that merely grows with
`e` need not contradict anything, and nothing here supplies such a `g`;

(d) the generic assertion for arbitrary rational coefficient series is false:
the `5/4` comparison sequence of `sec:mahler-defect` satisfies the growth
condition, has a rational binary series, and has an integer carry with the
same `2^e-1` rank lower bound, so no ceiling below `2^e-1` holds generically. -/
theorem rank_floor_and_false_proposed_carryRank_ceiling :
    (∀ e : ℕ, 1 ≤ e →
        finrank ℚ
            (Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e)))
          = 2 ^ e + 1)
      ∧ (¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) →
          ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
            IsTemperedBinaryOrbit Nat.totient v u
              ∧ ∀ e : ℕ, 2 ^ e - 1 ≤
                  finrank ℚ
                    (Submodule.span ℚ
                      (Set.range (canonicalCarryKernelFamily u e))))
      ∧ (∀ g : ℕ → ℕ,
          (∀ v : ℕ, ∀ u : ℕ → ℤ, 0 < v →
              IsTemperedBinaryOrbit Nat.totient v u →
              ∀ e : ℕ,
                finrank ℚ
                    (Submodule.span ℚ
                      (Set.range (canonicalCarryKernelFamily u e)))
                  ≤ g e) →
          (∃ e : ℕ, 1 ≤ e ∧ g e < 2 ^ e - 1) →
          Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))
      ∧ ((∀ n : ℕ, ParityPerturbedRationalControl.control n ≤ n)
          ∧ binaryCoeffSeries ParityPerturbedRationalControl.control = 5 / 4
          ∧ ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
              IsTemperedBinaryOrbit ParityPerturbedRationalControl.control v u
                ∧ ∀ e : ℕ, 2 ^ e - 1 ≤
                    finrank ℚ
                      (Submodule.span ℚ
                        (Set.range (canonicalCarryKernelFamily u e))))
      ∧ ¬ ∃ g : ℕ → ℕ,
          (∃ e : ℕ, 1 ≤ e ∧ g e < 2 ^ e - 1)
            ∧ ∀ (c : ℕ → ℕ) (v : ℕ) (u : ℕ → ℤ),
                (∀ n : ℕ, c n ≤ n) →
                ¬ Irrational (binaryCoeffSeries c) →
                0 < v →
                IsTemperedBinaryOrbit c v u →
                ∀ e : ℕ,
                  finrank ℚ
                      (Submodule.span ℚ
                        (Set.range (canonicalCarryKernelFamily u e)))
                    ≤ g e := by
  refine ⟨fun e he => finrank_totientKernelThroughLevelFamily_eq e he, ?_, ?_, ?_,
    no_generic_rationality_carryRank_ceiling⟩
  · intro hrat
    refine not_irrational_totientSeries_implies_unbounded_carryRank_unconditional ?_
    rwa [binaryCoeffSeries_totient_eq]
  · intro g hg hex
    obtain ⟨e, _he, hlt⟩ := hex
    by_contra hnot
    obtain ⟨v, hv, u, hu, hrank⟩ :=
      not_irrational_totientSeries_implies_unbounded_carryRank_unconditional
        (by rwa [binaryCoeffSeries_totient_eq])
    have h1 := hrank e
    have h2 := hg v u hv hu e
    omega
  · obtain ⟨hle, _hodd, _habs, hseries, _hnotirr, hcarry⟩ :=
      fiveQuarter_comparison_rational_with_carryRank_floor
    exact ⟨hle, hseries, hcarry⟩

#print axioms fiveQuarter_comparison_rational_with_carryRank_floor
#print axioms no_generic_rationality_carryRank_ceiling
#print axioms rank_floor_and_false_proposed_carryRank_ceiling

end ErdosProblems.Erdos249.PaperCompleteR21
