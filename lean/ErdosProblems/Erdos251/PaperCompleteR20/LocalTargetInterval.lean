import ErdosProblems.Erdos251.SparsePaperR11

noncomputable section
open Filter Topology Finset
namespace ErdosProblems.Erdos251.PaperCompleteR20
open PaperR8.SparseSchedule PaperR9.SparseAmbient

theorem generated_upperTail_le_majorant (f : ℕ → ℝ) (start K : ℕ)
    (hready : Ready f start 0) (hK : K ≤ start) :
    upperTail f start 0 ≤ ∑' n : ℕ, (((n+K : ℕ) : ℝ)+1)/2^(n+K+1) := by
  let e : ℕ → ℕ := fun j => centre f start j - K
  have hlow : ∀ j, K ≤ centre f start j := fun j =>
    hK.trans ((centre_strictMono f start).monotone (Nat.zero_le j))
  have hinj : Function.Injective e := by
    intro i j hij
    apply (centre_strictMono f start).injective
    dsimp [e] at hij
    have := hlow i
    have := hlow j
    omega
  have hs := (summable_nat_add_iff K).mpr linear_weight_summable
  have hb : ∀ j, upperTerm f start j ≤
      (((e j + K : ℕ) : ℝ)+1)/2^(e j+K+1) := by
    intro j
    have he : e j+K = centre f start j := Nat.sub_add_cancel (hlow j)
    rw [he]
    have hc : (capacity f start j : ℝ) ≤ (centre f start j : ℝ)+1 := by
      exact_mod_cast (capacity_budget f start hready j).2
    calc
      _ ≤ (capacity f start j : ℝ)*weight f start j := (term_order f start j).2.2
      _ ≤ _ := by
        simpa only [weight, mul_one_div] using
          div_le_div_of_nonneg_right hc (by positivity : (0 : ℝ) ≤ 2^(centre f start j+1))
  have h := Summable.tsum_le_tsum_of_inj e hinj (fun n hn => by positivity)
    hb (terms_summable f start hready).2.1 hs
  simpa only [upperTail, Nat.add_zero] using h

theorem local_target_interval (a : ℕ → ℕ) {A η : ℝ}
    (ha : HasSum (fun n => (a n : ℝ)/2^(n+1)) A)
    (f : ℕ → ℝ) (hf : Tendsto f atTop atTop) (K : ℕ) (hη : 0 < η) :
    ∃ start : ℕ, ∃ l u : ℝ, ∃ Nq : ℕ → ℕ,
      (Set.range (centre f start) ⊆ Set.Ici K) ∧
      UpperBanachZero (Set.range (centre f start)) ∧
      A < l ∧ l < u ∧ u < A+η ∧
      ∀ r : ℝ, l ≤ r → r ≤ u → ∃ e : ℕ → ℕ,
        (∀ n, e n ≠ 0 → n ∈ Set.range (centre f start)) ∧
        (∀ n < K, a n+e n = a n) ∧
        (∀ᶠ n in atTop, (e n : ℝ) ≤ f n) ∧
        (∀ q : ℕ, 0 < q → ∀ n, Nq q ≤ n →
          q ∣ e n ∧ q ∣ ∑ i ∈ range n, e i) ∧
        HasSum (fun n => ((a n+e n : ℕ) : ℝ)/2^(n+1)) r := by
  have ht := tendsto_sum_nat_add (fun n : ℕ => ((n : ℝ)+1)/2^(n+1))
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (ht.eventually (gt_mem_nhds hη))
  let K' := max K J
  obtain ⟨start, hs, hr, hSK, hSZ, hb⟩ := exists_sparse_budgeted_support f hf K'
  have hu : upperTail f start 0 < η :=
    (generated_upperTail_le_majorant f start K' hr hs).trans_lt (hJ K' (le_max_right _ _))
  refine ⟨start, A+lowerTail f start 0, A+upperTail f start 0,
    congruenceCutoff f hf start, ?_, hSZ, ?_, ?_, by linarith, ?_⟩
  · intro n hn
    exact (le_max_left K J).trans (hSK hn)
  · linarith [lowerTail_positive f start hr]
  · linarith [generated_interval_nonempty f start hr]
  · intro r hl hu
    obtain ⟨e, heS, hef, heq, hes⟩ := generated_ambient_filling_uniform f hf start hr
      (y := r-A) (by linarith) (by linarith)
    refine ⟨e, heS, ?_, hef, heq, ?_⟩
    · intro n hn
      have hz : e n = 0 := by
        by_contra hne
        have hh : K' ≤ n := hSK (heS n hne)
        have hk : K ≤ K' := le_max_left _ _
        exact (not_le_of_gt hn) (hk.trans hh)
      simp [hz]
    · have hh := ha.add hes
      rw [show A+(r-A)=r by ring] at hh
      convert hh using 1
      funext n
      rw [Nat.cast_add, add_div]

end ErdosProblems.Erdos251.PaperCompleteR20
#print axioms ErdosProblems.Erdos251.PaperCompleteR20.local_target_interval
