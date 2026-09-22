import ErdosProblems.Erdos251.PaperCoreR7

namespace ErdosProblems.Erdos251.PaperCompleteR20

theorem nat_mul_rat_den (q : ℚ) (m : ℕ) :
    ((m : ℚ)*q).den = q.den / Nat.gcd m q.den := by
  rw [Rat.mul_den]
  simp only [Rat.den_natCast, Rat.num_natCast, one_mul, Int.natAbs_mul,
    Int.natAbs_natCast]
  rw [q.reduced.gcd_mul_right_cancel]

theorem two_pow_rat_den (q : ℚ) (s d N : ℕ)
    (hq : q.den = 2^s*d) (hd : Odd d) :
    ((2 : ℚ)^N*q).den = 2^(s-N)*d := by
  have hc : Nat.Coprime d (2^N) := hd.coprime_two_right.pow_right N
  have hg : Nat.gcd (2^N) (2^s*d) = Nat.gcd (2^N) (2^s) :=
    hc.gcd_mul_right_cancel_right (2^s)
  have hm := nat_mul_rat_den q (2^N)
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hm
  rw [hm, hq, hg]
  by_cases hNs : N ≤ s
  · rw [Nat.gcd_eq_left (pow_dvd_pow 2 hNs)]
    have he : 2^s = 2^(s-N)*2^N := by rw [← pow_add, Nat.sub_add_cancel hNs]
    rw [he]
    have hp : 0 < 2^N := by positivity
    rw [show 2^(s-N)*2^N*d = (2^(s-N)*d)*2^N by ring]
    exact Nat.mul_div_left _ hp
  · have hsN : s ≤ N := by omega
    rw [Nat.gcd_eq_right (pow_dvd_pow 2 hsN), Nat.sub_eq_zero_of_le hsN,
      pow_zero, one_mul]
    exact Nat.mul_div_right d (by positivity)

theorem rational_orbit_exact_den (g : ℕ → ℤ) (q : ℚ) (s d N : ℕ)
    (hq : q.den = 2^s*d) (hd : Odd d) :
    (rationalDyadicOrbit g q N).den = 2^(s-N)*d := by
  have h := tail_iterate_eq_pow_mul_sub_block (rationalDyadicOrbit_recurrence g q) 0 N
  simp only [zero_add, rationalDyadicOrbit] at h
  rw [h, Rat.sub_intCast_den]
  exact two_pow_rat_den q s d N hq hd

theorem two_part_divides_mersenne (s d N h : ℕ) (hh : 0 < h) :
    2^(s-N)*d ∣ 2^h-1 ↔ s ≤ N ∧ d ∣ 2^h-1 := by
  have hp : 0 < 2^h := by positivity
  have hm : (2^h-1)%2 = 1 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hh)
    have hz : 2^(k+1)%2=0 := by simp [pow_succ]
    omega
  constructor
  · intro hv
    have hs : s ≤ N := by
      by_contra hn
      have he : s-N ≠ 0 := by omega
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero he
      obtain ⟨c, hc⟩ := hv
      rw [hk, pow_succ] at hc
      rw [hc] at hm
      simp [Nat.mul_mod] at hm
    exact ⟨hs, by simpa [Nat.sub_eq_zero_of_le hs] using hv⟩
  · rintro ⟨hs, hv⟩
    simpa [Nat.sub_eq_zero_of_le hs] using hv

theorem real_orbit_exact_den_and_shift
    {g : ℕ → ℤ} {T : ℕ → ℝ} (hrec : RealDyadicTailRecurrence g T)
    (q : ℚ) (hq0 : T 0 = q) (s d : ℕ) (hq : q.den = 2^s*d) (hd : Odd d)
    (N h : ℕ) (hh : 0 < h) :
    (∃ v : ℚ, T N = v ∧ v.den = 2^(s-N)*d) ∧
    (RealIntegral (realTailShift T h N) ↔ s ≤ N ∧ d ∣ 2^h-1) := by
  have he := realTail_eq_ratCast_rationalDyadicOrbit hrec q hq0
  refine ⟨⟨rationalDyadicOrbit g q N, he N,
    rational_orbit_exact_den g q s d N hq hd⟩, ?_⟩
  have hi : RealIntegral (realTailShift T h N) ↔
      RatIntegral (tailShift (rationalDyadicOrbit g q) h N) := by
    simp only [RealIntegral, RatIntegral, realTailShift, tailShift, he]
    constructor <;> rintro ⟨z, hz⟩ <;> refine ⟨z, ?_⟩ <;> exact_mod_cast hz
  rw [hi, tailShift_integral_iff_den_dvd_mersenne (rationalDyadicOrbit_recurrence g q),
    rational_orbit_exact_den g q s d N hq hd]
  exact two_part_divides_mersenne s d N h hh

end ErdosProblems.Erdos251.PaperCompleteR20
#print axioms ErdosProblems.Erdos251.PaperCompleteR20.real_orbit_exact_den_and_shift
#print axioms ErdosProblems.Erdos251.PaperR7.rationality_classification
