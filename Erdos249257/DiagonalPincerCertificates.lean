import Erdos249257.LcmDiagonalReduction
import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.LucasPrimality

/-!
# Finite diagonal-pincer certificates

This generated module materializes the kernel-safe prefix of finite
`certifiedKill (periodLcm t) (periodLcm t) L_min` rows in the imported
pincer table: 12 distinct scales through `t = 17`. Prime factors are proved prime in Lean,
the factorizations are multiplied back exactly, and Euler totients are
reconstructed from pairwise-coprime prime-power blocks.  No
`native_decide`, custom axiom, or unbounded-supply inference is used.

Results input SHA-256: `1114b667b8d044a97240d031dce4dcfd093d6ea93cef78086a05572c667416dd`.
Factorization input SHA-256: `4a0c5360a08c34381c932692f66a2094178ff2dfec7302788caed8e6ee3fdf3d`.
-/

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

abbrev FactorBlock := ℕ × ℕ

def factorBlockValue (b : FactorBlock) : ℕ := b.1 ^ b.2

def factorBlockTotient (b : FactorBlock) : ℕ := b.1 ^ (b.2 - 1) * (b.1 - 1)

/-- Square-and-multiply exponentiation, used to keep Lucas certificates logarithmic. -/
def binaryPow {α : Type*} [Monoid α] (a : α) : (n : ℕ) → α
  | 0 => 1
  | n + 1 =>
      let x := binaryPow a ((n + 1) / 2)
      if (n + 1) % 2 = 0 then x * x else x * x * a
termination_by n => n
decreasing_by omega

theorem binaryPow_eq_pow {α : Type*} [Monoid α] (a : α) :
    ∀ n : ℕ, binaryPow a n = a ^ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | n
      · simp [binaryPow]
      · rw [binaryPow]
        split_ifs with hmod
        · rw [ih ((n + 1) / 2) (by omega), ← pow_add]
          congr 1
          omega
        · have hmod' : (n + 1) % 2 = 1 := by omega
          rw [ih ((n + 1) / 2) (by omega), ← pow_add, ← pow_succ]
          congr 1
          omega

/-- The same square-and-multiply chain with explicit natural remainders. -/
def binaryPowMod (a m : ℕ) : (n : ℕ) → ℕ
  | 0 => 1 % m
  | n + 1 =>
      let x := binaryPowMod a m ((n + 1) / 2)
      if (n + 1) % 2 = 0 then x * x % m else x * x % m * a % m
termination_by n => n
decreasing_by omega

theorem binaryPow_natCast (a m n : ℕ) :
    binaryPow (a : ZMod m) n = (binaryPowMod a m n : ZMod m) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | n
      · simp [binaryPow, binaryPowMod, ZMod.natCast_mod]
      · rw [binaryPow, binaryPowMod, ih ((n + 1) / 2) (by omega)]
        split_ifs <;> simp [ZMod.natCast_mod]

theorem binaryPow_zmod {m : ℕ} [NeZero m] (a : ZMod m) (n : ℕ) :
    binaryPow a n = (binaryPowMod a.val m n : ZMod m) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val a]
  exact binaryPow_natCast a.val m n

/-- A checked prime-power factor list computes Euler's totient exactly. -/
theorem totient_factorBlocks (bs : List FactorBlock)
    (hprime : ∀ b ∈ bs, Nat.Prime b.1)
    (hpos : ∀ b ∈ bs, 0 < b.2)
    (hpair : bs.Pairwise (Function.onFun Nat.Coprime factorBlockValue)) :
    Nat.totient ((bs.map factorBlockValue).prod) =
      (bs.map factorBlockTotient).prod := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
      have hp : Nat.Prime b.1 := hprime b (by simp)
      have he : 0 < b.2 := hpos b (by simp)
      have hpair' := (List.pairwise_cons.mp hpair).2
      have hcop : Nat.Coprime (factorBlockValue b) ((bs.map factorBlockValue).prod) := by
        rw [Nat.coprime_list_prod_right_iff]
        rintro n hn
        obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hn
        exact (List.pairwise_cons.mp hpair).1 c hc
      rw [List.map_cons, List.prod_cons, Nat.totient_mul hcop,
        ih (fun c hc => hprime c (by simp [hc]))
          (fun c hc => hpos c (by simp [hc])) hpair']
      rw [show Nat.totient (factorBlockValue b) = factorBlockTotient b by
        simpa [factorBlockValue, factorBlockTotient] using Nat.totient_prime_pow hp he]
      simp only [List.map_cons, List.prod_cons]

/-- A prime divisor of a product of checked prime powers is one of their bases. -/
theorem prime_dvd_factorBlocks {q : ℕ} (bs : List FactorBlock)
    (hq : Nat.Prime q) (hprime : ∀ b ∈ bs, Nat.Prime b.1)
    (hdvd : q ∣ (bs.map factorBlockValue).prod) :
    ∃ b ∈ bs, q = b.1 := by
  induction bs with
  | nil =>
      simp only [List.map_nil, List.prod_nil] at hdvd
      have hqle : q ≤ 1 := Nat.le_of_dvd (by decide) hdvd
      exact (not_le_of_gt hq.one_lt hqle).elim
  | cons b bs ih =>
      rw [List.map_cons, List.prod_cons] at hdvd
      rcases (hq.dvd_mul.mp hdvd) with hhead | htail
      · have hbase : q ∣ b.1 := hq.dvd_of_dvd_pow hhead
        exact ⟨b, by simp, (Nat.prime_dvd_prime_iff_eq hq (hprime b (by simp))).mp hbase⟩
      · obtain ⟨c, hc, heq⟩ := ih (fun c hc => hprime c (by simp [hc])) htail
        exact ⟨c, by simp [hc], heq⟩

/-! ## Kernel-checked primality leaves -/

private theorem prime_2 : Nat.Prime 2 := by norm_num
private theorem prime_3 : Nat.Prime 3 := by norm_num
private theorem prime_5 : Nat.Prime 5 := by norm_num
private theorem prime_7 : Nat.Prime 7 := by norm_num
private theorem prime_11 : Nat.Prime 11 := by norm_num
private theorem prime_13 : Nat.Prime 13 := by norm_num
private theorem prime_17 : Nat.Prime 17 := by norm_num
private theorem prime_19 : Nat.Prime 19 := by norm_num
private theorem prime_23 : Nat.Prime 23 := by norm_num
private theorem prime_29 : Nat.Prime 29 := by norm_num
private theorem prime_31 : Nat.Prime 31 := by norm_num
private theorem prime_37 : Nat.Prime 37 := by norm_num
private theorem prime_41 : Nat.Prime 41 := by norm_num
private theorem prime_43 : Nat.Prime 43 := by norm_num
private theorem prime_47 : Nat.Prime 47 := by norm_num
private theorem prime_53 : Nat.Prime 53 := by norm_num
private theorem prime_59 : Nat.Prime 59 := by norm_num
private theorem prime_61 : Nat.Prime 61 := by norm_num
private theorem prime_67 : Nat.Prime 67 := by norm_num
private theorem prime_71 : Nat.Prime 71 := by norm_num
private theorem prime_73 : Nat.Prime 73 := by norm_num
private theorem prime_79 : Nat.Prime 79 := by norm_num
private theorem prime_83 : Nat.Prime 83 := by norm_num
private theorem prime_89 : Nat.Prime 89 := by norm_num
private theorem prime_97 : Nat.Prime 97 := by norm_num
private theorem prime_101 : Nat.Prime 101 := by norm_num
private theorem prime_103 : Nat.Prime 103 := by norm_num
private theorem prime_107 : Nat.Prime 107 := by norm_num
private theorem prime_109 : Nat.Prime 109 := by norm_num
private theorem prime_113 : Nat.Prime 113 := by norm_num
private theorem prime_127 : Nat.Prime 127 := by norm_num
private theorem prime_131 : Nat.Prime 131 := by norm_num
private theorem prime_137 : Nat.Prime 137 := by norm_num
private theorem prime_139 : Nat.Prime 139 := by norm_num
private theorem prime_149 : Nat.Prime 149 := by norm_num
private theorem prime_151 : Nat.Prime 151 := by norm_num
private theorem prime_163 : Nat.Prime 163 := by norm_num
private theorem prime_167 : Nat.Prime 167 := by norm_num
private theorem prime_181 : Nat.Prime 181 := by norm_num
private theorem prime_197 : Nat.Prime 197 := by norm_num
private theorem prime_211 : Nat.Prime 211 := by norm_num
private theorem prime_223 : Nat.Prime 223 := by norm_num
private theorem prime_227 : Nat.Prime 227 := by norm_num
private theorem prime_233 : Nat.Prime 233 := by norm_num
private theorem prime_239 : Nat.Prime 239 := by norm_num
private theorem prime_241 : Nat.Prime 241 := by norm_num
private theorem prime_263 : Nat.Prime 263 := by norm_num
private theorem prime_271 : Nat.Prime 271 := by norm_num
private theorem prime_277 : Nat.Prime 277 := by norm_num
private theorem prime_281 : Nat.Prime 281 := by norm_num
private theorem prime_283 : Nat.Prime 283 := by norm_num
private theorem prime_337 : Nat.Prime 337 := by norm_num
private theorem prime_421 : Nat.Prime 421 := by norm_num
private theorem prime_431 : Nat.Prime 431 := by norm_num
private theorem prime_433 : Nat.Prime 433 := by norm_num
private theorem prime_487 : Nat.Prime 487 := by norm_num
private theorem prime_509 : Nat.Prime 509 := by norm_num
private theorem prime_547 : Nat.Prime 547 := by norm_num
private theorem prime_557 : Nat.Prime 557 := by norm_num
private theorem prime_563 : Nat.Prime 563 := by norm_num
private theorem prime_599 : Nat.Prime 599 := by norm_num
private theorem prime_631 : Nat.Prime 631 := by norm_num
private theorem prime_647 : Nat.Prime 647 := by norm_num
private theorem prime_739 : Nat.Prime 739 := by norm_num
private theorem prime_827 : Nat.Prime 827 := by norm_num
private theorem prime_853 : Nat.Prime 853 := by norm_num
private theorem prime_857 : Nat.Prime 857 := by norm_num
private theorem prime_953 : Nat.Prime 953 := by norm_num
private theorem prime_1009 : Nat.Prime 1009 := by norm_num
private theorem prime_1097 : Nat.Prime 1097 := by norm_num
private theorem prime_1109 : Nat.Prime 1109 := by norm_num
private theorem prime_1301 : Nat.Prime 1301 := by norm_num
private theorem prime_1321 : Nat.Prime 1321 := by norm_num
private theorem prime_1429 : Nat.Prime 1429 := by norm_num
private theorem prime_1451 : Nat.Prime 1451 := by norm_num
private theorem prime_1459 : Nat.Prime 1459 := by norm_num
private theorem prime_1483 : Nat.Prime 1483 := by norm_num
private theorem prime_1579 : Nat.Prime 1579 := by norm_num
private theorem prime_1693 : Nat.Prime 1693 := by norm_num
private theorem prime_1723 : Nat.Prime 1723 := by norm_num
private theorem prime_1733 : Nat.Prime 1733 := by norm_num
private theorem prime_1789 : Nat.Prime 1789 := by norm_num
private theorem prime_1871 : Nat.Prime 1871 := by norm_num
private theorem prime_2111 : Nat.Prime 2111 := by norm_num
private theorem prime_2311 : Nat.Prime 2311 := by norm_num
private theorem prime_2377 : Nat.Prime 2377 := by norm_num
private theorem prime_2411 : Nat.Prime 2411 := by norm_num
private theorem prime_2521 : Nat.Prime 2521 := by norm_num
private theorem prime_2531 : Nat.Prime 2531 := by norm_num
private theorem prime_2857 : Nat.Prime 2857 := by norm_num
private theorem prime_3329 : Nat.Prime 3329 := by norm_num
private theorem prime_3467 : Nat.Prime 3467 := by norm_num
private theorem prime_3533 : Nat.Prime 3533 := by norm_num
private theorem prime_3697 : Nat.Prime 3697 := by norm_num
private theorem prime_3719 : Nat.Prime 3719 := by norm_num
private theorem prime_3917 : Nat.Prime 3917 := by norm_num
private theorem prime_4049 : Nat.Prime 4049 := by norm_num
private theorem prime_4051 : Nat.Prime 4051 := by norm_num
private theorem prime_4241 : Nat.Prime 4241 := by norm_num
private theorem prime_4397 : Nat.Prime 4397 := by norm_num
private theorem prime_4621 : Nat.Prime 4621 := by norm_num
private theorem prime_4903 : Nat.Prime 4903 := by norm_num
private theorem prime_5051 : Nat.Prime 5051 := by norm_num
private theorem prime_5407 : Nat.Prime 5407 := by norm_num
private theorem prime_5419 : Nat.Prime 5419 := by norm_num
private theorem prime_5573 : Nat.Prime 5573 := by norm_num
private theorem prime_5641 : Nat.Prime 5641 := by norm_num
private theorem prime_7237 : Nat.Prime 7237 := by norm_num
private theorem prime_9241 : Nat.Prime 9241 := by norm_num
private theorem prime_9857 : Nat.Prime 9857 := by norm_num
private theorem prime_9941 : Nat.Prime 9941 := by norm_num
private theorem prime_10151 : Nat.Prime 10151 := by norm_num
private theorem prime_10223 : Nat.Prime 10223 := by norm_num
private theorem prime_12113 : Nat.Prime 12113 := by norm_num
private theorem prime_16381 : Nat.Prime 16381 := by norm_num
private theorem prime_17579 : Nat.Prime 17579 := by norm_num
private theorem prime_18481 : Nat.Prime 18481 := by norm_num
private theorem prime_20021 : Nat.Prime 20021 := by norm_num
private theorem prime_23227 : Nat.Prime 23227 := by norm_num
private theorem prime_23977 : Nat.Prime 23977 := by norm_num
private theorem prime_25367 : Nat.Prime 25367 := by norm_num
private theorem prime_25741 : Nat.Prime 25741 := by norm_num
private theorem prime_27197 : Nat.Prime 27197 := by norm_num
private theorem prime_27733 : Nat.Prime 27733 := by norm_num
private theorem prime_27737 : Nat.Prime 27737 := by norm_num
private theorem prime_27739 : Nat.Prime 27739 := by norm_num
private theorem prime_35617 : Nat.Prime 35617 := by norm_num
private theorem prime_36037 : Nat.Prime 36037 := by norm_num
private theorem prime_48049 : Nat.Prime 48049 := by norm_num
private theorem prime_49009 : Nat.Prime 49009 := by norm_num
private theorem prime_51481 : Nat.Prime 51481 := by norm_num
private theorem prime_55441 : Nat.Prime 55441 := by norm_num
private theorem prime_55457 : Nat.Prime 55457 := by norm_num
private theorem prime_65521 : Nat.Prime 65521 := by norm_num
private theorem prime_72073 : Nat.Prime 72073 := by norm_num
private theorem prime_96097 : Nat.Prime 96097 := by norm_num
private theorem prime_110881 : Nat.Prime 110881 := by norm_num
private theorem prime_120121 : Nat.Prime 120121 := by norm_num
private theorem prime_128971 : Nat.Prime 128971 := by norm_num
private theorem prime_130343 : Nat.Prime 130343 := by norm_num
private theorem prime_131041 : Nat.Prime 131041 := by norm_num
private theorem prime_180181 : Nat.Prime 180181 := by norm_num
private theorem prime_382883 : Nat.Prime 382883 := by norm_num
private theorem prime_471241 : Nat.Prime 471241 := by norm_num
private theorem prime_612613 : Nat.Prime 612613 := by norm_num
private theorem prime_680681 : Nat.Prime 680681 := by norm_num
private theorem prime_720743 : Nat.Prime 720743 := by norm_num
private theorem prime_816817 : Nat.Prime 816817 := by norm_num
private theorem prime_1441459 : Nat.Prime 1441459 := by norm_num
private theorem prime_1441463 : Nat.Prime 1441463 := by norm_num
private theorem prime_1633633 : Nat.Prime 1633633 := by norm_num
private theorem prime_2450453 : Nat.Prime 2450453 := by norm_num
private theorem prime_4084081 : Nat.Prime 4084081 := by norm_num
private theorem prime_8168161 : Nat.Prime 8168161 := by norm_num
private theorem prime_12252259 : Nat.Prime 12252259 := by norm_num
private theorem prime_12252263 : Nat.Prime 12252263 := by norm_num
private theorem prime_24504503 : Nat.Prime 24504503 := by norm_num

/-! ## Exact totients used by the finite windows -/

private theorem phi_2 : Nat.totient 2 = 1 := by
  rw [← show ((([(2, 1)] : List FactorBlock).map factorBlockValue).prod) = 2 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_3 : Nat.totient 3 = 2 := by
  rw [← show ((([(3, 1)] : List FactorBlock).map factorBlockValue).prod) = 3 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_3]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_4 : Nat.totient 4 = 2 := by
  rw [← show ((([(2, 2)] : List FactorBlock).map factorBlockValue).prod) = 4 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_5 : Nat.totient 5 = 4 := by
  rw [← show ((([(5, 1)] : List FactorBlock).map factorBlockValue).prod) = 5 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_5]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_6 : Nat.totient 6 = 2 := by
  rw [← show ((([(2, 1), (3, 1)] : List FactorBlock).map factorBlockValue).prod) = 6 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_3]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_7 : Nat.totient 7 = 6 := by
  rw [← show ((([(7, 1)] : List FactorBlock).map factorBlockValue).prod) = 7 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_7]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_8 : Nat.totient 8 = 4 := by
  rw [← show ((([(2, 3)] : List FactorBlock).map factorBlockValue).prod) = 8 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_9 : Nat.totient 9 = 6 := by
  rw [← show ((([(3, 2)] : List FactorBlock).map factorBlockValue).prod) = 9 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_3]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_10 : Nat.totient 10 = 4 := by
  rw [← show ((([(2, 1), (5, 1)] : List FactorBlock).map factorBlockValue).prod) = 10 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_5]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_11 : Nat.totient 11 = 10 := by
  rw [← show ((([(11, 1)] : List FactorBlock).map factorBlockValue).prod) = 11 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_11]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_12 : Nat.totient 12 = 4 := by
  rw [← show ((([(2, 2), (3, 1)] : List FactorBlock).map factorBlockValue).prod) = 12 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_3]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_13 : Nat.totient 13 = 12 := by
  rw [← show ((([(13, 1)] : List FactorBlock).map factorBlockValue).prod) = 13 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_13]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_14 : Nat.totient 14 = 6 := by
  rw [← show ((([(2, 1), (7, 1)] : List FactorBlock).map factorBlockValue).prod) = 14 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_7]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_15 : Nat.totient 15 = 8 := by
  rw [← show ((([(3, 1), (5, 1)] : List FactorBlock).map factorBlockValue).prod) = 15 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_3, prime_5]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_16 : Nat.totient 16 = 8 := by
  rw [← show ((([(2, 4)] : List FactorBlock).map factorBlockValue).prod) = 16 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_17 : Nat.totient 17 = 16 := by
  rw [← show ((([(17, 1)] : List FactorBlock).map factorBlockValue).prod) = 17 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_17]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_18 : Nat.totient 18 = 6 := by
  rw [← show ((([(2, 1), (3, 2)] : List FactorBlock).map factorBlockValue).prod) = 18 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_3]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_19 : Nat.totient 19 = 18 := by
  rw [← show ((([(19, 1)] : List FactorBlock).map factorBlockValue).prod) = 19 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_19]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_25 : Nat.totient 25 = 20 := by
  rw [← show ((([(5, 2)] : List FactorBlock).map factorBlockValue).prod) = 25 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_5]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_26 : Nat.totient 26 = 12 := by
  rw [← show ((([(2, 1), (13, 1)] : List FactorBlock).map factorBlockValue).prod) = 26 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_13]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_27 : Nat.totient 27 = 18 := by
  rw [← show ((([(3, 3)] : List FactorBlock).map factorBlockValue).prod) = 27 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_3]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_28 : Nat.totient 28 = 12 := by
  rw [← show ((([(2, 2), (7, 1)] : List FactorBlock).map factorBlockValue).prod) = 28 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_7]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_29 : Nat.totient 29 = 28 := by
  rw [← show ((([(29, 1)] : List FactorBlock).map factorBlockValue).prod) = 29 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_29]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_30 : Nat.totient 30 = 8 := by
  rw [← show ((([(2, 1), (3, 1), (5, 1)] : List FactorBlock).map factorBlockValue).prod) = 30 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_3, prime_5]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_31 : Nat.totient 31 = 30 := by
  rw [← show ((([(31, 1)] : List FactorBlock).map factorBlockValue).prod) = 31 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_31]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_61 : Nat.totient 61 = 60 := by
  rw [← show ((([(61, 1)] : List FactorBlock).map factorBlockValue).prod) = 61 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_62 : Nat.totient 62 = 30 := by
  rw [← show ((([(2, 1), (31, 1)] : List FactorBlock).map factorBlockValue).prod) = 62 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_31]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_63 : Nat.totient 63 = 36 := by
  rw [← show ((([(3, 2), (7, 1)] : List FactorBlock).map factorBlockValue).prod) = 63 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_3, prime_7]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_64 : Nat.totient 64 = 32 := by
  rw [← show ((([(2, 6)] : List FactorBlock).map factorBlockValue).prod) = 64 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_65 : Nat.totient 65 = 48 := by
  rw [← show ((([(5, 1), (13, 1)] : List FactorBlock).map factorBlockValue).prod) = 65 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_5, prime_13]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_66 : Nat.totient 66 = 20 := by
  rw [← show ((([(2, 1), (3, 1), (11, 1)] : List FactorBlock).map factorBlockValue).prod) = 66 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_3, prime_11]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_67 : Nat.totient 67 = 66 := by
  rw [← show ((([(67, 1)] : List FactorBlock).map factorBlockValue).prod) = 67 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_67]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_68 : Nat.totient 68 = 32 := by
  rw [← show ((([(2, 2), (17, 1)] : List FactorBlock).map factorBlockValue).prod) = 68 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_17]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_69 : Nat.totient 69 = 44 := by
  rw [← show ((([(3, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod) = 69 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_3, prime_23]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_121 : Nat.totient 121 = 110 := by
  rw [← show ((([(11, 2)] : List FactorBlock).map factorBlockValue).prod) = 121 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_11]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_122 : Nat.totient 122 = 60 := by
  rw [← show ((([(2, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 122 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_123 : Nat.totient 123 = 80 := by
  rw [← show ((([(3, 1), (41, 1)] : List FactorBlock).map factorBlockValue).prod) = 123 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_3, prime_41]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_124 : Nat.totient 124 = 60 := by
  rw [← show ((([(2, 2), (31, 1)] : List FactorBlock).map factorBlockValue).prod) = 124 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_31]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_125 : Nat.totient 125 = 100 := by
  rw [← show ((([(5, 3)] : List FactorBlock).map factorBlockValue).prod) = 125 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_5]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_126 : Nat.totient 126 = 36 := by
  rw [← show ((([(2, 1), (3, 2), (7, 1)] : List FactorBlock).map factorBlockValue).prod) = 126 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_3, prime_7]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_127 : Nat.totient 127 = 126 := by
  rw [← show ((([(127, 1)] : List FactorBlock).map factorBlockValue).prod) = 127 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_127]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_128 : Nat.totient 128 = 64 := by
  rw [← show ((([(2, 7)] : List FactorBlock).map factorBlockValue).prod) = 128 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_129 : Nat.totient 129 = 84 := by
  rw [← show ((([(3, 1), (43, 1)] : List FactorBlock).map factorBlockValue).prod) = 129 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_3, prime_43]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_421 : Nat.totient 421 = 420 := by
  rw [← show ((([(421, 1)] : List FactorBlock).map factorBlockValue).prod) = 421 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_421]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_422 : Nat.totient 422 = 210 := by
  rw [← show ((([(2, 1), (211, 1)] : List FactorBlock).map factorBlockValue).prod) = 422 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_211]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_423 : Nat.totient 423 = 276 := by
  rw [← show ((([(3, 2), (47, 1)] : List FactorBlock).map factorBlockValue).prod) = 423 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_3, prime_47]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_424 : Nat.totient 424 = 208 := by
  rw [← show ((([(2, 3), (53, 1)] : List FactorBlock).map factorBlockValue).prod) = 424 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_53]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_425 : Nat.totient 425 = 320 := by
  rw [← show ((([(5, 2), (17, 1)] : List FactorBlock).map factorBlockValue).prod) = 425 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_5, prime_17]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_426 : Nat.totient 426 = 140 := by
  rw [← show ((([(2, 1), (3, 1), (71, 1)] : List FactorBlock).map factorBlockValue).prod) = 426 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_3, prime_71]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_427 : Nat.totient 427 = 360 := by
  rw [← show ((([(7, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 427 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_7, prime_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_428 : Nat.totient 428 = 212 := by
  rw [← show ((([(2, 2), (107, 1)] : List FactorBlock).map factorBlockValue).prod) = 428 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_107]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_429 : Nat.totient 429 = 240 := by
  rw [← show ((([(3, 1), (11, 1), (13, 1)] : List FactorBlock).map factorBlockValue).prod) = 429 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_3, prime_11, prime_13]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_430 : Nat.totient 430 = 168 := by
  rw [← show ((([(2, 1), (5, 1), (43, 1)] : List FactorBlock).map factorBlockValue).prod) = 430 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_5, prime_43]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_431 : Nat.totient 431 = 430 := by
  rw [← show ((([(431, 1)] : List FactorBlock).map factorBlockValue).prod) = 431 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_432 : Nat.totient 432 = 144 := by
  rw [← show ((([(2, 4), (3, 3)] : List FactorBlock).map factorBlockValue).prod) = 432 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_3]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_433 : Nat.totient 433 = 432 := by
  rw [← show ((([(433, 1)] : List FactorBlock).map factorBlockValue).prod) = 433 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_433]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_434 : Nat.totient 434 = 180 := by
  rw [← show ((([(2, 1), (7, 1), (31, 1)] : List FactorBlock).map factorBlockValue).prod) = 434 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_7, prime_31]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_841 : Nat.totient 841 = 812 := by
  rw [← show ((([(29, 2)] : List FactorBlock).map factorBlockValue).prod) = 841 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_29]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_842 : Nat.totient 842 = 420 := by
  rw [← show ((([(2, 1), (421, 1)] : List FactorBlock).map factorBlockValue).prod) = 842 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_421]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_843 : Nat.totient 843 = 560 := by
  rw [← show ((([(3, 1), (281, 1)] : List FactorBlock).map factorBlockValue).prod) = 843 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_3, prime_281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_844 : Nat.totient 844 = 420 := by
  rw [← show ((([(2, 2), (211, 1)] : List FactorBlock).map factorBlockValue).prod) = 844 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_211]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_845 : Nat.totient 845 = 624 := by
  rw [← show ((([(5, 1), (13, 2)] : List FactorBlock).map factorBlockValue).prod) = 845 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_5, prime_13]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_846 : Nat.totient 846 = 276 := by
  rw [← show ((([(2, 1), (3, 2), (47, 1)] : List FactorBlock).map factorBlockValue).prod) = 846 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_3, prime_47]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_847 : Nat.totient 847 = 660 := by
  rw [← show ((([(7, 1), (11, 2)] : List FactorBlock).map factorBlockValue).prod) = 847 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_7, prime_11]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_848 : Nat.totient 848 = 416 := by
  rw [← show ((([(2, 4), (53, 1)] : List FactorBlock).map factorBlockValue).prod) = 848 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_53]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_849 : Nat.totient 849 = 564 := by
  rw [← show ((([(3, 1), (283, 1)] : List FactorBlock).map factorBlockValue).prod) = 849 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_3, prime_283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_850 : Nat.totient 850 = 320 := by
  rw [← show ((([(2, 1), (5, 2), (17, 1)] : List FactorBlock).map factorBlockValue).prod) = 850 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_5, prime_17]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_851 : Nat.totient 851 = 792 := by
  rw [← show ((([(23, 1), (37, 1)] : List FactorBlock).map factorBlockValue).prod) = 851 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_23, prime_37]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_852 : Nat.totient 852 = 280 := by
  rw [← show ((([(2, 2), (3, 1), (71, 1)] : List FactorBlock).map factorBlockValue).prod) = 852 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_3, prime_71]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_853 : Nat.totient 853 = 852 := by
  rw [← show ((([(853, 1)] : List FactorBlock).map factorBlockValue).prod) = 853 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_853]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_854 : Nat.totient 854 = 360 := by
  rw [← show ((([(2, 1), (7, 1), (61, 1)] : List FactorBlock).map factorBlockValue).prod) = 854 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_7, prime_61]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_855 : Nat.totient 855 = 432 := by
  rw [← show ((([(3, 2), (5, 1), (19, 1)] : List FactorBlock).map factorBlockValue).prod) = 855 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_3, prime_5, prime_19]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_1681 : Nat.totient 1681 = 1640 := by
  rw [← show ((([(41, 2)] : List FactorBlock).map factorBlockValue).prod) = 1681 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_41]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_1682 : Nat.totient 1682 = 812 := by
  rw [← show ((([(2, 1), (29, 2)] : List FactorBlock).map factorBlockValue).prod) = 1682 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_29]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_1683 : Nat.totient 1683 = 960 := by
  rw [← show ((([(3, 2), (11, 1), (17, 1)] : List FactorBlock).map factorBlockValue).prod) = 1683 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_3, prime_11, prime_17]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_1684 : Nat.totient 1684 = 840 := by
  rw [← show ((([(2, 2), (421, 1)] : List FactorBlock).map factorBlockValue).prod) = 1684 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_421]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_1685 : Nat.totient 1685 = 1344 := by
  rw [← show ((([(5, 1), (337, 1)] : List FactorBlock).map factorBlockValue).prod) = 1685 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_5, prime_337]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_1686 : Nat.totient 1686 = 560 := by
  rw [← show ((([(2, 1), (3, 1), (281, 1)] : List FactorBlock).map factorBlockValue).prod) = 1686 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_3, prime_281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_1687 : Nat.totient 1687 = 1440 := by
  rw [← show ((([(7, 1), (241, 1)] : List FactorBlock).map factorBlockValue).prod) = 1687 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_7, prime_241]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_1688 : Nat.totient 1688 = 840 := by
  rw [← show ((([(2, 3), (211, 1)] : List FactorBlock).map factorBlockValue).prod) = 1688 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_211]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_1689 : Nat.totient 1689 = 1124 := by
  rw [← show ((([(3, 1), (563, 1)] : List FactorBlock).map factorBlockValue).prod) = 1689 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_3, prime_563]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_1690 : Nat.totient 1690 = 624 := by
  rw [← show ((([(2, 1), (5, 1), (13, 2)] : List FactorBlock).map factorBlockValue).prod) = 1690 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_5, prime_13]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_1691 : Nat.totient 1691 = 1584 := by
  rw [← show ((([(19, 1), (89, 1)] : List FactorBlock).map factorBlockValue).prod) = 1691 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_19, prime_89]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_1692 : Nat.totient 1692 = 552 := by
  rw [← show ((([(2, 2), (3, 2), (47, 1)] : List FactorBlock).map factorBlockValue).prod) = 1692 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_3, prime_47]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_1693 : Nat.totient 1693 = 1692 := by
  rw [← show ((([(1693, 1)] : List FactorBlock).map factorBlockValue).prod) = 1693 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_1693]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_1694 : Nat.totient 1694 = 660 := by
  rw [← show ((([(2, 1), (7, 1), (11, 2)] : List FactorBlock).map factorBlockValue).prod) = 1694 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_7, prime_11]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_1695 : Nat.totient 1695 = 896 := by
  rw [← show ((([(3, 1), (5, 1), (113, 1)] : List FactorBlock).map factorBlockValue).prod) = 1695 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_3, prime_5, prime_113]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_2521 : Nat.totient 2521 = 2520 := by
  rw [← show ((([(2521, 1)] : List FactorBlock).map factorBlockValue).prod) = 2521 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2521]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_2522 : Nat.totient 2522 = 1152 := by
  rw [← show ((([(2, 1), (13, 1), (97, 1)] : List FactorBlock).map factorBlockValue).prod) = 2522 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_13, prime_97]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_2523 : Nat.totient 2523 = 1624 := by
  rw [← show ((([(3, 1), (29, 2)] : List FactorBlock).map factorBlockValue).prod) = 2523 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_3, prime_29]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_2524 : Nat.totient 2524 = 1260 := by
  rw [← show ((([(2, 2), (631, 1)] : List FactorBlock).map factorBlockValue).prod) = 2524 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_631]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_2525 : Nat.totient 2525 = 2000 := by
  rw [← show ((([(5, 2), (101, 1)] : List FactorBlock).map factorBlockValue).prod) = 2525 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_5, prime_101]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_2526 : Nat.totient 2526 = 840 := by
  rw [← show ((([(2, 1), (3, 1), (421, 1)] : List FactorBlock).map factorBlockValue).prod) = 2526 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_3, prime_421]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_2527 : Nat.totient 2527 = 2052 := by
  rw [← show ((([(7, 1), (19, 2)] : List FactorBlock).map factorBlockValue).prod) = 2527 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_7, prime_19]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_2528 : Nat.totient 2528 = 1248 := by
  rw [← show ((([(2, 5), (79, 1)] : List FactorBlock).map factorBlockValue).prod) = 2528 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_79]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_2529 : Nat.totient 2529 = 1680 := by
  rw [← show ((([(3, 2), (281, 1)] : List FactorBlock).map factorBlockValue).prod) = 2529 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_3, prime_281]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_2530 : Nat.totient 2530 = 880 := by
  rw [← show ((([(2, 1), (5, 1), (11, 1), (23, 1)] : List FactorBlock).map factorBlockValue).prod) = 2530 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_5, prime_11, prime_23]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_2531 : Nat.totient 2531 = 2530 := by
  rw [← show ((([(2531, 1)] : List FactorBlock).map factorBlockValue).prod) = 2531 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2531]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_2532 : Nat.totient 2532 = 840 := by
  rw [← show ((([(2, 2), (3, 1), (211, 1)] : List FactorBlock).map factorBlockValue).prod) = 2532 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_3, prime_211]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_2533 : Nat.totient 2533 = 2368 := by
  rw [← show ((([(17, 1), (149, 1)] : List FactorBlock).map factorBlockValue).prod) = 2533 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_17, prime_149]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_2534 : Nat.totient 2534 = 1080 := by
  rw [← show ((([(2, 1), (7, 1), (181, 1)] : List FactorBlock).map factorBlockValue).prod) = 2534 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_7, prime_181]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_5041 : Nat.totient 5041 = 4970 := by
  rw [← show ((([(71, 2)] : List FactorBlock).map factorBlockValue).prod) = 5041 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_71]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_5042 : Nat.totient 5042 = 2520 := by
  rw [← show ((([(2, 1), (2521, 1)] : List FactorBlock).map factorBlockValue).prod) = 5042 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_2521]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_5043 : Nat.totient 5043 = 3280 := by
  rw [← show ((([(3, 1), (41, 2)] : List FactorBlock).map factorBlockValue).prod) = 5043 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_3, prime_41]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_5044 : Nat.totient 5044 = 2304 := by
  rw [← show ((([(2, 2), (13, 1), (97, 1)] : List FactorBlock).map factorBlockValue).prod) = 5044 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_13, prime_97]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_5045 : Nat.totient 5045 = 4032 := by
  rw [← show ((([(5, 1), (1009, 1)] : List FactorBlock).map factorBlockValue).prod) = 5045 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_5, prime_1009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_5046 : Nat.totient 5046 = 1624 := by
  rw [← show ((([(2, 1), (3, 1), (29, 2)] : List FactorBlock).map factorBlockValue).prod) = 5046 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_3, prime_29]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_5047 : Nat.totient 5047 = 4284 := by
  rw [← show ((([(7, 2), (103, 1)] : List FactorBlock).map factorBlockValue).prod) = 5047 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_7, prime_103]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_5048 : Nat.totient 5048 = 2520 := by
  rw [← show ((([(2, 3), (631, 1)] : List FactorBlock).map factorBlockValue).prod) = 5048 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_631]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_5049 : Nat.totient 5049 = 2880 := by
  rw [← show ((([(3, 3), (11, 1), (17, 1)] : List FactorBlock).map factorBlockValue).prod) = 5049 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_3, prime_11, prime_17]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_5050 : Nat.totient 5050 = 2000 := by
  rw [← show ((([(2, 1), (5, 2), (101, 1)] : List FactorBlock).map factorBlockValue).prod) = 5050 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_5, prime_101]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_5051 : Nat.totient 5051 = 5050 := by
  rw [← show ((([(5051, 1)] : List FactorBlock).map factorBlockValue).prod) = 5051 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_5051]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_5052 : Nat.totient 5052 = 1680 := by
  rw [← show ((([(2, 2), (3, 1), (421, 1)] : List FactorBlock).map factorBlockValue).prod) = 5052 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_3, prime_421]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_5053 : Nat.totient 5053 = 4860 := by
  rw [← show ((([(31, 1), (163, 1)] : List FactorBlock).map factorBlockValue).prod) = 5053 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_31, prime_163]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_5054 : Nat.totient 5054 = 2052 := by
  rw [← show ((([(2, 1), (7, 1), (19, 2)] : List FactorBlock).map factorBlockValue).prod) = 5054 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_7, prime_19]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_27721 : Nat.totient 27721 = 26244 := by
  rw [← show ((([(19, 1), (1459, 1)] : List FactorBlock).map factorBlockValue).prod) = 27721 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_19, prime_1459]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_27722 : Nat.totient 27722 = 13612 := by
  rw [← show ((([(2, 1), (83, 1), (167, 1)] : List FactorBlock).map factorBlockValue).prod) = 27722 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_83, prime_167]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_27723 : Nat.totient 27723 = 18480 := by
  rw [← show ((([(3, 1), (9241, 1)] : List FactorBlock).map factorBlockValue).prod) = 27723 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_3, prime_9241]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_27724 : Nat.totient 27724 = 13328 := by
  rw [← show ((([(2, 2), (29, 1), (239, 1)] : List FactorBlock).map factorBlockValue).prod) = 27724 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_29, prime_239]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_27725 : Nat.totient 27725 = 22160 := by
  rw [← show ((([(5, 2), (1109, 1)] : List FactorBlock).map factorBlockValue).prod) = 27725 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_5, prime_1109]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_27726 : Nat.totient 27726 = 9240 := by
  rw [← show ((([(2, 1), (3, 1), (4621, 1)] : List FactorBlock).map factorBlockValue).prod) = 27726 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_3, prime_4621]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_27727 : Nat.totient 27727 = 22272 := by
  rw [← show ((([(7, 1), (17, 1), (233, 1)] : List FactorBlock).map factorBlockValue).prod) = 27727 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_7, prime_17, prime_233]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_27728 : Nat.totient 27728 = 13856 := by
  rw [← show ((([(2, 4), (1733, 1)] : List FactorBlock).map factorBlockValue).prod) = 27728 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_1733]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_27729 : Nat.totient 27729 = 16848 := by
  rw [← show ((([(3, 3), (13, 1), (79, 1)] : List FactorBlock).map factorBlockValue).prod) = 27729 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_3, prime_13, prime_79]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_27730 : Nat.totient 27730 = 10672 := by
  rw [← show ((([(2, 1), (5, 1), (47, 1), (59, 1)] : List FactorBlock).map factorBlockValue).prod) = 27730 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_5, prime_47, prime_59]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_27731 : Nat.totient 27731 = 25200 := by
  rw [← show ((([(11, 1), (2521, 1)] : List FactorBlock).map factorBlockValue).prod) = 27731 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_11, prime_2521]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_27732 : Nat.totient 27732 = 9240 := by
  rw [← show ((([(2, 2), (3, 1), (2311, 1)] : List FactorBlock).map factorBlockValue).prod) = 27732 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_3, prime_2311]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_27733 : Nat.totient 27733 = 27732 := by
  rw [← show ((([(27733, 1)] : List FactorBlock).map factorBlockValue).prod) = 27733 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_27733]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_27734 : Nat.totient 27734 = 11844 := by
  rw [← show ((([(2, 1), (7, 2), (283, 1)] : List FactorBlock).map factorBlockValue).prod) = 27734 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_7, prime_283]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_27735 : Nat.totient 27735 = 14448 := by
  rw [← show ((([(3, 1), (5, 1), (43, 2)] : List FactorBlock).map factorBlockValue).prod) = 27735 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_3, prime_5, prime_43]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_27736 : Nat.totient 27736 = 13864 := by
  rw [← show ((([(2, 3), (3467, 1)] : List FactorBlock).map factorBlockValue).prod) = 27736 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_3467]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_27737 : Nat.totient 27737 = 27736 := by
  rw [← show ((([(27737, 1)] : List FactorBlock).map factorBlockValue).prod) = 27737 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_27737]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_27738 : Nat.totient 27738 = 8712 := by
  rw [← show ((([(2, 1), (3, 2), (23, 1), (67, 1)] : List FactorBlock).map factorBlockValue).prod) = 27738 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_3, prime_23, prime_67]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_27739 : Nat.totient 27739 = 27738 := by
  rw [← show ((([(27739, 1)] : List FactorBlock).map factorBlockValue).prod) = 27739 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_27739]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_27740 : Nat.totient 27740 = 10368 := by
  rw [← show ((([(2, 2), (5, 1), (19, 1), (73, 1)] : List FactorBlock).map factorBlockValue).prod) = 27740 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_5, prime_19, prime_73]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_27741 : Nat.totient 27741 = 15840 := by
  rw [← show ((([(3, 1), (7, 1), (1321, 1)] : List FactorBlock).map factorBlockValue).prod) = 27741 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_3, prime_7, prime_1321]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_55441 : Nat.totient 55441 = 55440 := by
  rw [← show ((([(55441, 1)] : List FactorBlock).map factorBlockValue).prod) = 55441 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_55441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_55442 : Nat.totient 55442 = 26244 := by
  rw [← show ((([(2, 1), (19, 1), (1459, 1)] : List FactorBlock).map factorBlockValue).prod) = 55442 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_19, prime_1459]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_55443 : Nat.totient 55443 = 36960 := by
  rw [← show ((([(3, 1), (18481, 1)] : List FactorBlock).map factorBlockValue).prod) = 55443 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_3, prime_18481]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_55444 : Nat.totient 55444 = 27224 := by
  rw [← show ((([(2, 2), (83, 1), (167, 1)] : List FactorBlock).map factorBlockValue).prod) = 55444 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_83, prime_167]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_55445 : Nat.totient 55445 = 40896 := by
  rw [← show ((([(5, 1), (13, 1), (853, 1)] : List FactorBlock).map factorBlockValue).prod) = 55445 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_5, prime_13, prime_853]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_55446 : Nat.totient 55446 = 18480 := by
  rw [← show ((([(2, 1), (3, 1), (9241, 1)] : List FactorBlock).map factorBlockValue).prod) = 55446 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_3, prime_9241]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_55447 : Nat.totient 55447 = 46992 := by
  rw [← show ((([(7, 1), (89, 2)] : List FactorBlock).map factorBlockValue).prod) = 55447 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_7, prime_89]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_55448 : Nat.totient 55448 = 26656 := by
  rw [← show ((([(2, 3), (29, 1), (239, 1)] : List FactorBlock).map factorBlockValue).prod) = 55448 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_29, prime_239]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_55449 : Nat.totient 55449 = 36000 := by
  rw [← show ((([(3, 2), (61, 1), (101, 1)] : List FactorBlock).map factorBlockValue).prod) = 55449 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_3, prime_61, prime_101]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_55450 : Nat.totient 55450 = 22160 := by
  rw [← show ((([(2, 1), (5, 2), (1109, 1)] : List FactorBlock).map factorBlockValue).prod) = 55450 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_5, prime_1109]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_55451 : Nat.totient 55451 = 49700 := by
  rw [← show ((([(11, 1), (71, 2)] : List FactorBlock).map factorBlockValue).prod) = 55451 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_11, prime_71]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_55452 : Nat.totient 55452 = 18480 := by
  rw [← show ((([(2, 2), (3, 1), (4621, 1)] : List FactorBlock).map factorBlockValue).prod) = 55452 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_3, prime_4621]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_55453 : Nat.totient 55453 = 53020 := by
  rw [← show ((([(23, 1), (2411, 1)] : List FactorBlock).map factorBlockValue).prod) = 55453 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_23, prime_2411]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_55454 : Nat.totient 55454 = 22272 := by
  rw [← show ((([(2, 1), (7, 1), (17, 1), (233, 1)] : List FactorBlock).map factorBlockValue).prod) = 55454 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_7, prime_17, prime_233]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_55455 : Nat.totient 55455 = 29568 := by
  rw [← show ((([(3, 1), (5, 1), (3697, 1)] : List FactorBlock).map factorBlockValue).prod) = 55455 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_3, prime_5, prime_3697]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_55456 : Nat.totient 55456 = 27712 := by
  rw [← show ((([(2, 5), (1733, 1)] : List FactorBlock).map factorBlockValue).prod) = 55456 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_1733]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_55457 : Nat.totient 55457 = 55456 := by
  rw [← show ((([(55457, 1)] : List FactorBlock).map factorBlockValue).prod) = 55457 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_55457]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_55458 : Nat.totient 55458 = 16848 := by
  rw [← show ((([(2, 1), (3, 3), (13, 1), (79, 1)] : List FactorBlock).map factorBlockValue).prod) = 55458 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_3, prime_13, prime_79]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_55459 : Nat.totient 55459 = 53640 := by
  rw [← show ((([(31, 1), (1789, 1)] : List FactorBlock).map factorBlockValue).prod) = 55459 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_31, prime_1789]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_55460 : Nat.totient 55460 = 21344 := by
  rw [← show ((([(2, 2), (5, 1), (47, 1), (59, 1)] : List FactorBlock).map factorBlockValue).prod) = 55460 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_5, prime_47, prime_59]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_55461 : Nat.totient 55461 = 29808 := by
  rw [← show ((([(3, 1), (7, 1), (19, 1), (139, 1)] : List FactorBlock).map factorBlockValue).prod) = 55461 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_3, prime_7, prime_19, prime_139]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_360361 : Nat.totient 360361 = 356224 := by
  rw [← show ((([(89, 1), (4049, 1)] : List FactorBlock).map factorBlockValue).prod) = 360361 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_89, prime_4049]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_360362 : Nat.totient 360362 = 180180 := by
  rw [← show ((([(2, 1), (180181, 1)] : List FactorBlock).map factorBlockValue).prod) = 360362 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_180181]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_360363 : Nat.totient 360363 = 240240 := by
  rw [← show ((([(3, 1), (120121, 1)] : List FactorBlock).map factorBlockValue).prod) = 360363 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_3, prime_120121]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_360364 : Nat.totient 360364 = 172304 := by
  rw [← show ((([(2, 2), (23, 1), (3917, 1)] : List FactorBlock).map factorBlockValue).prod) = 360364 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_23, prime_3917]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_360365 : Nat.totient 360365 = 288288 := by
  rw [← show ((([(5, 1), (72073, 1)] : List FactorBlock).map factorBlockValue).prod) = 360365 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_5, prime_72073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_360366 : Nat.totient 360366 = 113024 := by
  rw [← show ((([(2, 1), (3, 1), (17, 1), (3533, 1)] : List FactorBlock).map factorBlockValue).prod) = 360366 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_3, prime_17, prime_3533]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_360367 : Nat.totient 360367 = 308880 := by
  rw [← show ((([(7, 1), (51481, 1)] : List FactorBlock).map factorBlockValue).prod) = 360367 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_7, prime_51481]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_360368 : Nat.totient 360368 = 177600 := by
  rw [← show ((([(2, 4), (101, 1), (223, 1)] : List FactorBlock).map factorBlockValue).prod) = 360368 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_101, prime_223]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_360369 : Nat.totient 360369 = 240084 := by
  rw [← show ((([(3, 5), (1483, 1)] : List FactorBlock).map factorBlockValue).prod) = 360369 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_3, prime_1483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_360370 : Nat.totient 360370 = 144144 := by
  rw [← show ((([(2, 1), (5, 1), (36037, 1)] : List FactorBlock).map factorBlockValue).prod) = 360370 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_5, prime_36037]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_360371 : Nat.totient 360371 = 325800 := by
  rw [← show ((([(11, 1), (181, 2)] : List FactorBlock).map factorBlockValue).prod) = 360371 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_11, prime_181]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_360372 : Nat.totient 360372 = 117856 := by
  rw [← show ((([(2, 2), (3, 1), (59, 1), (509, 1)] : List FactorBlock).map factorBlockValue).prod) = 360372 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_3, prime_59, prime_509]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_360373 : Nat.totient 360373 = 314928 := by
  rw [← show ((([(13, 1), (19, 1), (1459, 1)] : List FactorBlock).map factorBlockValue).prod) = 360373 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_13, prime_19, prime_1459]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_360374 : Nat.totient 360374 = 154440 := by
  rw [← show ((([(2, 1), (7, 1), (25741, 1)] : List FactorBlock).map factorBlockValue).prod) = 360374 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_7, prime_25741]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_360375 : Nat.totient 360375 = 186000 := by
  rw [← show ((([(3, 1), (5, 3), (31, 2)] : List FactorBlock).map factorBlockValue).prod) = 360375 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_3, prime_5, prime_31]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_360376 : Nat.totient 360376 = 178080 := by
  rw [← show ((([(2, 3), (107, 1), (421, 1)] : List FactorBlock).map factorBlockValue).prod) = 360376 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_107, prime_421]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_360377 : Nat.totient 360377 = 358800 := by
  rw [← show ((([(277, 1), (1301, 1)] : List FactorBlock).map factorBlockValue).prod) = 360377 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_277, prime_1301]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_360378 : Nat.totient 360378 = 120120 := by
  rw [← show ((([(2, 1), (3, 2), (20021, 1)] : List FactorBlock).map factorBlockValue).prod) = 360378 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_3, prime_20021]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_360379 : Nat.totient 360379 = 359176 := by
  rw [← show ((([(557, 1), (647, 1)] : List FactorBlock).map factorBlockValue).prod) = 360379 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_557, prime_647]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_360380 : Nat.totient 360380 = 139968 := by
  rw [← show ((([(2, 2), (5, 1), (37, 1), (487, 1)] : List FactorBlock).map factorBlockValue).prod) = 360380 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_5, prime_37, prime_487]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_360381 : Nat.totient 360381 = 204360 := by
  rw [← show ((([(3, 1), (7, 1), (131, 2)] : List FactorBlock).map factorBlockValue).prod) = 360381 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_3, prime_7, prime_131]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_360382 : Nat.totient 360382 = 163800 := by
  rw [← show ((([(2, 1), (11, 1), (16381, 1)] : List FactorBlock).map factorBlockValue).prod) = 360382 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_11, prime_16381]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_720721 : Nat.totient 720721 = 710500 := by
  rw [← show ((([(71, 1), (10151, 1)] : List FactorBlock).map factorBlockValue).prod) = 720721 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_71, prime_10151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_720722 : Nat.totient 720722 = 356224 := by
  rw [← show ((([(2, 1), (89, 1), (4049, 1)] : List FactorBlock).map factorBlockValue).prod) = 720722 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_89, prime_4049]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_720723 : Nat.totient 720723 = 453600 := by
  rw [← show ((([(3, 1), (37, 1), (43, 1), (151, 1)] : List FactorBlock).map factorBlockValue).prod) = 720723 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_3, prime_37, prime_43, prime_151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_720724 : Nat.totient 720724 = 360360 := by
  rw [← show ((([(2, 2), (180181, 1)] : List FactorBlock).map factorBlockValue).prod) = 720724 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_180181]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_720725 : Nat.totient 720725 = 569520 := by
  rw [← show ((([(5, 2), (127, 1), (227, 1)] : List FactorBlock).map factorBlockValue).prod) = 720725 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_5, prime_127, prime_227]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_720726 : Nat.totient 720726 = 240240 := by
  rw [← show ((([(2, 1), (3, 1), (120121, 1)] : List FactorBlock).map factorBlockValue).prod) = 720726 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_3, prime_120121]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_720727 : Nat.totient 720727 = 585144 := by
  rw [← show ((([(7, 1), (19, 1), (5419, 1)] : List FactorBlock).map factorBlockValue).prod) = 720727 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_7, prime_19, prime_5419]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_720728 : Nat.totient 720728 = 344608 := by
  rw [← show ((([(2, 3), (23, 1), (3917, 1)] : List FactorBlock).map factorBlockValue).prod) = 720728 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_23, prime_3917]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_720729 : Nat.totient 720729 = 473472 := by
  rw [← show ((([(3, 2), (73, 1), (1097, 1)] : List FactorBlock).map factorBlockValue).prod) = 720729 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_3, prime_73, prime_1097]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_720730 : Nat.totient 720730 = 288288 := by
  rw [← show ((([(2, 1), (5, 1), (72073, 1)] : List FactorBlock).map factorBlockValue).prod) = 720730 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_5, prime_72073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_720731 : Nat.totient 720731 = 655200 := by
  rw [← show ((([(11, 1), (65521, 1)] : List FactorBlock).map factorBlockValue).prod) = 720731 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_11, prime_65521]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_720732 : Nat.totient 720732 = 226048 := by
  rw [← show ((([(2, 2), (3, 1), (17, 1), (3533, 1)] : List FactorBlock).map factorBlockValue).prod) = 720732 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_3, prime_17, prime_3533]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_720733 : Nat.totient 720733 = 665280 := by
  rw [← show ((([(13, 1), (55441, 1)] : List FactorBlock).map factorBlockValue).prod) = 720733 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_13, prime_55441]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_720734 : Nat.totient 720734 = 308880 := by
  rw [← show ((([(2, 1), (7, 1), (51481, 1)] : List FactorBlock).map factorBlockValue).prod) = 720734 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_7, prime_51481]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_720735 : Nat.totient 720735 = 384384 := by
  rw [← show ((([(3, 1), (5, 1), (48049, 1)] : List FactorBlock).map factorBlockValue).prod) = 720735 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_3, prime_5, prime_48049]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_720736 : Nat.totient 720736 = 355200 := by
  rw [← show ((([(2, 5), (101, 1), (223, 1)] : List FactorBlock).map factorBlockValue).prod) = 720736 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_101, prime_223]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_720737 : Nat.totient 720737 = 695072 := by
  rw [← show ((([(29, 2), (857, 1)] : List FactorBlock).map factorBlockValue).prod) = 720737 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_29, prime_857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_720738 : Nat.totient 720738 = 240084 := by
  rw [← show ((([(2, 1), (3, 5), (1483, 1)] : List FactorBlock).map factorBlockValue).prod) = 720738 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_3, prime_1483]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_720739 : Nat.totient 720739 = 703120 := by
  rw [← show ((([(41, 1), (17579, 1)] : List FactorBlock).map factorBlockValue).prod) = 720739 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_41, prime_17579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_720740 : Nat.totient 720740 = 288288 := by
  rw [← show ((([(2, 2), (5, 1), (36037, 1)] : List FactorBlock).map factorBlockValue).prod) = 720740 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_5, prime_36037]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_720741 : Nat.totient 720741 = 411768 := by
  rw [← show ((([(3, 1), (7, 2), (4903, 1)] : List FactorBlock).map factorBlockValue).prod) = 720741 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_3, prime_7, prime_4903]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_720742 : Nat.totient 720742 = 325800 := by
  rw [← show ((([(2, 1), (11, 1), (181, 2)] : List FactorBlock).map factorBlockValue).prod) = 720742 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_11, prime_181]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_720743 : Nat.totient 720743 = 720742 := by
  rw [← show ((([(720743, 1)] : List FactorBlock).map factorBlockValue).prod) = 720743 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_720743]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_1441441 : Nat.totient 1441441 = 1414192 := by
  rw [← show ((([(53, 1), (27197, 1)] : List FactorBlock).map factorBlockValue).prod) = 1441441 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_53, prime_27197]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_1441442 : Nat.totient 1441442 = 710500 := by
  rw [← show ((([(2, 1), (71, 1), (10151, 1)] : List FactorBlock).map factorBlockValue).prod) = 1441442 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_71, prime_10151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_1441443 : Nat.totient 1441443 = 940424 := by
  rw [← show ((([(3, 1), (47, 1), (10223, 1)] : List FactorBlock).map factorBlockValue).prod) = 1441443 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_3, prime_47, prime_10223]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_1441444 : Nat.totient 1441444 = 712448 := by
  rw [← show ((([(2, 2), (89, 1), (4049, 1)] : List FactorBlock).map factorBlockValue).prod) = 1441444 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_89, prime_4049]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_1441445 : Nat.totient 1441445 = 1113280 := by
  rw [← show ((([(5, 1), (29, 1), (9941, 1)] : List FactorBlock).map factorBlockValue).prod) = 1441445 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_5, prime_29, prime_9941]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_1441446 : Nat.totient 1441446 = 453600 := by
  rw [← show ((([(2, 1), (3, 1), (37, 1), (43, 1), (151, 1)] : List FactorBlock).map factorBlockValue).prod) = 1441446 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_3, prime_37, prime_43, prime_151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_1441447 : Nat.totient 1441447 = 1162752 := by
  rw [← show ((([(7, 1), (17, 1), (12113, 1)] : List FactorBlock).map factorBlockValue).prod) = 1441447 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_7, prime_17, prime_12113]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_1441448 : Nat.totient 1441448 = 720720 := by
  rw [← show ((([(2, 3), (180181, 1)] : List FactorBlock).map factorBlockValue).prod) = 1441448 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_180181]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_1441449 : Nat.totient 1441449 = 952560 := by
  rw [← show ((([(3, 3), (197, 1), (271, 1)] : List FactorBlock).map factorBlockValue).prod) = 1441449 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_3, prime_197, prime_271]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_1441450 : Nat.totient 1441450 = 569520 := by
  rw [← show ((([(2, 1), (5, 2), (127, 1), (227, 1)] : List FactorBlock).map factorBlockValue).prod) = 1441450 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_5, prime_127, prime_227]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_1441451 : Nat.totient 1441451 = 1310400 := by
  rw [← show ((([(11, 1), (131041, 1)] : List FactorBlock).map factorBlockValue).prod) = 1441451 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_11, prime_131041]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_1441452 : Nat.totient 1441452 = 480480 := by
  rw [← show ((([(2, 2), (3, 1), (120121, 1)] : List FactorBlock).map factorBlockValue).prod) = 1441452 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_3, prime_120121]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_1441453 : Nat.totient 1441453 = 1330560 := by
  rw [← show ((([(13, 1), (110881, 1)] : List FactorBlock).map factorBlockValue).prod) = 1441453 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_13, prime_110881]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_1441454 : Nat.totient 1441454 = 585144 := by
  rw [← show ((([(2, 1), (7, 1), (19, 1), (5419, 1)] : List FactorBlock).map factorBlockValue).prod) = 1441454 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_7, prime_19, prime_5419]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_1441455 : Nat.totient 1441455 = 768768 := by
  rw [← show ((([(3, 1), (5, 1), (96097, 1)] : List FactorBlock).map factorBlockValue).prod) = 1441455 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_3, prime_5, prime_96097]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_1441456 : Nat.totient 1441456 = 689216 := by
  rw [← show ((([(2, 4), (23, 1), (3917, 1)] : List FactorBlock).map factorBlockValue).prod) = 1441456 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_23, prime_3917]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_1441457 : Nat.totient 1441457 = 1437696 := by
  rw [← show ((([(433, 1), (3329, 1)] : List FactorBlock).map factorBlockValue).prod) = 1441457 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_433, prime_3329]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_1441458 : Nat.totient 1441458 = 473472 := by
  rw [← show ((([(2, 1), (3, 2), (73, 1), (1097, 1)] : List FactorBlock).map factorBlockValue).prod) = 1441458 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_3, prime_73, prime_1097]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_1441459 : Nat.totient 1441459 = 1441458 := by
  rw [← show ((([(1441459, 1)] : List FactorBlock).map factorBlockValue).prod) = 1441459 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_1441459]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_1441460 : Nat.totient 1441460 = 576576 := by
  rw [← show ((([(2, 2), (5, 1), (72073, 1)] : List FactorBlock).map factorBlockValue).prod) = 1441460 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_5, prime_72073]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_1441461 : Nat.totient 1441461 = 812784 := by
  rw [← show ((([(3, 1), (7, 1), (83, 1), (827, 1)] : List FactorBlock).map factorBlockValue).prod) = 1441461 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_3, prime_7, prime_83, prime_827]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_1441462 : Nat.totient 1441462 = 655200 := by
  rw [← show ((([(2, 1), (11, 1), (65521, 1)] : List FactorBlock).map factorBlockValue).prod) = 1441462 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_11, prime_65521]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_1441463 : Nat.totient 1441463 = 1441462 := by
  rw [← show ((([(1441463, 1)] : List FactorBlock).map factorBlockValue).prod) = 1441463 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_1441463]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_12252241 : Nat.totient 12252241 = 12243312 := by
  rw [← show ((([(1693, 1), (7237, 1)] : List FactorBlock).map factorBlockValue).prod) = 12252241 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_1693, prime_7237]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_12252242 : Nat.totient 12252242 = 5995732 := by
  rw [← show ((([(2, 1), (47, 1), (130343, 1)] : List FactorBlock).map factorBlockValue).prod) = 12252242 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_47, prime_130343]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_12252243 : Nat.totient 12252243 = 8168160 := by
  rw [← show ((([(3, 1), (4084081, 1)] : List FactorBlock).map factorBlockValue).prod) = 12252243 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_3, prime_4084081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_12252244 : Nat.totient 12252244 = 6119000 := by
  rw [← show ((([(2, 2), (1451, 1), (2111, 1)] : List FactorBlock).map factorBlockValue).prod) = 12252244 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_1451, prime_2111]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_12252245 : Nat.totient 12252245 = 9285840 := by
  rw [← show ((([(5, 1), (19, 1), (128971, 1)] : List FactorBlock).map factorBlockValue).prod) = 12252245 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_5, prime_19, prime_128971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_12252246 : Nat.totient 12252246 = 4081224 := by
  rw [← show ((([(2, 1), (3, 1), (1429, 2)] : List FactorBlock).map factorBlockValue).prod) = 12252246 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_3, prime_1429]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_12252247 : Nat.totient 12252247 = 10357632 := by
  rw [← show ((([(7, 1), (73, 1), (23977, 1)] : List FactorBlock).map factorBlockValue).prod) = 12252247 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_7, prime_73, prime_23977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_12252248 : Nat.totient 12252248 = 5983488 := by
  rw [← show ((([(2, 3), (43, 1), (35617, 1)] : List FactorBlock).map factorBlockValue).prod) = 12252248 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_43, prime_35617]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_12252249 : Nat.totient 12252249 = 8089920 := by
  rw [← show ((([(3, 3), (107, 1), (4241, 1)] : List FactorBlock).map factorBlockValue).prod) = 12252249 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_3, prime_107, prime_4241]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_12252250 : Nat.totient 12252250 = 4900800 := by
  rw [← show ((([(2, 1), (5, 3), (49009, 1)] : List FactorBlock).map factorBlockValue).prod) = 12252250 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_5, prime_49009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_12252251 : Nat.totient 12252251 = 11038720 := by
  rw [← show ((([(11, 1), (113, 1), (9857, 1)] : List FactorBlock).map factorBlockValue).prod) = 12252251 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_11, prime_113, prime_9857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_12252252 : Nat.totient 12252252 = 4060800 := by
  rw [← show ((([(2, 2), (3, 1), (181, 1), (5641, 1)] : List FactorBlock).map factorBlockValue).prod) = 12252252 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_3, prime_181, prime_5641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_12252253 : Nat.totient 12252253 = 11282544 := by
  rw [← show ((([(13, 1), (547, 1), (1723, 1)] : List FactorBlock).map factorBlockValue).prod) = 12252253 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_13, prime_547, prime_1723]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_12252254 : Nat.totient 12252254 = 4898880 := by
  rw [← show ((([(2, 1), (7, 2), (31, 1), (37, 1), (109, 1)] : List FactorBlock).map factorBlockValue).prod) = 12252254 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_7, prime_31, prime_37, prime_109]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_12252255 : Nat.totient 12252255 = 6534528 := by
  rw [← show ((([(3, 1), (5, 1), (816817, 1)] : List FactorBlock).map factorBlockValue).prod) = 12252255 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_3, prime_5, prime_816817]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_12252256 : Nat.totient 12252256 = 6126112 := by
  rw [← show ((([(2, 5), (382883, 1)] : List FactorBlock).map factorBlockValue).prod) = 12252256 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_382883]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_12252257 : Nat.totient 12252257 = 11368000 := by
  rw [← show ((([(17, 1), (71, 1), (10151, 1)] : List FactorBlock).map factorBlockValue).prod) = 12252257 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_17, prime_71, prime_10151]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_12252258 : Nat.totient 12252258 = 4084080 := by
  rw [← show ((([(2, 1), (3, 2), (680681, 1)] : List FactorBlock).map factorBlockValue).prod) = 12252258 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_3, prime_680681]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_12252259 : Nat.totient 12252259 = 12252258 := by
  rw [← show ((([(12252259, 1)] : List FactorBlock).map factorBlockValue).prod) = 12252259 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_12252259]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_12252260 : Nat.totient 12252260 = 4900896 := by
  rw [← show ((([(2, 2), (5, 1), (612613, 1)] : List FactorBlock).map factorBlockValue).prod) = 12252260 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_5, prime_612613]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_12252261 : Nat.totient 12252261 = 6696624 := by
  rw [← show ((([(3, 1), (7, 1), (23, 1), (25367, 1)] : List FactorBlock).map factorBlockValue).prod) = 12252261 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_3, prime_7, prime_23, prime_25367]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_12252262 : Nat.totient 12252262 = 5514120 := by
  rw [← show ((([(2, 1), (11, 1), (103, 1), (5407, 1)] : List FactorBlock).map factorBlockValue).prod) = 12252262 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_11, prime_103, prime_5407]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_12252263 : Nat.totient 12252263 = 12252262 := by
  rw [← show ((([(12252263, 1)] : List FactorBlock).map factorBlockValue).prod) = 12252263 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_12252263]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_12252264 : Nat.totient 12252264 = 3815424 := by
  rw [← show ((([(2, 3), (3, 1), (19, 1), (97, 1), (277, 1)] : List FactorBlock).map factorBlockValue).prod) = 12252264 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_3, prime_19, prime_97, prime_277]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_12252265 : Nat.totient 12252265 = 9801808 := by
  rw [← show ((([(5, 1), (2450453, 1)] : List FactorBlock).map factorBlockValue).prod) = 12252265 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_5, prime_2450453]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_12252266 : Nat.totient 12252266 = 5654880 := by
  rw [← show ((([(2, 1), (13, 1), (471241, 1)] : List FactorBlock).map factorBlockValue).prod) = 12252266 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_13, prime_471241]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_24504481 : Nat.totient 24504481 = 24494512 := by
  rw [← show ((([(4397, 1), (5573, 1)] : List FactorBlock).map factorBlockValue).prod) = 24504481 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_4397, prime_5573]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_24504482 : Nat.totient 24504482 = 12243312 := by
  rw [← show ((([(2, 1), (1693, 1), (7237, 1)] : List FactorBlock).map factorBlockValue).prod) = 24504482 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_1693, prime_7237]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_24504483 : Nat.totient 24504483 = 16336320 := by
  rw [← show ((([(3, 1), (8168161, 1)] : List FactorBlock).map factorBlockValue).prod) = 24504483 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_3, prime_8168161]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_24504484 : Nat.totient 24504484 = 11991464 := by
  rw [← show ((([(2, 2), (47, 1), (130343, 1)] : List FactorBlock).map factorBlockValue).prod) = 24504484 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_47, prime_130343]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_24504485 : Nat.totient 24504485 = 19509840 := by
  rw [← show ((([(5, 1), (211, 1), (23227, 1)] : List FactorBlock).map factorBlockValue).prod) = 24504485 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_5, prime_211, prime_23227]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_24504486 : Nat.totient 24504486 = 8168160 := by
  rw [← show ((([(2, 1), (3, 1), (4084081, 1)] : List FactorBlock).map factorBlockValue).prod) = 24504486 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_3, prime_4084081]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_24504487 : Nat.totient 24504487 = 20992620 := by
  rw [← show ((([(7, 1), (1871, 2)] : List FactorBlock).map factorBlockValue).prod) = 24504487 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_7, prime_1871]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_24504488 : Nat.totient 24504488 = 12238000 := by
  rw [← show ((([(2, 3), (1451, 1), (2111, 1)] : List FactorBlock).map factorBlockValue).prod) = 24504488 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_1451, prime_2111]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_24504489 : Nat.totient 24504489 = 16313472 := by
  rw [← show ((([(3, 2), (953, 1), (2857, 1)] : List FactorBlock).map factorBlockValue).prod) = 24504489 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_3, prime_953, prime_2857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_24504490 : Nat.totient 24504490 = 9285840 := by
  rw [← show ((([(2, 1), (5, 1), (19, 1), (128971, 1)] : List FactorBlock).map factorBlockValue).prod) = 24504490 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_5, prime_19, prime_128971]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_24504491 : Nat.totient 24504491 = 22233640 := by
  rw [← show ((([(11, 1), (599, 1), (3719, 1)] : List FactorBlock).map factorBlockValue).prod) = 24504491 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_11, prime_599, prime_3719]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_24504492 : Nat.totient 24504492 = 8162448 := by
  rw [← show ((([(2, 2), (3, 1), (1429, 2)] : List FactorBlock).map factorBlockValue).prod) = 24504492 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_3, prime_1429]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_24504493 : Nat.totient 24504493 = 22239360 := by
  rw [← show ((([(13, 2), (61, 1), (2377, 1)] : List FactorBlock).map factorBlockValue).prod) = 24504493 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_13, prime_61, prime_2377]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_24504494 : Nat.totient 24504494 = 10357632 := by
  rw [← show ((([(2, 1), (7, 1), (73, 1), (23977, 1)] : List FactorBlock).map factorBlockValue).prod) = 24504494 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_7, prime_73, prime_23977]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_24504495 : Nat.totient 24504495 = 13069056 := by
  rw [← show ((([(3, 1), (5, 1), (1633633, 1)] : List FactorBlock).map factorBlockValue).prod) = 24504495 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_3, prime_5, prime_1633633]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_24504496 : Nat.totient 24504496 = 11966976 := by
  rw [← show ((([(2, 4), (43, 1), (35617, 1)] : List FactorBlock).map factorBlockValue).prod) = 24504496 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_43, prime_35617]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_24504497 : Nat.totient 24504497 = 22627072 := by
  rw [← show ((([(17, 1), (53, 1), (27197, 1)] : List FactorBlock).map factorBlockValue).prod) = 24504497 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_17, prime_53, prime_27197]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_24504498 : Nat.totient 24504498 = 8089920 := by
  rw [← show ((([(2, 1), (3, 3), (107, 1), (4241, 1)] : List FactorBlock).map factorBlockValue).prod) = 24504498 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_3, prime_107, prime_4241]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_24504499 : Nat.totient 24504499 = 23344200 := by
  rw [← show ((([(23, 1), (263, 1), (4051, 1)] : List FactorBlock).map factorBlockValue).prod) = 24504499 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_23, prime_263, prime_4051]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_24504500 : Nat.totient 24504500 = 9801600 := by
  rw [← show ((([(2, 2), (5, 3), (49009, 1)] : List FactorBlock).map factorBlockValue).prod) = 24504500 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_5, prime_49009]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_24504501 : Nat.totient 24504501 = 13974768 := by
  rw [← show ((([(3, 1), (7, 1), (739, 1), (1579, 1)] : List FactorBlock).map factorBlockValue).prod) = 24504501 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_3, prime_7, prime_739, prime_1579]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_24504502 : Nat.totient 24504502 = 11038720 := by
  rw [← show ((([(2, 1), (11, 1), (113, 1), (9857, 1)] : List FactorBlock).map factorBlockValue).prod) = 24504502 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_11, prime_113, prime_9857]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_24504503 : Nat.totient 24504503 = 24504502 := by
  rw [← show ((([(24504503, 1)] : List FactorBlock).map factorBlockValue).prod) = 24504503 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_24504503]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_24504504 : Nat.totient 24504504 = 8121600 := by
  rw [← show ((([(2, 3), (3, 1), (181, 1), (5641, 1)] : List FactorBlock).map factorBlockValue).prod) = 24504504 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_3, prime_181, prime_5641]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_24504505 : Nat.totient 24504505 = 19181440 := by
  rw [← show ((([(5, 1), (83, 1), (137, 1), (431, 1)] : List FactorBlock).map factorBlockValue).prod) = 24504505 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_5, prime_83, prime_137, prime_431]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_24504506 : Nat.totient 24504506 = 11282544 := by
  rw [← show ((([(2, 1), (13, 1), (547, 1), (1723, 1)] : List FactorBlock).map factorBlockValue).prod) = 24504506 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_2, prime_13, prime_547, prime_1723]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

/-! ## The 34 diagonal certificates -/

theorem certifiedKill_diagonal_t1 :
    certifiedKill (periodLcm 1) (periodLcm 1) 6 := by
  norm_num [certifiedKill, windowDiscrepancy, periodLcm, Finset.sum_range_succ,
    phi_2, phi_3, phi_4, phi_5, phi_6, phi_7, phi_3, phi_4, phi_5, phi_6, phi_7, phi_8]

theorem certifiedKill_diagonal_t2 :
    certifiedKill (periodLcm 2) (periodLcm 2) 5 := by
  norm_num [certifiedKill, windowDiscrepancy, periodLcm, Finset.sum_range_succ,
    phi_3, phi_4, phi_5, phi_6, phi_7, phi_5, phi_6, phi_7, phi_8, phi_9]

theorem certifiedKill_diagonal_t3 :
    certifiedKill (periodLcm 3) (periodLcm 3) 7 := by
  norm_num [certifiedKill, windowDiscrepancy, periodLcm, Finset.sum_range_succ,
    phi_7, phi_8, phi_9, phi_10, phi_11, phi_12, phi_13, phi_13, phi_14, phi_15, phi_16, phi_17, phi_18, phi_19]

theorem certifiedKill_diagonal_t4 :
    certifiedKill (periodLcm 4) (periodLcm 4) 7 := by
  norm_num [certifiedKill, windowDiscrepancy, periodLcm, Finset.sum_range_succ,
    phi_13, phi_14, phi_15, phi_16, phi_17, phi_18, phi_19, phi_25, phi_26, phi_27, phi_28, phi_29, phi_30, phi_31]

theorem certifiedKill_diagonal_t5 :
    certifiedKill (periodLcm 5) (periodLcm 5) 9 := by
  norm_num [certifiedKill, windowDiscrepancy, periodLcm, Finset.sum_range_succ,
    phi_61, phi_62, phi_63, phi_64, phi_65, phi_66, phi_67, phi_68, phi_69, phi_121, phi_122, phi_123, phi_124, phi_125, phi_126, phi_127, phi_128, phi_129]

theorem certifiedKill_diagonal_t7 :
    certifiedKill (periodLcm 7) (periodLcm 7) 14 := by
  norm_num [certifiedKill, windowDiscrepancy, periodLcm, Finset.sum_range_succ,
    phi_421, phi_422, phi_423, phi_424, phi_425, phi_426, phi_427, phi_428, phi_429, phi_430, phi_431, phi_432, phi_433, phi_434, phi_841, phi_842, phi_843, phi_844, phi_845, phi_846, phi_847, phi_848, phi_849, phi_850, phi_851, phi_852, phi_853, phi_854]

theorem certifiedKill_diagonal_t8 :
    certifiedKill (periodLcm 8) (periodLcm 8) 15 := by
  norm_num [certifiedKill, windowDiscrepancy, periodLcm, Finset.sum_range_succ,
    phi_841, phi_842, phi_843, phi_844, phi_845, phi_846, phi_847, phi_848, phi_849, phi_850, phi_851, phi_852, phi_853, phi_854, phi_855, phi_1681, phi_1682, phi_1683, phi_1684, phi_1685, phi_1686, phi_1687, phi_1688, phi_1689, phi_1690, phi_1691, phi_1692, phi_1693, phi_1694, phi_1695]

theorem certifiedKill_diagonal_t9 :
    certifiedKill (periodLcm 9) (periodLcm 9) 14 := by
  norm_num [certifiedKill, windowDiscrepancy, periodLcm, Finset.sum_range_succ,
    phi_2521, phi_2522, phi_2523, phi_2524, phi_2525, phi_2526, phi_2527, phi_2528, phi_2529, phi_2530, phi_2531, phi_2532, phi_2533, phi_2534, phi_5041, phi_5042, phi_5043, phi_5044, phi_5045, phi_5046, phi_5047, phi_5048, phi_5049, phi_5050, phi_5051, phi_5052, phi_5053, phi_5054]

theorem certifiedKill_diagonal_t11 :
    certifiedKill (periodLcm 11) (periodLcm 11) 21 := by
  norm_num [certifiedKill, windowDiscrepancy, periodLcm, Finset.sum_range_succ,
    phi_27721, phi_27722, phi_27723, phi_27724, phi_27725, phi_27726, phi_27727, phi_27728, phi_27729, phi_27730, phi_27731, phi_27732, phi_27733, phi_27734, phi_27735, phi_27736, phi_27737, phi_27738, phi_27739, phi_27740, phi_27741, phi_55441, phi_55442, phi_55443, phi_55444, phi_55445, phi_55446, phi_55447, phi_55448, phi_55449, phi_55450, phi_55451, phi_55452, phi_55453, phi_55454, phi_55455, phi_55456, phi_55457, phi_55458, phi_55459, phi_55460, phi_55461]

theorem certifiedKill_diagonal_t13 :
    certifiedKill (periodLcm 13) (periodLcm 13) 22 := by
  norm_num [certifiedKill, windowDiscrepancy, periodLcm, Finset.sum_range_succ,
    phi_360361, phi_360362, phi_360363, phi_360364, phi_360365, phi_360366, phi_360367, phi_360368, phi_360369, phi_360370, phi_360371, phi_360372, phi_360373, phi_360374, phi_360375, phi_360376, phi_360377, phi_360378, phi_360379, phi_360380, phi_360381, phi_360382, phi_720721, phi_720722, phi_720723, phi_720724, phi_720725, phi_720726, phi_720727, phi_720728, phi_720729, phi_720730, phi_720731, phi_720732, phi_720733, phi_720734, phi_720735, phi_720736, phi_720737, phi_720738, phi_720739, phi_720740, phi_720741, phi_720742]

theorem certifiedKill_diagonal_t16 :
    certifiedKill (periodLcm 16) (periodLcm 16) 23 := by
  norm_num [certifiedKill, windowDiscrepancy, periodLcm, Finset.sum_range_succ,
    phi_720721, phi_720722, phi_720723, phi_720724, phi_720725, phi_720726, phi_720727, phi_720728, phi_720729, phi_720730, phi_720731, phi_720732, phi_720733, phi_720734, phi_720735, phi_720736, phi_720737, phi_720738, phi_720739, phi_720740, phi_720741, phi_720742, phi_720743, phi_1441441, phi_1441442, phi_1441443, phi_1441444, phi_1441445, phi_1441446, phi_1441447, phi_1441448, phi_1441449, phi_1441450, phi_1441451, phi_1441452, phi_1441453, phi_1441454, phi_1441455, phi_1441456, phi_1441457, phi_1441458, phi_1441459, phi_1441460, phi_1441461, phi_1441462, phi_1441463]

theorem certifiedKill_diagonal_t17 :
    certifiedKill (periodLcm 17) (periodLcm 17) 26 := by
  norm_num [certifiedKill, windowDiscrepancy, periodLcm, Finset.sum_range_succ,
    phi_12252241, phi_12252242, phi_12252243, phi_12252244, phi_12252245, phi_12252246, phi_12252247, phi_12252248, phi_12252249, phi_12252250, phi_12252251, phi_12252252, phi_12252253, phi_12252254, phi_12252255, phi_12252256, phi_12252257, phi_12252258, phi_12252259, phi_12252260, phi_12252261, phi_12252262, phi_12252263, phi_12252264, phi_12252265, phi_12252266, phi_24504481, phi_24504482, phi_24504483, phi_24504484, phi_24504485, phi_24504486, phi_24504487, phi_24504488, phi_24504489, phi_24504490, phi_24504491, phi_24504492, phi_24504493, phi_24504494, phi_24504495, phi_24504496, phi_24504497, phi_24504498, phi_24504499, phi_24504500, phi_24504501, phi_24504502, phi_24504503, phi_24504504, phi_24504505, phi_24504506]

def diagonalPincerCertificateScales : List ℕ := [1, 2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17]

def diagonalPincerKillDepth : ℕ → ℕ
  | 1 => 6
  | 2 => 5
  | 3 => 7
  | 4 => 7
  | 5 => 9
  | 7 => 14
  | 8 => 15
  | 9 => 14
  | 11 => 21
  | 13 => 22
  | 16 => 23
  | 17 => 26
  | _ => 0

/-- All 12 distinct LCM scales in the landed `t ≤ 17` prefix fire. -/
theorem certifiedKill_diagonal_all_imported :
    ∀ t ∈ diagonalPincerCertificateScales,
      certifiedKill (periodLcm t) (periodLcm t) (diagonalPincerKillDepth t) := by
  intro t ht
  simp only [diagonalPincerCertificateScales, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [diagonalPincerKillDepth] using certifiedKill_diagonal_t1
  · simpa [diagonalPincerKillDepth] using certifiedKill_diagonal_t2
  · simpa [diagonalPincerKillDepth] using certifiedKill_diagonal_t3
  · simpa [diagonalPincerKillDepth] using certifiedKill_diagonal_t4
  · simpa [diagonalPincerKillDepth] using certifiedKill_diagonal_t5
  · simpa [diagonalPincerKillDepth] using certifiedKill_diagonal_t7
  · simpa [diagonalPincerKillDepth] using certifiedKill_diagonal_t8
  · simpa [diagonalPincerKillDepth] using certifiedKill_diagonal_t9
  · simpa [diagonalPincerKillDepth] using certifiedKill_diagonal_t11
  · simpa [diagonalPincerKillDepth] using certifiedKill_diagonal_t13
  · simpa [diagonalPincerKillDepth] using certifiedKill_diagonal_t16
  · simpa [diagonalPincerKillDepth] using certifiedKill_diagonal_t17

#print axioms certifiedKill_diagonal_all_imported

end TotientTailPeriodKiller
end Erdos249257
