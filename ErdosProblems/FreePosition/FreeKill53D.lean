import Batteries.Tactic.OpenPrivate
import Erdos249257.DiagonalPincerCertificatesT53

namespace Erdos249257
namespace TotientTailPeriodKiller

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

open private
  phi_t53_164249358725037825439201 phi_t53_164249358725037825439202 phi_t53_164249358725037825439203 phi_t53_164249358725037825439204
  phi_t53_164249358725037825439205 phi_t53_164249358725037825439206 phi_t53_164249358725037825439207 phi_t53_164249358725037825439208
  phi_t53_164249358725037825439209 phi_t53_164249358725037825439210 phi_t53_164249358725037825439211 phi_t53_164249358725037825439212
  phi_t53_164249358725037825439213 phi_t53_164249358725037825439214 phi_t53_164249358725037825439215 phi_t53_164249358725037825439216
  phi_t53_164249358725037825439217 phi_t53_164249358725037825439218 phi_t53_164249358725037825439219 phi_t53_164249358725037825439220
  phi_t53_164249358725037825439221 phi_t53_164249358725037825439222 phi_t53_164249358725037825439223 phi_t53_164249358725037825439224
  phi_t53_164249358725037825439225 phi_t53_164249358725037825439226 phi_t53_164249358725037825439227 phi_t53_164249358725037825439228
  phi_t53_164249358725037825439229 phi_t53_164249358725037825439230 phi_t53_164249358725037825439231 phi_t53_164249358725037825439232
  phi_t53_164249358725037825439233 phi_t53_164249358725037825439234 phi_t53_164249358725037825439235 phi_t53_164249358725037825439236
  phi_t53_164249358725037825439237 phi_t53_164249358725037825439238 phi_t53_164249358725037825439239 phi_t53_164249358725037825439240
  phi_t53_164249358725037825439241 phi_t53_164249358725037825439242 phi_t53_164249358725037825439243 phi_t53_164249358725037825439244
  phi_t53_164249358725037825439245 phi_t53_164249358725037825439246 phi_t53_164249358725037825439247 phi_t53_164249358725037825439248
  phi_t53_164249358725037825439249 phi_t53_164249358725037825439250 phi_t53_164249358725037825439251 phi_t53_164249358725037825439252
  phi_t53_164249358725037825439253 phi_t53_164249358725037825439254 phi_t53_164249358725037825439255 phi_t53_164249358725037825439256
  phi_t53_164249358725037825439257 phi_t53_164249358725037825439258 phi_t53_164249358725037825439259 phi_t53_164249358725037825439260
  phi_t53_164249358725037825439261 phi_t53_164249358725037825439262 phi_t53_164249358725037825439263 phi_t53_164249358725037825439264
  phi_t53_164249358725037825439265 phi_t53_164249358725037825439266 phi_t53_164249358725037825439267 phi_t53_164249358725037825439268
  phi_t53_164249358725037825439269 phi_t53_164249358725037825439270 phi_t53_164249358725037825439271 phi_t53_164249358725037825439272
  phi_t53_164249358725037825439273 phi_t53_164249358725037825439274 phi_t53_164249358725037825439275 phi_t53_164249358725037825439276
  phi_t53_164249358725037825439277 phi_t53_164249358725037825439278 phi_t53_164249358725037825439279 phi_t53_164249358725037825439280
  phi_t53_164249358725037825439281
  from Erdos249257.DiagonalPincerCertificatesT53

private theorem prime_free53D_2 : Nat.Prime 2 := by norm_num
private theorem prime_free53D_3 : Nat.Prime 3 := by norm_num
private theorem prime_free53D_5 : Nat.Prime 5 := by norm_num
private theorem prime_free53D_7 : Nat.Prime 7 := by norm_num
private theorem prime_free53D_11 : Nat.Prime 11 := by norm_num
private theorem prime_free53D_13 : Nat.Prime 13 := by norm_num
private theorem prime_free53D_17 : Nat.Prime 17 := by norm_num
private theorem prime_free53D_19 : Nat.Prime 19 := by norm_num
private theorem prime_free53D_23 : Nat.Prime 23 := by norm_num
private theorem prime_free53D_29 : Nat.Prime 29 := by norm_num
private theorem prime_free53D_31 : Nat.Prime 31 := by norm_num
private theorem prime_free53D_37 : Nat.Prime 37 := by norm_num
private theorem prime_free53D_41 : Nat.Prime 41 := by norm_num
private theorem prime_free53D_43 : Nat.Prime 43 := by norm_num
private theorem prime_free53D_47 : Nat.Prime 47 := by norm_num
private theorem prime_free53D_53 : Nat.Prime 53 := by norm_num
private theorem prime_free53D_67 : Nat.Prime 67 := by norm_num
private theorem prime_free53D_79 : Nat.Prime 79 := by norm_num
private theorem prime_free53D_359 : Nat.Prime 359 := by norm_num
private theorem prime_free53D_167355017 : Nat.Prime 167355017 := by norm_num
private theorem prime_free53D_5380187 : Nat.Prime 5380187 := by norm_num

private theorem prime_free53D_5767723305889 : Nat.Prime 5767723305889 := by
  apply lucas_primality 5767723305889 (7 : ZMod 5767723305889)
  ·
      have fermat_0 : (7 : ZMod 5767723305889) ^ 1 = 7 := by norm_num
      have fermat_1 : (7 : ZMod 5767723305889) ^ 2 = 49 := by
        calc
          (7 : ZMod 5767723305889) ^ 2 = (7 : ZMod 5767723305889) ^ (1 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 1 * (7 : ZMod 5767723305889) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [fermat_0]; decide
      have fermat_2 : (7 : ZMod 5767723305889) ^ 5 = 16807 := by
        calc
          (7 : ZMod 5767723305889) ^ 5 = (7 : ZMod 5767723305889) ^ (2 + 2 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 2 * (7 : ZMod 5767723305889) ^ 2) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 16807 := by rw [fermat_1]; decide
      have fermat_3 : (7 : ZMod 5767723305889) ^ 10 = 282475249 := by
        calc
          (7 : ZMod 5767723305889) ^ 10 = (7 : ZMod 5767723305889) ^ (5 + 5) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 5 * (7 : ZMod 5767723305889) ^ 5 := by rw [pow_add]
          _ = 282475249 := by rw [fermat_2]; decide
      have fermat_4 : (7 : ZMod 5767723305889) ^ 20 = 1582083943575 := by
        calc
          (7 : ZMod 5767723305889) ^ 20 = (7 : ZMod 5767723305889) ^ (10 + 10) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 10 * (7 : ZMod 5767723305889) ^ 10 := by rw [pow_add]
          _ = 1582083943575 := by rw [fermat_3]; decide
      have fermat_5 : (7 : ZMod 5767723305889) ^ 41 = 612985272143 := by
        calc
          (7 : ZMod 5767723305889) ^ 41 = (7 : ZMod 5767723305889) ^ (20 + 20 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 20 * (7 : ZMod 5767723305889) ^ 20) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 612985272143 := by rw [fermat_4]; decide
      have fermat_6 : (7 : ZMod 5767723305889) ^ 83 = 2627669472805 := by
        calc
          (7 : ZMod 5767723305889) ^ 83 = (7 : ZMod 5767723305889) ^ (41 + 41 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 41 * (7 : ZMod 5767723305889) ^ 41) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 2627669472805 := by rw [fermat_5]; decide
      have fermat_7 : (7 : ZMod 5767723305889) ^ 167 = 544597554193 := by
        calc
          (7 : ZMod 5767723305889) ^ 167 = (7 : ZMod 5767723305889) ^ (83 + 83 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 83 * (7 : ZMod 5767723305889) ^ 83) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 544597554193 := by rw [fermat_6]; decide
      have fermat_8 : (7 : ZMod 5767723305889) ^ 335 = 2100915400064 := by
        calc
          (7 : ZMod 5767723305889) ^ 335 = (7 : ZMod 5767723305889) ^ (167 + 167 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 167 * (7 : ZMod 5767723305889) ^ 167) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 2100915400064 := by rw [fermat_7]; decide
      have fermat_9 : (7 : ZMod 5767723305889) ^ 671 = 3530361924295 := by
        calc
          (7 : ZMod 5767723305889) ^ 671 = (7 : ZMod 5767723305889) ^ (335 + 335 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 335 * (7 : ZMod 5767723305889) ^ 335) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 3530361924295 := by rw [fermat_8]; decide
      have fermat_10 : (7 : ZMod 5767723305889) ^ 1342 = 1018417292082 := by
        calc
          (7 : ZMod 5767723305889) ^ 1342 = (7 : ZMod 5767723305889) ^ (671 + 671) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 671 * (7 : ZMod 5767723305889) ^ 671 := by rw [pow_add]
          _ = 1018417292082 := by rw [fermat_9]; decide
      have fermat_11 : (7 : ZMod 5767723305889) ^ 2685 = 3079085392025 := by
        calc
          (7 : ZMod 5767723305889) ^ 2685 = (7 : ZMod 5767723305889) ^ (1342 + 1342 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 1342 * (7 : ZMod 5767723305889) ^ 1342) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 3079085392025 := by rw [fermat_10]; decide
      have fermat_12 : (7 : ZMod 5767723305889) ^ 5371 = 2785331484588 := by
        calc
          (7 : ZMod 5767723305889) ^ 5371 = (7 : ZMod 5767723305889) ^ (2685 + 2685 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 2685 * (7 : ZMod 5767723305889) ^ 2685) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 2785331484588 := by rw [fermat_11]; decide
      have fermat_13 : (7 : ZMod 5767723305889) ^ 10743 = 4821885814881 := by
        calc
          (7 : ZMod 5767723305889) ^ 10743 = (7 : ZMod 5767723305889) ^ (5371 + 5371 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 5371 * (7 : ZMod 5767723305889) ^ 5371) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 4821885814881 := by rw [fermat_12]; decide
      have fermat_14 : (7 : ZMod 5767723305889) ^ 21486 = 174411906748 := by
        calc
          (7 : ZMod 5767723305889) ^ 21486 = (7 : ZMod 5767723305889) ^ (10743 + 10743) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 10743 * (7 : ZMod 5767723305889) ^ 10743 := by rw [pow_add]
          _ = 174411906748 := by rw [fermat_13]; decide
      have fermat_15 : (7 : ZMod 5767723305889) ^ 42972 = 1095743771425 := by
        calc
          (7 : ZMod 5767723305889) ^ 42972 = (7 : ZMod 5767723305889) ^ (21486 + 21486) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 21486 * (7 : ZMod 5767723305889) ^ 21486 := by rw [pow_add]
          _ = 1095743771425 := by rw [fermat_14]; decide
      have fermat_16 : (7 : ZMod 5767723305889) ^ 85945 = 1453503412025 := by
        calc
          (7 : ZMod 5767723305889) ^ 85945 = (7 : ZMod 5767723305889) ^ (42972 + 42972 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 42972 * (7 : ZMod 5767723305889) ^ 42972) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 1453503412025 := by rw [fermat_15]; decide
      have fermat_17 : (7 : ZMod 5767723305889) ^ 171891 = 5559010869422 := by
        calc
          (7 : ZMod 5767723305889) ^ 171891 = (7 : ZMod 5767723305889) ^ (85945 + 85945 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 85945 * (7 : ZMod 5767723305889) ^ 85945) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 5559010869422 := by rw [fermat_16]; decide
      have fermat_18 : (7 : ZMod 5767723305889) ^ 343783 = 1948841012834 := by
        calc
          (7 : ZMod 5767723305889) ^ 343783 = (7 : ZMod 5767723305889) ^ (171891 + 171891 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 171891 * (7 : ZMod 5767723305889) ^ 171891) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 1948841012834 := by rw [fermat_17]; decide
      have fermat_19 : (7 : ZMod 5767723305889) ^ 687566 = 3689750943395 := by
        calc
          (7 : ZMod 5767723305889) ^ 687566 = (7 : ZMod 5767723305889) ^ (343783 + 343783) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 343783 * (7 : ZMod 5767723305889) ^ 343783 := by rw [pow_add]
          _ = 3689750943395 := by rw [fermat_18]; decide
      have fermat_20 : (7 : ZMod 5767723305889) ^ 1375132 = 730233041485 := by
        calc
          (7 : ZMod 5767723305889) ^ 1375132 = (7 : ZMod 5767723305889) ^ (687566 + 687566) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 687566 * (7 : ZMod 5767723305889) ^ 687566 := by rw [pow_add]
          _ = 730233041485 := by rw [fermat_19]; decide
      have fermat_21 : (7 : ZMod 5767723305889) ^ 2750264 = 4923693000667 := by
        calc
          (7 : ZMod 5767723305889) ^ 2750264 = (7 : ZMod 5767723305889) ^ (1375132 + 1375132) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 1375132 * (7 : ZMod 5767723305889) ^ 1375132 := by rw [pow_add]
          _ = 4923693000667 := by rw [fermat_20]; decide
      have fermat_22 : (7 : ZMod 5767723305889) ^ 5500529 = 2499104851723 := by
        calc
          (7 : ZMod 5767723305889) ^ 5500529 = (7 : ZMod 5767723305889) ^ (2750264 + 2750264 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 2750264 * (7 : ZMod 5767723305889) ^ 2750264) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 2499104851723 := by rw [fermat_21]; decide
      have fermat_23 : (7 : ZMod 5767723305889) ^ 11001059 = 795413681663 := by
        calc
          (7 : ZMod 5767723305889) ^ 11001059 = (7 : ZMod 5767723305889) ^ (5500529 + 5500529 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 5500529 * (7 : ZMod 5767723305889) ^ 5500529) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 795413681663 := by rw [fermat_22]; decide
      have fermat_24 : (7 : ZMod 5767723305889) ^ 22002118 = 4482401057725 := by
        calc
          (7 : ZMod 5767723305889) ^ 22002118 = (7 : ZMod 5767723305889) ^ (11001059 + 11001059) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 11001059 * (7 : ZMod 5767723305889) ^ 11001059 := by rw [pow_add]
          _ = 4482401057725 := by rw [fermat_23]; decide
      have fermat_25 : (7 : ZMod 5767723305889) ^ 44004236 = 5613778644487 := by
        calc
          (7 : ZMod 5767723305889) ^ 44004236 = (7 : ZMod 5767723305889) ^ (22002118 + 22002118) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 22002118 * (7 : ZMod 5767723305889) ^ 22002118 := by rw [pow_add]
          _ = 5613778644487 := by rw [fermat_24]; decide
      have fermat_26 : (7 : ZMod 5767723305889) ^ 88008473 = 4041289281557 := by
        calc
          (7 : ZMod 5767723305889) ^ 88008473 = (7 : ZMod 5767723305889) ^ (44004236 + 44004236 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 44004236 * (7 : ZMod 5767723305889) ^ 44004236) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 4041289281557 := by rw [fermat_25]; decide
      have fermat_27 : (7 : ZMod 5767723305889) ^ 176016946 = 2862267162538 := by
        calc
          (7 : ZMod 5767723305889) ^ 176016946 = (7 : ZMod 5767723305889) ^ (88008473 + 88008473) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 88008473 * (7 : ZMod 5767723305889) ^ 88008473 := by rw [pow_add]
          _ = 2862267162538 := by rw [fermat_26]; decide
      have fermat_28 : (7 : ZMod 5767723305889) ^ 352033893 = 5021631186843 := by
        calc
          (7 : ZMod 5767723305889) ^ 352033893 = (7 : ZMod 5767723305889) ^ (176016946 + 176016946 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 176016946 * (7 : ZMod 5767723305889) ^ 176016946) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 5021631186843 := by rw [fermat_27]; decide
      have fermat_29 : (7 : ZMod 5767723305889) ^ 704067786 = 207703267678 := by
        calc
          (7 : ZMod 5767723305889) ^ 704067786 = (7 : ZMod 5767723305889) ^ (352033893 + 352033893) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 352033893 * (7 : ZMod 5767723305889) ^ 352033893 := by rw [pow_add]
          _ = 207703267678 := by rw [fermat_28]; decide
      have fermat_30 : (7 : ZMod 5767723305889) ^ 1408135572 = 413043068950 := by
        calc
          (7 : ZMod 5767723305889) ^ 1408135572 = (7 : ZMod 5767723305889) ^ (704067786 + 704067786) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 704067786 * (7 : ZMod 5767723305889) ^ 704067786 := by rw [pow_add]
          _ = 413043068950 := by rw [fermat_29]; decide
      have fermat_31 : (7 : ZMod 5767723305889) ^ 2816271145 = 3366852013518 := by
        calc
          (7 : ZMod 5767723305889) ^ 2816271145 = (7 : ZMod 5767723305889) ^ (1408135572 + 1408135572 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 1408135572 * (7 : ZMod 5767723305889) ^ 1408135572) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 3366852013518 := by rw [fermat_30]; decide
      have fermat_32 : (7 : ZMod 5767723305889) ^ 5632542290 = 2347388110408 := by
        calc
          (7 : ZMod 5767723305889) ^ 5632542290 = (7 : ZMod 5767723305889) ^ (2816271145 + 2816271145) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 2816271145 * (7 : ZMod 5767723305889) ^ 2816271145 := by rw [pow_add]
          _ = 2347388110408 := by rw [fermat_31]; decide
      have fermat_33 : (7 : ZMod 5767723305889) ^ 11265084581 = 1673568471059 := by
        calc
          (7 : ZMod 5767723305889) ^ 11265084581 = (7 : ZMod 5767723305889) ^ (5632542290 + 5632542290 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 5632542290 * (7 : ZMod 5767723305889) ^ 5632542290) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 1673568471059 := by rw [fermat_32]; decide
      have fermat_34 : (7 : ZMod 5767723305889) ^ 22530169163 = 1436112776911 := by
        calc
          (7 : ZMod 5767723305889) ^ 22530169163 = (7 : ZMod 5767723305889) ^ (11265084581 + 11265084581 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 11265084581 * (7 : ZMod 5767723305889) ^ 11265084581) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 1436112776911 := by rw [fermat_33]; decide
      have fermat_35 : (7 : ZMod 5767723305889) ^ 45060338327 = 3634178574273 := by
        calc
          (7 : ZMod 5767723305889) ^ 45060338327 = (7 : ZMod 5767723305889) ^ (22530169163 + 22530169163 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 22530169163 * (7 : ZMod 5767723305889) ^ 22530169163) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 3634178574273 := by rw [fermat_34]; decide
      have fermat_36 : (7 : ZMod 5767723305889) ^ 90120676654 = 1330761736964 := by
        calc
          (7 : ZMod 5767723305889) ^ 90120676654 = (7 : ZMod 5767723305889) ^ (45060338327 + 45060338327) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 45060338327 * (7 : ZMod 5767723305889) ^ 45060338327 := by rw [pow_add]
          _ = 1330761736964 := by rw [fermat_35]; decide
      have fermat_37 : (7 : ZMod 5767723305889) ^ 180241353309 = 2001303328758 := by
        calc
          (7 : ZMod 5767723305889) ^ 180241353309 = (7 : ZMod 5767723305889) ^ (90120676654 + 90120676654 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 90120676654 * (7 : ZMod 5767723305889) ^ 90120676654) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 2001303328758 := by rw [fermat_36]; decide
      have fermat_38 : (7 : ZMod 5767723305889) ^ 360482706618 = 650941191093 := by
        calc
          (7 : ZMod 5767723305889) ^ 360482706618 = (7 : ZMod 5767723305889) ^ (180241353309 + 180241353309) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 180241353309 * (7 : ZMod 5767723305889) ^ 180241353309 := by rw [pow_add]
          _ = 650941191093 := by rw [fermat_37]; decide
      have fermat_39 : (7 : ZMod 5767723305889) ^ 720965413236 = 2863437206040 := by
        calc
          (7 : ZMod 5767723305889) ^ 720965413236 = (7 : ZMod 5767723305889) ^ (360482706618 + 360482706618) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 360482706618 * (7 : ZMod 5767723305889) ^ 360482706618 := by rw [pow_add]
          _ = 2863437206040 := by rw [fermat_38]; decide
      have fermat_40 : (7 : ZMod 5767723305889) ^ 1441930826472 = 1451322283838 := by
        calc
          (7 : ZMod 5767723305889) ^ 1441930826472 = (7 : ZMod 5767723305889) ^ (720965413236 + 720965413236) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 720965413236 * (7 : ZMod 5767723305889) ^ 720965413236 := by rw [pow_add]
          _ = 1451322283838 := by rw [fermat_39]; decide
      have fermat_41 : (7 : ZMod 5767723305889) ^ 2883861652944 = 5767723305888 := by
        calc
          (7 : ZMod 5767723305889) ^ 2883861652944 = (7 : ZMod 5767723305889) ^ (1441930826472 + 1441930826472) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 1441930826472 * (7 : ZMod 5767723305889) ^ 1441930826472 := by rw [pow_add]
          _ = 5767723305888 := by rw [fermat_40]; decide
      have fermat_42 : (7 : ZMod 5767723305889) ^ 5767723305888 = 1 := by
        calc
          (7 : ZMod 5767723305889) ^ 5767723305888 = (7 : ZMod 5767723305889) ^ (2883861652944 + 2883861652944) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 2883861652944 * (7 : ZMod 5767723305889) ^ 2883861652944 := by rw [pow_add]
          _ = 1 := by rw [fermat_41]; decide
      simpa using fermat_42
  · intro q hq hqd
    have hdvd : q ∣ (([(2, 5), (3, 1), (359, 1), (167355017, 1)] : List FactorBlock).map factorBlockValue).prod := by
      rwa [show (([(2, 5), (3, 1), (359, 1), (167355017, 1)] : List FactorBlock).map factorBlockValue).prod = 5767723305889 - 1 by
        norm_num [factorBlockValue]]
    obtain ⟨b, hb, rfl⟩ := prime_dvd_factorBlocks _ hq (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      · exact prime_free53D_2
      · exact prime_free53D_3
      · exact prime_free53D_359
      · exact prime_free53D_167355017) hdvd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    ·
      have factor_0_0 : (7 : ZMod 5767723305889) ^ 1 = 7 := by norm_num
      have factor_0_1 : (7 : ZMod 5767723305889) ^ 2 = 49 := by
        calc
          (7 : ZMod 5767723305889) ^ 2 = (7 : ZMod 5767723305889) ^ (1 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 1 * (7 : ZMod 5767723305889) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_0_0]; decide
      have factor_0_2 : (7 : ZMod 5767723305889) ^ 5 = 16807 := by
        calc
          (7 : ZMod 5767723305889) ^ 5 = (7 : ZMod 5767723305889) ^ (2 + 2 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 2 * (7 : ZMod 5767723305889) ^ 2) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 16807 := by rw [factor_0_1]; decide
      have factor_0_3 : (7 : ZMod 5767723305889) ^ 10 = 282475249 := by
        calc
          (7 : ZMod 5767723305889) ^ 10 = (7 : ZMod 5767723305889) ^ (5 + 5) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 5 * (7 : ZMod 5767723305889) ^ 5 := by rw [pow_add]
          _ = 282475249 := by rw [factor_0_2]; decide
      have factor_0_4 : (7 : ZMod 5767723305889) ^ 20 = 1582083943575 := by
        calc
          (7 : ZMod 5767723305889) ^ 20 = (7 : ZMod 5767723305889) ^ (10 + 10) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 10 * (7 : ZMod 5767723305889) ^ 10 := by rw [pow_add]
          _ = 1582083943575 := by rw [factor_0_3]; decide
      have factor_0_5 : (7 : ZMod 5767723305889) ^ 41 = 612985272143 := by
        calc
          (7 : ZMod 5767723305889) ^ 41 = (7 : ZMod 5767723305889) ^ (20 + 20 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 20 * (7 : ZMod 5767723305889) ^ 20) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 612985272143 := by rw [factor_0_4]; decide
      have factor_0_6 : (7 : ZMod 5767723305889) ^ 83 = 2627669472805 := by
        calc
          (7 : ZMod 5767723305889) ^ 83 = (7 : ZMod 5767723305889) ^ (41 + 41 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 41 * (7 : ZMod 5767723305889) ^ 41) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 2627669472805 := by rw [factor_0_5]; decide
      have factor_0_7 : (7 : ZMod 5767723305889) ^ 167 = 544597554193 := by
        calc
          (7 : ZMod 5767723305889) ^ 167 = (7 : ZMod 5767723305889) ^ (83 + 83 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 83 * (7 : ZMod 5767723305889) ^ 83) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 544597554193 := by rw [factor_0_6]; decide
      have factor_0_8 : (7 : ZMod 5767723305889) ^ 335 = 2100915400064 := by
        calc
          (7 : ZMod 5767723305889) ^ 335 = (7 : ZMod 5767723305889) ^ (167 + 167 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 167 * (7 : ZMod 5767723305889) ^ 167) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 2100915400064 := by rw [factor_0_7]; decide
      have factor_0_9 : (7 : ZMod 5767723305889) ^ 671 = 3530361924295 := by
        calc
          (7 : ZMod 5767723305889) ^ 671 = (7 : ZMod 5767723305889) ^ (335 + 335 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 335 * (7 : ZMod 5767723305889) ^ 335) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 3530361924295 := by rw [factor_0_8]; decide
      have factor_0_10 : (7 : ZMod 5767723305889) ^ 1342 = 1018417292082 := by
        calc
          (7 : ZMod 5767723305889) ^ 1342 = (7 : ZMod 5767723305889) ^ (671 + 671) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 671 * (7 : ZMod 5767723305889) ^ 671 := by rw [pow_add]
          _ = 1018417292082 := by rw [factor_0_9]; decide
      have factor_0_11 : (7 : ZMod 5767723305889) ^ 2685 = 3079085392025 := by
        calc
          (7 : ZMod 5767723305889) ^ 2685 = (7 : ZMod 5767723305889) ^ (1342 + 1342 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 1342 * (7 : ZMod 5767723305889) ^ 1342) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 3079085392025 := by rw [factor_0_10]; decide
      have factor_0_12 : (7 : ZMod 5767723305889) ^ 5371 = 2785331484588 := by
        calc
          (7 : ZMod 5767723305889) ^ 5371 = (7 : ZMod 5767723305889) ^ (2685 + 2685 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 2685 * (7 : ZMod 5767723305889) ^ 2685) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 2785331484588 := by rw [factor_0_11]; decide
      have factor_0_13 : (7 : ZMod 5767723305889) ^ 10743 = 4821885814881 := by
        calc
          (7 : ZMod 5767723305889) ^ 10743 = (7 : ZMod 5767723305889) ^ (5371 + 5371 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 5371 * (7 : ZMod 5767723305889) ^ 5371) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 4821885814881 := by rw [factor_0_12]; decide
      have factor_0_14 : (7 : ZMod 5767723305889) ^ 21486 = 174411906748 := by
        calc
          (7 : ZMod 5767723305889) ^ 21486 = (7 : ZMod 5767723305889) ^ (10743 + 10743) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 10743 * (7 : ZMod 5767723305889) ^ 10743 := by rw [pow_add]
          _ = 174411906748 := by rw [factor_0_13]; decide
      have factor_0_15 : (7 : ZMod 5767723305889) ^ 42972 = 1095743771425 := by
        calc
          (7 : ZMod 5767723305889) ^ 42972 = (7 : ZMod 5767723305889) ^ (21486 + 21486) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 21486 * (7 : ZMod 5767723305889) ^ 21486 := by rw [pow_add]
          _ = 1095743771425 := by rw [factor_0_14]; decide
      have factor_0_16 : (7 : ZMod 5767723305889) ^ 85945 = 1453503412025 := by
        calc
          (7 : ZMod 5767723305889) ^ 85945 = (7 : ZMod 5767723305889) ^ (42972 + 42972 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 42972 * (7 : ZMod 5767723305889) ^ 42972) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 1453503412025 := by rw [factor_0_15]; decide
      have factor_0_17 : (7 : ZMod 5767723305889) ^ 171891 = 5559010869422 := by
        calc
          (7 : ZMod 5767723305889) ^ 171891 = (7 : ZMod 5767723305889) ^ (85945 + 85945 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 85945 * (7 : ZMod 5767723305889) ^ 85945) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 5559010869422 := by rw [factor_0_16]; decide
      have factor_0_18 : (7 : ZMod 5767723305889) ^ 343783 = 1948841012834 := by
        calc
          (7 : ZMod 5767723305889) ^ 343783 = (7 : ZMod 5767723305889) ^ (171891 + 171891 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 171891 * (7 : ZMod 5767723305889) ^ 171891) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 1948841012834 := by rw [factor_0_17]; decide
      have factor_0_19 : (7 : ZMod 5767723305889) ^ 687566 = 3689750943395 := by
        calc
          (7 : ZMod 5767723305889) ^ 687566 = (7 : ZMod 5767723305889) ^ (343783 + 343783) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 343783 * (7 : ZMod 5767723305889) ^ 343783 := by rw [pow_add]
          _ = 3689750943395 := by rw [factor_0_18]; decide
      have factor_0_20 : (7 : ZMod 5767723305889) ^ 1375132 = 730233041485 := by
        calc
          (7 : ZMod 5767723305889) ^ 1375132 = (7 : ZMod 5767723305889) ^ (687566 + 687566) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 687566 * (7 : ZMod 5767723305889) ^ 687566 := by rw [pow_add]
          _ = 730233041485 := by rw [factor_0_19]; decide
      have factor_0_21 : (7 : ZMod 5767723305889) ^ 2750264 = 4923693000667 := by
        calc
          (7 : ZMod 5767723305889) ^ 2750264 = (7 : ZMod 5767723305889) ^ (1375132 + 1375132) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 1375132 * (7 : ZMod 5767723305889) ^ 1375132 := by rw [pow_add]
          _ = 4923693000667 := by rw [factor_0_20]; decide
      have factor_0_22 : (7 : ZMod 5767723305889) ^ 5500529 = 2499104851723 := by
        calc
          (7 : ZMod 5767723305889) ^ 5500529 = (7 : ZMod 5767723305889) ^ (2750264 + 2750264 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 2750264 * (7 : ZMod 5767723305889) ^ 2750264) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 2499104851723 := by rw [factor_0_21]; decide
      have factor_0_23 : (7 : ZMod 5767723305889) ^ 11001059 = 795413681663 := by
        calc
          (7 : ZMod 5767723305889) ^ 11001059 = (7 : ZMod 5767723305889) ^ (5500529 + 5500529 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 5500529 * (7 : ZMod 5767723305889) ^ 5500529) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 795413681663 := by rw [factor_0_22]; decide
      have factor_0_24 : (7 : ZMod 5767723305889) ^ 22002118 = 4482401057725 := by
        calc
          (7 : ZMod 5767723305889) ^ 22002118 = (7 : ZMod 5767723305889) ^ (11001059 + 11001059) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 11001059 * (7 : ZMod 5767723305889) ^ 11001059 := by rw [pow_add]
          _ = 4482401057725 := by rw [factor_0_23]; decide
      have factor_0_25 : (7 : ZMod 5767723305889) ^ 44004236 = 5613778644487 := by
        calc
          (7 : ZMod 5767723305889) ^ 44004236 = (7 : ZMod 5767723305889) ^ (22002118 + 22002118) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 22002118 * (7 : ZMod 5767723305889) ^ 22002118 := by rw [pow_add]
          _ = 5613778644487 := by rw [factor_0_24]; decide
      have factor_0_26 : (7 : ZMod 5767723305889) ^ 88008473 = 4041289281557 := by
        calc
          (7 : ZMod 5767723305889) ^ 88008473 = (7 : ZMod 5767723305889) ^ (44004236 + 44004236 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 44004236 * (7 : ZMod 5767723305889) ^ 44004236) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 4041289281557 := by rw [factor_0_25]; decide
      have factor_0_27 : (7 : ZMod 5767723305889) ^ 176016946 = 2862267162538 := by
        calc
          (7 : ZMod 5767723305889) ^ 176016946 = (7 : ZMod 5767723305889) ^ (88008473 + 88008473) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 88008473 * (7 : ZMod 5767723305889) ^ 88008473 := by rw [pow_add]
          _ = 2862267162538 := by rw [factor_0_26]; decide
      have factor_0_28 : (7 : ZMod 5767723305889) ^ 352033893 = 5021631186843 := by
        calc
          (7 : ZMod 5767723305889) ^ 352033893 = (7 : ZMod 5767723305889) ^ (176016946 + 176016946 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 176016946 * (7 : ZMod 5767723305889) ^ 176016946) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 5021631186843 := by rw [factor_0_27]; decide
      have factor_0_29 : (7 : ZMod 5767723305889) ^ 704067786 = 207703267678 := by
        calc
          (7 : ZMod 5767723305889) ^ 704067786 = (7 : ZMod 5767723305889) ^ (352033893 + 352033893) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 352033893 * (7 : ZMod 5767723305889) ^ 352033893 := by rw [pow_add]
          _ = 207703267678 := by rw [factor_0_28]; decide
      have factor_0_30 : (7 : ZMod 5767723305889) ^ 1408135572 = 413043068950 := by
        calc
          (7 : ZMod 5767723305889) ^ 1408135572 = (7 : ZMod 5767723305889) ^ (704067786 + 704067786) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 704067786 * (7 : ZMod 5767723305889) ^ 704067786 := by rw [pow_add]
          _ = 413043068950 := by rw [factor_0_29]; decide
      have factor_0_31 : (7 : ZMod 5767723305889) ^ 2816271145 = 3366852013518 := by
        calc
          (7 : ZMod 5767723305889) ^ 2816271145 = (7 : ZMod 5767723305889) ^ (1408135572 + 1408135572 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 1408135572 * (7 : ZMod 5767723305889) ^ 1408135572) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 3366852013518 := by rw [factor_0_30]; decide
      have factor_0_32 : (7 : ZMod 5767723305889) ^ 5632542290 = 2347388110408 := by
        calc
          (7 : ZMod 5767723305889) ^ 5632542290 = (7 : ZMod 5767723305889) ^ (2816271145 + 2816271145) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 2816271145 * (7 : ZMod 5767723305889) ^ 2816271145 := by rw [pow_add]
          _ = 2347388110408 := by rw [factor_0_31]; decide
      have factor_0_33 : (7 : ZMod 5767723305889) ^ 11265084581 = 1673568471059 := by
        calc
          (7 : ZMod 5767723305889) ^ 11265084581 = (7 : ZMod 5767723305889) ^ (5632542290 + 5632542290 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 5632542290 * (7 : ZMod 5767723305889) ^ 5632542290) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 1673568471059 := by rw [factor_0_32]; decide
      have factor_0_34 : (7 : ZMod 5767723305889) ^ 22530169163 = 1436112776911 := by
        calc
          (7 : ZMod 5767723305889) ^ 22530169163 = (7 : ZMod 5767723305889) ^ (11265084581 + 11265084581 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 11265084581 * (7 : ZMod 5767723305889) ^ 11265084581) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 1436112776911 := by rw [factor_0_33]; decide
      have factor_0_35 : (7 : ZMod 5767723305889) ^ 45060338327 = 3634178574273 := by
        calc
          (7 : ZMod 5767723305889) ^ 45060338327 = (7 : ZMod 5767723305889) ^ (22530169163 + 22530169163 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 22530169163 * (7 : ZMod 5767723305889) ^ 22530169163) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 3634178574273 := by rw [factor_0_34]; decide
      have factor_0_36 : (7 : ZMod 5767723305889) ^ 90120676654 = 1330761736964 := by
        calc
          (7 : ZMod 5767723305889) ^ 90120676654 = (7 : ZMod 5767723305889) ^ (45060338327 + 45060338327) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 45060338327 * (7 : ZMod 5767723305889) ^ 45060338327 := by rw [pow_add]
          _ = 1330761736964 := by rw [factor_0_35]; decide
      have factor_0_37 : (7 : ZMod 5767723305889) ^ 180241353309 = 2001303328758 := by
        calc
          (7 : ZMod 5767723305889) ^ 180241353309 = (7 : ZMod 5767723305889) ^ (90120676654 + 90120676654 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 90120676654 * (7 : ZMod 5767723305889) ^ 90120676654) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 2001303328758 := by rw [factor_0_36]; decide
      have factor_0_38 : (7 : ZMod 5767723305889) ^ 360482706618 = 650941191093 := by
        calc
          (7 : ZMod 5767723305889) ^ 360482706618 = (7 : ZMod 5767723305889) ^ (180241353309 + 180241353309) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 180241353309 * (7 : ZMod 5767723305889) ^ 180241353309 := by rw [pow_add]
          _ = 650941191093 := by rw [factor_0_37]; decide
      have factor_0_39 : (7 : ZMod 5767723305889) ^ 720965413236 = 2863437206040 := by
        calc
          (7 : ZMod 5767723305889) ^ 720965413236 = (7 : ZMod 5767723305889) ^ (360482706618 + 360482706618) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 360482706618 * (7 : ZMod 5767723305889) ^ 360482706618 := by rw [pow_add]
          _ = 2863437206040 := by rw [factor_0_38]; decide
      have factor_0_40 : (7 : ZMod 5767723305889) ^ 1441930826472 = 1451322283838 := by
        calc
          (7 : ZMod 5767723305889) ^ 1441930826472 = (7 : ZMod 5767723305889) ^ (720965413236 + 720965413236) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 720965413236 * (7 : ZMod 5767723305889) ^ 720965413236 := by rw [pow_add]
          _ = 1451322283838 := by rw [factor_0_39]; decide
      have factor_0_41 : (7 : ZMod 5767723305889) ^ 2883861652944 = 5767723305888 := by
        calc
          (7 : ZMod 5767723305889) ^ 2883861652944 = (7 : ZMod 5767723305889) ^ (1441930826472 + 1441930826472) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 1441930826472 * (7 : ZMod 5767723305889) ^ 1441930826472 := by rw [pow_add]
          _ = 5767723305888 := by rw [factor_0_40]; decide
      change (7 : ZMod 5767723305889) ^ 2883861652944 ≠ 1
      rw [factor_0_41]
      decide
    ·
      have factor_1_0 : (7 : ZMod 5767723305889) ^ 1 = 7 := by norm_num
      have factor_1_1 : (7 : ZMod 5767723305889) ^ 3 = 343 := by
        calc
          (7 : ZMod 5767723305889) ^ 3 = (7 : ZMod 5767723305889) ^ (1 + 1 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 1 * (7 : ZMod 5767723305889) ^ 1) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_1_0]; decide
      have factor_1_2 : (7 : ZMod 5767723305889) ^ 6 = 117649 := by
        calc
          (7 : ZMod 5767723305889) ^ 6 = (7 : ZMod 5767723305889) ^ (3 + 3) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 3 * (7 : ZMod 5767723305889) ^ 3 := by rw [pow_add]
          _ = 117649 := by rw [factor_1_1]; decide
      have factor_1_3 : (7 : ZMod 5767723305889) ^ 13 = 96889010407 := by
        calc
          (7 : ZMod 5767723305889) ^ 13 = (7 : ZMod 5767723305889) ^ (6 + 6 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 6 * (7 : ZMod 5767723305889) ^ 6) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 96889010407 := by rw [factor_1_2]; decide
      have factor_1_4 : (7 : ZMod 5767723305889) ^ 27 = 2765513178792 := by
        calc
          (7 : ZMod 5767723305889) ^ 27 = (7 : ZMod 5767723305889) ^ (13 + 13 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 13 * (7 : ZMod 5767723305889) ^ 13) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 2765513178792 := by rw [factor_1_3]; decide
      have factor_1_5 : (7 : ZMod 5767723305889) ^ 55 = 1150099824847 := by
        calc
          (7 : ZMod 5767723305889) ^ 55 = (7 : ZMod 5767723305889) ^ (27 + 27 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 27 * (7 : ZMod 5767723305889) ^ 27) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 1150099824847 := by rw [factor_1_4]; decide
      have factor_1_6 : (7 : ZMod 5767723305889) ^ 111 = 78236352731 := by
        calc
          (7 : ZMod 5767723305889) ^ 111 = (7 : ZMod 5767723305889) ^ (55 + 55 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 55 * (7 : ZMod 5767723305889) ^ 55) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 78236352731 := by rw [factor_1_5]; decide
      have factor_1_7 : (7 : ZMod 5767723305889) ^ 223 = 210615471895 := by
        calc
          (7 : ZMod 5767723305889) ^ 223 = (7 : ZMod 5767723305889) ^ (111 + 111 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 111 * (7 : ZMod 5767723305889) ^ 111) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 210615471895 := by rw [factor_1_6]; decide
      have factor_1_8 : (7 : ZMod 5767723305889) ^ 447 = 3797077170159 := by
        calc
          (7 : ZMod 5767723305889) ^ 447 = (7 : ZMod 5767723305889) ^ (223 + 223 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 223 * (7 : ZMod 5767723305889) ^ 223) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 3797077170159 := by rw [factor_1_7]; decide
      have factor_1_9 : (7 : ZMod 5767723305889) ^ 895 = 2235947311806 := by
        calc
          (7 : ZMod 5767723305889) ^ 895 = (7 : ZMod 5767723305889) ^ (447 + 447 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 447 * (7 : ZMod 5767723305889) ^ 447) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 2235947311806 := by rw [factor_1_8]; decide
      have factor_1_10 : (7 : ZMod 5767723305889) ^ 1790 = 333912200306 := by
        calc
          (7 : ZMod 5767723305889) ^ 1790 = (7 : ZMod 5767723305889) ^ (895 + 895) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 895 * (7 : ZMod 5767723305889) ^ 895 := by rw [pow_add]
          _ = 333912200306 := by rw [factor_1_9]; decide
      have factor_1_11 : (7 : ZMod 5767723305889) ^ 3581 = 4389517121408 := by
        calc
          (7 : ZMod 5767723305889) ^ 3581 = (7 : ZMod 5767723305889) ^ (1790 + 1790 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 1790 * (7 : ZMod 5767723305889) ^ 1790) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 4389517121408 := by rw [factor_1_10]; decide
      have factor_1_12 : (7 : ZMod 5767723305889) ^ 7162 = 3526777704829 := by
        calc
          (7 : ZMod 5767723305889) ^ 7162 = (7 : ZMod 5767723305889) ^ (3581 + 3581) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 3581 * (7 : ZMod 5767723305889) ^ 3581 := by rw [pow_add]
          _ = 3526777704829 := by rw [factor_1_11]; decide
      have factor_1_13 : (7 : ZMod 5767723305889) ^ 14324 = 2567528860708 := by
        calc
          (7 : ZMod 5767723305889) ^ 14324 = (7 : ZMod 5767723305889) ^ (7162 + 7162) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 7162 * (7 : ZMod 5767723305889) ^ 7162 := by rw [pow_add]
          _ = 2567528860708 := by rw [factor_1_12]; decide
      have factor_1_14 : (7 : ZMod 5767723305889) ^ 28648 = 2129365799783 := by
        calc
          (7 : ZMod 5767723305889) ^ 28648 = (7 : ZMod 5767723305889) ^ (14324 + 14324) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 14324 * (7 : ZMod 5767723305889) ^ 14324 := by rw [pow_add]
          _ = 2129365799783 := by rw [factor_1_13]; decide
      have factor_1_15 : (7 : ZMod 5767723305889) ^ 57297 = 5068601834603 := by
        calc
          (7 : ZMod 5767723305889) ^ 57297 = (7 : ZMod 5767723305889) ^ (28648 + 28648 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 28648 * (7 : ZMod 5767723305889) ^ 28648) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 5068601834603 := by rw [factor_1_14]; decide
      have factor_1_16 : (7 : ZMod 5767723305889) ^ 114594 = 3024564818781 := by
        calc
          (7 : ZMod 5767723305889) ^ 114594 = (7 : ZMod 5767723305889) ^ (57297 + 57297) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 57297 * (7 : ZMod 5767723305889) ^ 57297 := by rw [pow_add]
          _ = 3024564818781 := by rw [factor_1_15]; decide
      have factor_1_17 : (7 : ZMod 5767723305889) ^ 229188 = 4882526821383 := by
        calc
          (7 : ZMod 5767723305889) ^ 229188 = (7 : ZMod 5767723305889) ^ (114594 + 114594) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 114594 * (7 : ZMod 5767723305889) ^ 114594 := by rw [pow_add]
          _ = 4882526821383 := by rw [factor_1_16]; decide
      have factor_1_18 : (7 : ZMod 5767723305889) ^ 458377 = 5197864893595 := by
        calc
          (7 : ZMod 5767723305889) ^ 458377 = (7 : ZMod 5767723305889) ^ (229188 + 229188 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 229188 * (7 : ZMod 5767723305889) ^ 229188) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 5197864893595 := by rw [factor_1_17]; decide
      have factor_1_19 : (7 : ZMod 5767723305889) ^ 916754 = 3592090135737 := by
        calc
          (7 : ZMod 5767723305889) ^ 916754 = (7 : ZMod 5767723305889) ^ (458377 + 458377) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 458377 * (7 : ZMod 5767723305889) ^ 458377 := by rw [pow_add]
          _ = 3592090135737 := by rw [factor_1_18]; decide
      have factor_1_20 : (7 : ZMod 5767723305889) ^ 1833509 = 4289090484412 := by
        calc
          (7 : ZMod 5767723305889) ^ 1833509 = (7 : ZMod 5767723305889) ^ (916754 + 916754 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 916754 * (7 : ZMod 5767723305889) ^ 916754) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 4289090484412 := by rw [factor_1_19]; decide
      have factor_1_21 : (7 : ZMod 5767723305889) ^ 3667019 = 4268941071567 := by
        calc
          (7 : ZMod 5767723305889) ^ 3667019 = (7 : ZMod 5767723305889) ^ (1833509 + 1833509 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 1833509 * (7 : ZMod 5767723305889) ^ 1833509) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 4268941071567 := by rw [factor_1_20]; decide
      have factor_1_22 : (7 : ZMod 5767723305889) ^ 7334039 = 3295494866757 := by
        calc
          (7 : ZMod 5767723305889) ^ 7334039 = (7 : ZMod 5767723305889) ^ (3667019 + 3667019 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 3667019 * (7 : ZMod 5767723305889) ^ 3667019) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 3295494866757 := by rw [factor_1_21]; decide
      have factor_1_23 : (7 : ZMod 5767723305889) ^ 14668078 = 1256737813019 := by
        calc
          (7 : ZMod 5767723305889) ^ 14668078 = (7 : ZMod 5767723305889) ^ (7334039 + 7334039) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 7334039 * (7 : ZMod 5767723305889) ^ 7334039 := by rw [pow_add]
          _ = 1256737813019 := by rw [factor_1_22]; decide
      have factor_1_24 : (7 : ZMod 5767723305889) ^ 29336157 = 5364338251526 := by
        calc
          (7 : ZMod 5767723305889) ^ 29336157 = (7 : ZMod 5767723305889) ^ (14668078 + 14668078 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 14668078 * (7 : ZMod 5767723305889) ^ 14668078) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 5364338251526 := by rw [factor_1_23]; decide
      have factor_1_25 : (7 : ZMod 5767723305889) ^ 58672315 = 3969951368124 := by
        calc
          (7 : ZMod 5767723305889) ^ 58672315 = (7 : ZMod 5767723305889) ^ (29336157 + 29336157 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 29336157 * (7 : ZMod 5767723305889) ^ 29336157) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 3969951368124 := by rw [factor_1_24]; decide
      have factor_1_26 : (7 : ZMod 5767723305889) ^ 117344631 = 1842609403301 := by
        calc
          (7 : ZMod 5767723305889) ^ 117344631 = (7 : ZMod 5767723305889) ^ (58672315 + 58672315 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 58672315 * (7 : ZMod 5767723305889) ^ 58672315) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 1842609403301 := by rw [factor_1_25]; decide
      have factor_1_27 : (7 : ZMod 5767723305889) ^ 234689262 = 3499729259799 := by
        calc
          (7 : ZMod 5767723305889) ^ 234689262 = (7 : ZMod 5767723305889) ^ (117344631 + 117344631) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 117344631 * (7 : ZMod 5767723305889) ^ 117344631 := by rw [pow_add]
          _ = 3499729259799 := by rw [factor_1_26]; decide
      have factor_1_28 : (7 : ZMod 5767723305889) ^ 469378524 = 4948219271780 := by
        calc
          (7 : ZMod 5767723305889) ^ 469378524 = (7 : ZMod 5767723305889) ^ (234689262 + 234689262) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 234689262 * (7 : ZMod 5767723305889) ^ 234689262 := by rw [pow_add]
          _ = 4948219271780 := by rw [factor_1_27]; decide
      have factor_1_29 : (7 : ZMod 5767723305889) ^ 938757048 = 5156139765312 := by
        calc
          (7 : ZMod 5767723305889) ^ 938757048 = (7 : ZMod 5767723305889) ^ (469378524 + 469378524) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 469378524 * (7 : ZMod 5767723305889) ^ 469378524 := by rw [pow_add]
          _ = 5156139765312 := by rw [factor_1_28]; decide
      have factor_1_30 : (7 : ZMod 5767723305889) ^ 1877514096 = 2105669657283 := by
        calc
          (7 : ZMod 5767723305889) ^ 1877514096 = (7 : ZMod 5767723305889) ^ (938757048 + 938757048) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 938757048 * (7 : ZMod 5767723305889) ^ 938757048 := by rw [pow_add]
          _ = 2105669657283 := by rw [factor_1_29]; decide
      have factor_1_31 : (7 : ZMod 5767723305889) ^ 3755028193 = 598196068045 := by
        calc
          (7 : ZMod 5767723305889) ^ 3755028193 = (7 : ZMod 5767723305889) ^ (1877514096 + 1877514096 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 1877514096 * (7 : ZMod 5767723305889) ^ 1877514096) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 598196068045 := by rw [factor_1_30]; decide
      have factor_1_32 : (7 : ZMod 5767723305889) ^ 7510056387 = 5441062642184 := by
        calc
          (7 : ZMod 5767723305889) ^ 7510056387 = (7 : ZMod 5767723305889) ^ (3755028193 + 3755028193 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 3755028193 * (7 : ZMod 5767723305889) ^ 3755028193) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 5441062642184 := by rw [factor_1_31]; decide
      have factor_1_33 : (7 : ZMod 5767723305889) ^ 15020112775 = 4439088829345 := by
        calc
          (7 : ZMod 5767723305889) ^ 15020112775 = (7 : ZMod 5767723305889) ^ (7510056387 + 7510056387 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 7510056387 * (7 : ZMod 5767723305889) ^ 7510056387) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 4439088829345 := by rw [factor_1_32]; decide
      have factor_1_34 : (7 : ZMod 5767723305889) ^ 30040225551 = 4880580775204 := by
        calc
          (7 : ZMod 5767723305889) ^ 30040225551 = (7 : ZMod 5767723305889) ^ (15020112775 + 15020112775 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 15020112775 * (7 : ZMod 5767723305889) ^ 15020112775) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 4880580775204 := by rw [factor_1_33]; decide
      have factor_1_35 : (7 : ZMod 5767723305889) ^ 60080451103 = 4849132627982 := by
        calc
          (7 : ZMod 5767723305889) ^ 60080451103 = (7 : ZMod 5767723305889) ^ (30040225551 + 30040225551 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 30040225551 * (7 : ZMod 5767723305889) ^ 30040225551) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 4849132627982 := by rw [factor_1_34]; decide
      have factor_1_36 : (7 : ZMod 5767723305889) ^ 120160902206 = 5546093772020 := by
        calc
          (7 : ZMod 5767723305889) ^ 120160902206 = (7 : ZMod 5767723305889) ^ (60080451103 + 60080451103) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 60080451103 * (7 : ZMod 5767723305889) ^ 60080451103 := by rw [pow_add]
          _ = 5546093772020 := by rw [factor_1_35]; decide
      have factor_1_37 : (7 : ZMod 5767723305889) ^ 240321804412 = 1526038363831 := by
        calc
          (7 : ZMod 5767723305889) ^ 240321804412 = (7 : ZMod 5767723305889) ^ (120160902206 + 120160902206) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 120160902206 * (7 : ZMod 5767723305889) ^ 120160902206 := by rw [pow_add]
          _ = 1526038363831 := by rw [factor_1_36]; decide
      have factor_1_38 : (7 : ZMod 5767723305889) ^ 480643608824 = 5078751800865 := by
        calc
          (7 : ZMod 5767723305889) ^ 480643608824 = (7 : ZMod 5767723305889) ^ (240321804412 + 240321804412) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 240321804412 * (7 : ZMod 5767723305889) ^ 240321804412 := by rw [pow_add]
          _ = 5078751800865 := by rw [factor_1_37]; decide
      have factor_1_39 : (7 : ZMod 5767723305889) ^ 961287217648 = 2061964893161 := by
        calc
          (7 : ZMod 5767723305889) ^ 961287217648 = (7 : ZMod 5767723305889) ^ (480643608824 + 480643608824) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 480643608824 * (7 : ZMod 5767723305889) ^ 480643608824 := by rw [pow_add]
          _ = 2061964893161 := by rw [factor_1_38]; decide
      have factor_1_40 : (7 : ZMod 5767723305889) ^ 1922574435296 = 2061964893160 := by
        calc
          (7 : ZMod 5767723305889) ^ 1922574435296 = (7 : ZMod 5767723305889) ^ (961287217648 + 961287217648) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 961287217648 * (7 : ZMod 5767723305889) ^ 961287217648 := by rw [pow_add]
          _ = 2061964893160 := by rw [factor_1_39]; decide
      change (7 : ZMod 5767723305889) ^ 1922574435296 ≠ 1
      rw [factor_1_40]
      decide
    ·
      have factor_2_0 : (7 : ZMod 5767723305889) ^ 1 = 7 := by norm_num
      have factor_2_1 : (7 : ZMod 5767723305889) ^ 3 = 343 := by
        calc
          (7 : ZMod 5767723305889) ^ 3 = (7 : ZMod 5767723305889) ^ (1 + 1 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 1 * (7 : ZMod 5767723305889) ^ 1) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 343 := by rw [factor_2_0]; decide
      have factor_2_2 : (7 : ZMod 5767723305889) ^ 7 = 823543 := by
        calc
          (7 : ZMod 5767723305889) ^ 7 = (7 : ZMod 5767723305889) ^ (3 + 3 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 3 * (7 : ZMod 5767723305889) ^ 3) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 823543 := by rw [factor_2_1]; decide
      have factor_2_3 : (7 : ZMod 5767723305889) ^ 14 = 678223072849 := by
        calc
          (7 : ZMod 5767723305889) ^ 14 = (7 : ZMod 5767723305889) ^ (7 + 7) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 7 * (7 : ZMod 5767723305889) ^ 7 := by rw [pow_add]
          _ = 678223072849 := by rw [factor_2_2]; decide
      have factor_2_4 : (7 : ZMod 5767723305889) ^ 29 = 2852509725361 := by
        calc
          (7 : ZMod 5767723305889) ^ 29 = (7 : ZMod 5767723305889) ^ (14 + 14 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 14 * (7 : ZMod 5767723305889) ^ 14) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 2852509725361 := by rw [factor_2_3]; decide
      have factor_2_5 : (7 : ZMod 5767723305889) ^ 59 = 4417939242705 := by
        calc
          (7 : ZMod 5767723305889) ^ 59 = (7 : ZMod 5767723305889) ^ (29 + 29 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 29 * (7 : ZMod 5767723305889) ^ 29) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 4417939242705 := by rw [factor_2_4]; decide
      have factor_2_6 : (7 : ZMod 5767723305889) ^ 119 = 4112832725287 := by
        calc
          (7 : ZMod 5767723305889) ^ 119 = (7 : ZMod 5767723305889) ^ (59 + 59 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 59 * (7 : ZMod 5767723305889) ^ 59) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 4112832725287 := by rw [factor_2_5]; decide
      have factor_2_7 : (7 : ZMod 5767723305889) ^ 239 = 4593931766450 := by
        calc
          (7 : ZMod 5767723305889) ^ 239 = (7 : ZMod 5767723305889) ^ (119 + 119 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 119 * (7 : ZMod 5767723305889) ^ 119) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 4593931766450 := by rw [factor_2_6]; decide
      have factor_2_8 : (7 : ZMod 5767723305889) ^ 478 = 2011524951199 := by
        calc
          (7 : ZMod 5767723305889) ^ 478 = (7 : ZMod 5767723305889) ^ (239 + 239) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 239 * (7 : ZMod 5767723305889) ^ 239 := by rw [pow_add]
          _ = 2011524951199 := by rw [factor_2_7]; decide
      have factor_2_9 : (7 : ZMod 5767723305889) ^ 957 = 2910477955051 := by
        calc
          (7 : ZMod 5767723305889) ^ 957 = (7 : ZMod 5767723305889) ^ (478 + 478 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 478 * (7 : ZMod 5767723305889) ^ 478) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 2910477955051 := by rw [factor_2_8]; decide
      have factor_2_10 : (7 : ZMod 5767723305889) ^ 1915 = 481334133490 := by
        calc
          (7 : ZMod 5767723305889) ^ 1915 = (7 : ZMod 5767723305889) ^ (957 + 957 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 957 * (7 : ZMod 5767723305889) ^ 957) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 481334133490 := by rw [factor_2_9]; decide
      have factor_2_11 : (7 : ZMod 5767723305889) ^ 3830 = 820764540524 := by
        calc
          (7 : ZMod 5767723305889) ^ 3830 = (7 : ZMod 5767723305889) ^ (1915 + 1915) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 1915 * (7 : ZMod 5767723305889) ^ 1915 := by rw [pow_add]
          _ = 820764540524 := by rw [factor_2_10]; decide
      have factor_2_12 : (7 : ZMod 5767723305889) ^ 7660 = 3507415937751 := by
        calc
          (7 : ZMod 5767723305889) ^ 7660 = (7 : ZMod 5767723305889) ^ (3830 + 3830) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 3830 * (7 : ZMod 5767723305889) ^ 3830 := by rw [pow_add]
          _ = 3507415937751 := by rw [factor_2_11]; decide
      have factor_2_13 : (7 : ZMod 5767723305889) ^ 15321 = 1956867794288 := by
        calc
          (7 : ZMod 5767723305889) ^ 15321 = (7 : ZMod 5767723305889) ^ (7660 + 7660 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 7660 * (7 : ZMod 5767723305889) ^ 7660) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 1956867794288 := by rw [factor_2_12]; decide
      have factor_2_14 : (7 : ZMod 5767723305889) ^ 30643 = 3879106989191 := by
        calc
          (7 : ZMod 5767723305889) ^ 30643 = (7 : ZMod 5767723305889) ^ (15321 + 15321 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 15321 * (7 : ZMod 5767723305889) ^ 15321) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 3879106989191 := by rw [factor_2_13]; decide
      have factor_2_15 : (7 : ZMod 5767723305889) ^ 61287 = 4530826003737 := by
        calc
          (7 : ZMod 5767723305889) ^ 61287 = (7 : ZMod 5767723305889) ^ (30643 + 30643 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 30643 * (7 : ZMod 5767723305889) ^ 30643) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 4530826003737 := by rw [factor_2_14]; decide
      have factor_2_16 : (7 : ZMod 5767723305889) ^ 122574 = 5668384934891 := by
        calc
          (7 : ZMod 5767723305889) ^ 122574 = (7 : ZMod 5767723305889) ^ (61287 + 61287) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 61287 * (7 : ZMod 5767723305889) ^ 61287 := by rw [pow_add]
          _ = 5668384934891 := by rw [factor_2_15]; decide
      have factor_2_17 : (7 : ZMod 5767723305889) ^ 245148 = 5246573872694 := by
        calc
          (7 : ZMod 5767723305889) ^ 245148 = (7 : ZMod 5767723305889) ^ (122574 + 122574) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 122574 * (7 : ZMod 5767723305889) ^ 122574 := by rw [pow_add]
          _ = 5246573872694 := by rw [factor_2_16]; decide
      have factor_2_18 : (7 : ZMod 5767723305889) ^ 490297 = 4381990186359 := by
        calc
          (7 : ZMod 5767723305889) ^ 490297 = (7 : ZMod 5767723305889) ^ (245148 + 245148 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 245148 * (7 : ZMod 5767723305889) ^ 245148) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 4381990186359 := by rw [factor_2_17]; decide
      have factor_2_19 : (7 : ZMod 5767723305889) ^ 980595 = 1140591613704 := by
        calc
          (7 : ZMod 5767723305889) ^ 980595 = (7 : ZMod 5767723305889) ^ (490297 + 490297 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 490297 * (7 : ZMod 5767723305889) ^ 490297) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 1140591613704 := by rw [factor_2_18]; decide
      have factor_2_20 : (7 : ZMod 5767723305889) ^ 1961191 = 2706270353563 := by
        calc
          (7 : ZMod 5767723305889) ^ 1961191 = (7 : ZMod 5767723305889) ^ (980595 + 980595 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 980595 * (7 : ZMod 5767723305889) ^ 980595) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 2706270353563 := by rw [factor_2_19]; decide
      have factor_2_21 : (7 : ZMod 5767723305889) ^ 3922383 = 2839936096418 := by
        calc
          (7 : ZMod 5767723305889) ^ 3922383 = (7 : ZMod 5767723305889) ^ (1961191 + 1961191 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 1961191 * (7 : ZMod 5767723305889) ^ 1961191) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 2839936096418 := by rw [factor_2_20]; decide
      have factor_2_22 : (7 : ZMod 5767723305889) ^ 7844766 = 692117574042 := by
        calc
          (7 : ZMod 5767723305889) ^ 7844766 = (7 : ZMod 5767723305889) ^ (3922383 + 3922383) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 3922383 * (7 : ZMod 5767723305889) ^ 3922383 := by rw [pow_add]
          _ = 692117574042 := by rw [factor_2_21]; decide
      have factor_2_23 : (7 : ZMod 5767723305889) ^ 15689532 = 147428379744 := by
        calc
          (7 : ZMod 5767723305889) ^ 15689532 = (7 : ZMod 5767723305889) ^ (7844766 + 7844766) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 7844766 * (7 : ZMod 5767723305889) ^ 7844766 := by rw [pow_add]
          _ = 147428379744 := by rw [factor_2_22]; decide
      have factor_2_24 : (7 : ZMod 5767723305889) ^ 31379065 = 1141070615207 := by
        calc
          (7 : ZMod 5767723305889) ^ 31379065 = (7 : ZMod 5767723305889) ^ (15689532 + 15689532 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 15689532 * (7 : ZMod 5767723305889) ^ 15689532) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 1141070615207 := by rw [factor_2_23]; decide
      have factor_2_25 : (7 : ZMod 5767723305889) ^ 62758131 = 2467262541926 := by
        calc
          (7 : ZMod 5767723305889) ^ 62758131 = (7 : ZMod 5767723305889) ^ (31379065 + 31379065 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 31379065 * (7 : ZMod 5767723305889) ^ 31379065) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 2467262541926 := by rw [factor_2_24]; decide
      have factor_2_26 : (7 : ZMod 5767723305889) ^ 125516262 = 2750362724553 := by
        calc
          (7 : ZMod 5767723305889) ^ 125516262 = (7 : ZMod 5767723305889) ^ (62758131 + 62758131) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 62758131 * (7 : ZMod 5767723305889) ^ 62758131 := by rw [pow_add]
          _ = 2750362724553 := by rw [factor_2_25]; decide
      have factor_2_27 : (7 : ZMod 5767723305889) ^ 251032525 = 2419100826097 := by
        calc
          (7 : ZMod 5767723305889) ^ 251032525 = (7 : ZMod 5767723305889) ^ (125516262 + 125516262 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 125516262 * (7 : ZMod 5767723305889) ^ 125516262) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 2419100826097 := by rw [factor_2_26]; decide
      have factor_2_28 : (7 : ZMod 5767723305889) ^ 502065051 = 4582805132267 := by
        calc
          (7 : ZMod 5767723305889) ^ 502065051 = (7 : ZMod 5767723305889) ^ (251032525 + 251032525 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 251032525 * (7 : ZMod 5767723305889) ^ 251032525) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 4582805132267 := by rw [factor_2_27]; decide
      have factor_2_29 : (7 : ZMod 5767723305889) ^ 1004130102 = 3854035960847 := by
        calc
          (7 : ZMod 5767723305889) ^ 1004130102 = (7 : ZMod 5767723305889) ^ (502065051 + 502065051) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 502065051 * (7 : ZMod 5767723305889) ^ 502065051 := by rw [pow_add]
          _ = 3854035960847 := by rw [factor_2_28]; decide
      have factor_2_30 : (7 : ZMod 5767723305889) ^ 2008260204 = 5394256462345 := by
        calc
          (7 : ZMod 5767723305889) ^ 2008260204 = (7 : ZMod 5767723305889) ^ (1004130102 + 1004130102) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 1004130102 * (7 : ZMod 5767723305889) ^ 1004130102 := by rw [pow_add]
          _ = 5394256462345 := by rw [factor_2_29]; decide
      have factor_2_31 : (7 : ZMod 5767723305889) ^ 4016520408 = 1289294610180 := by
        calc
          (7 : ZMod 5767723305889) ^ 4016520408 = (7 : ZMod 5767723305889) ^ (2008260204 + 2008260204) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 2008260204 * (7 : ZMod 5767723305889) ^ 2008260204 := by rw [pow_add]
          _ = 1289294610180 := by rw [factor_2_30]; decide
      have factor_2_32 : (7 : ZMod 5767723305889) ^ 8033040816 = 2918842407647 := by
        calc
          (7 : ZMod 5767723305889) ^ 8033040816 = (7 : ZMod 5767723305889) ^ (4016520408 + 4016520408) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 4016520408 * (7 : ZMod 5767723305889) ^ 4016520408 := by rw [pow_add]
          _ = 2918842407647 := by rw [factor_2_31]; decide
      have factor_2_33 : (7 : ZMod 5767723305889) ^ 16066081632 = 2946759745776 := by
        calc
          (7 : ZMod 5767723305889) ^ 16066081632 = (7 : ZMod 5767723305889) ^ (8033040816 + 8033040816) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 8033040816 * (7 : ZMod 5767723305889) ^ 8033040816 := by rw [pow_add]
          _ = 2946759745776 := by rw [factor_2_32]; decide
      change (7 : ZMod 5767723305889) ^ 16066081632 ≠ 1
      rw [factor_2_33]
      decide
    ·
      have factor_3_0 : (7 : ZMod 5767723305889) ^ 1 = 7 := by norm_num
      have factor_3_1 : (7 : ZMod 5767723305889) ^ 2 = 49 := by
        calc
          (7 : ZMod 5767723305889) ^ 2 = (7 : ZMod 5767723305889) ^ (1 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 1 * (7 : ZMod 5767723305889) ^ 1 := by rw [pow_add]
          _ = 49 := by rw [factor_3_0]; decide
      have factor_3_2 : (7 : ZMod 5767723305889) ^ 4 = 2401 := by
        calc
          (7 : ZMod 5767723305889) ^ 4 = (7 : ZMod 5767723305889) ^ (2 + 2) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 2 * (7 : ZMod 5767723305889) ^ 2 := by rw [pow_add]
          _ = 2401 := by rw [factor_3_1]; decide
      have factor_3_3 : (7 : ZMod 5767723305889) ^ 8 = 5764801 := by
        calc
          (7 : ZMod 5767723305889) ^ 8 = (7 : ZMod 5767723305889) ^ (4 + 4) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 4 * (7 : ZMod 5767723305889) ^ 4 := by rw [pow_add]
          _ = 5764801 := by rw [factor_3_2]; decide
      have factor_3_4 : (7 : ZMod 5767723305889) ^ 16 = 4394314040156 := by
        calc
          (7 : ZMod 5767723305889) ^ 16 = (7 : ZMod 5767723305889) ^ (8 + 8) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 8 * (7 : ZMod 5767723305889) ^ 8 := by rw [pow_add]
          _ = 4394314040156 := by rw [factor_3_3]; decide
      have factor_3_5 : (7 : ZMod 5767723305889) ^ 33 = 2588286501518 := by
        calc
          (7 : ZMod 5767723305889) ^ 33 = (7 : ZMod 5767723305889) ^ (16 + 16 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 16 * (7 : ZMod 5767723305889) ^ 16) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 2588286501518 := by rw [factor_3_4]; decide
      have factor_3_6 : (7 : ZMod 5767723305889) ^ 67 = 4762470969405 := by
        calc
          (7 : ZMod 5767723305889) ^ 67 = (7 : ZMod 5767723305889) ^ (33 + 33 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 33 * (7 : ZMod 5767723305889) ^ 33) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 4762470969405 := by rw [factor_3_5]; decide
      have factor_3_7 : (7 : ZMod 5767723305889) ^ 134 = 5394378172929 := by
        calc
          (7 : ZMod 5767723305889) ^ 134 = (7 : ZMod 5767723305889) ^ (67 + 67) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 67 * (7 : ZMod 5767723305889) ^ 67 := by rw [pow_add]
          _ = 5394378172929 := by rw [factor_3_6]; decide
      have factor_3_8 : (7 : ZMod 5767723305889) ^ 269 = 3434257087426 := by
        calc
          (7 : ZMod 5767723305889) ^ 269 = (7 : ZMod 5767723305889) ^ (134 + 134 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 134 * (7 : ZMod 5767723305889) ^ 134) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 3434257087426 := by rw [factor_3_7]; decide
      have factor_3_9 : (7 : ZMod 5767723305889) ^ 538 = 4691297965881 := by
        calc
          (7 : ZMod 5767723305889) ^ 538 = (7 : ZMod 5767723305889) ^ (269 + 269) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 269 * (7 : ZMod 5767723305889) ^ 269 := by rw [pow_add]
          _ = 4691297965881 := by rw [factor_3_8]; decide
      have factor_3_10 : (7 : ZMod 5767723305889) ^ 1077 = 1075921475829 := by
        calc
          (7 : ZMod 5767723305889) ^ 1077 = (7 : ZMod 5767723305889) ^ (538 + 538 + 1) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = ((7 : ZMod 5767723305889) ^ 538 * (7 : ZMod 5767723305889) ^ 538) * (7 : ZMod 5767723305889) := by rw [pow_succ, pow_add]
          _ = 1075921475829 := by rw [factor_3_9]; decide
      have factor_3_11 : (7 : ZMod 5767723305889) ^ 2154 = 3404978666285 := by
        calc
          (7 : ZMod 5767723305889) ^ 2154 = (7 : ZMod 5767723305889) ^ (1077 + 1077) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 1077 * (7 : ZMod 5767723305889) ^ 1077 := by rw [pow_add]
          _ = 3404978666285 := by rw [factor_3_10]; decide
      have factor_3_12 : (7 : ZMod 5767723305889) ^ 4308 = 524500201088 := by
        calc
          (7 : ZMod 5767723305889) ^ 4308 = (7 : ZMod 5767723305889) ^ (2154 + 2154) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 2154 * (7 : ZMod 5767723305889) ^ 2154 := by rw [pow_add]
          _ = 524500201088 := by rw [factor_3_11]; decide
      have factor_3_13 : (7 : ZMod 5767723305889) ^ 8616 = 232586423444 := by
        calc
          (7 : ZMod 5767723305889) ^ 8616 = (7 : ZMod 5767723305889) ^ (4308 + 4308) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 4308 * (7 : ZMod 5767723305889) ^ 4308 := by rw [pow_add]
          _ = 232586423444 := by rw [factor_3_12]; decide
      have factor_3_14 : (7 : ZMod 5767723305889) ^ 17232 = 863688694387 := by
        calc
          (7 : ZMod 5767723305889) ^ 17232 = (7 : ZMod 5767723305889) ^ (8616 + 8616) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 8616 * (7 : ZMod 5767723305889) ^ 8616 := by rw [pow_add]
          _ = 863688694387 := by rw [factor_3_13]; decide
      have factor_3_15 : (7 : ZMod 5767723305889) ^ 34464 = 1817496731715 := by
        calc
          (7 : ZMod 5767723305889) ^ 34464 = (7 : ZMod 5767723305889) ^ (17232 + 17232) := congrArg (fun n : ℕ => (7 : ZMod 5767723305889) ^ n) (by norm_num)
          _ = (7 : ZMod 5767723305889) ^ 17232 * (7 : ZMod 5767723305889) ^ 17232 := by rw [pow_add]
          _ = 1817496731715 := by rw [factor_3_14]; decide
      change (7 : ZMod 5767723305889) ^ 34464 ≠ 1
      rw [factor_3_15]
      decide

private theorem phi_free53D_164249358725037825439199 :
    Nat.totient 164249358725037825439199 = 159749771690029101444864 := by
  rw [← show ((([(67, 1), (79, 1), (5380187, 1), (5767723305889, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439199 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_free53D_67, prime_free53D_79, prime_free53D_5380187,
      prime_free53D_5767723305889]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

private theorem phi_free53D_164249358725037825439200 :
    Nat.totient 164249358725037825439200 = 22352208111977103360000 := by
  rw [← show ((([(2, 5), (3, 3), (5, 2), (7, 2), (11, 1), (13, 1), (17, 1), (19, 1), (23, 1), (29, 1), (31, 1), (37, 1), (41, 1), (43, 1), (47, 1), (53, 1)] : List FactorBlock).map factorBlockValue).prod) = 164249358725037825439200 by
    norm_num [factorBlockValue]]
  rw [totient_factorBlocks]
  · norm_num [factorBlockTotient]
  · simp [prime_free53D_2, prime_free53D_3, prime_free53D_5, prime_free53D_7,
      prime_free53D_11, prime_free53D_13, prime_free53D_17, prime_free53D_19,
      prime_free53D_23, prime_free53D_29, prime_free53D_31, prime_free53D_37,
      prime_free53D_41, prime_free53D_43, prime_free53D_47, prime_free53D_53]
  · norm_num
  · norm_num [factorBlockValue, Function.onFun] <;> decide

/-- An off-diagonal free-position kill at the position two integers before the t=53 modulus. -/
theorem freeKill_53D : certifiedKill 1 164249358725037825439198 82 := by
  norm_num [certifiedKill, windowDiscrepancy, Finset.sum_range_succ,
    phi_free53D_164249358725037825439199, phi_free53D_164249358725037825439200, phi_t53_164249358725037825439201, phi_t53_164249358725037825439202,
    phi_t53_164249358725037825439203, phi_t53_164249358725037825439204, phi_t53_164249358725037825439205, phi_t53_164249358725037825439206,
    phi_t53_164249358725037825439207, phi_t53_164249358725037825439208, phi_t53_164249358725037825439209, phi_t53_164249358725037825439210,
    phi_t53_164249358725037825439211, phi_t53_164249358725037825439212, phi_t53_164249358725037825439213, phi_t53_164249358725037825439214,
    phi_t53_164249358725037825439215, phi_t53_164249358725037825439216, phi_t53_164249358725037825439217, phi_t53_164249358725037825439218,
    phi_t53_164249358725037825439219, phi_t53_164249358725037825439220, phi_t53_164249358725037825439221, phi_t53_164249358725037825439222,
    phi_t53_164249358725037825439223, phi_t53_164249358725037825439224, phi_t53_164249358725037825439225, phi_t53_164249358725037825439226,
    phi_t53_164249358725037825439227, phi_t53_164249358725037825439228, phi_t53_164249358725037825439229, phi_t53_164249358725037825439230,
    phi_t53_164249358725037825439231, phi_t53_164249358725037825439232, phi_t53_164249358725037825439233, phi_t53_164249358725037825439234,
    phi_t53_164249358725037825439235, phi_t53_164249358725037825439236, phi_t53_164249358725037825439237, phi_t53_164249358725037825439238,
    phi_t53_164249358725037825439239, phi_t53_164249358725037825439240, phi_t53_164249358725037825439241, phi_t53_164249358725037825439242,
    phi_t53_164249358725037825439243, phi_t53_164249358725037825439244, phi_t53_164249358725037825439245, phi_t53_164249358725037825439246,
    phi_t53_164249358725037825439247, phi_t53_164249358725037825439248, phi_t53_164249358725037825439249, phi_t53_164249358725037825439250,
    phi_t53_164249358725037825439251, phi_t53_164249358725037825439252, phi_t53_164249358725037825439253, phi_t53_164249358725037825439254,
    phi_t53_164249358725037825439255, phi_t53_164249358725037825439256, phi_t53_164249358725037825439257, phi_t53_164249358725037825439258,
    phi_t53_164249358725037825439259, phi_t53_164249358725037825439260, phi_t53_164249358725037825439261, phi_t53_164249358725037825439262,
    phi_t53_164249358725037825439263, phi_t53_164249358725037825439264, phi_t53_164249358725037825439265, phi_t53_164249358725037825439266,
    phi_t53_164249358725037825439267, phi_t53_164249358725037825439268, phi_t53_164249358725037825439269, phi_t53_164249358725037825439270,
    phi_t53_164249358725037825439271, phi_t53_164249358725037825439272, phi_t53_164249358725037825439273, phi_t53_164249358725037825439274,
    phi_t53_164249358725037825439275, phi_t53_164249358725037825439276, phi_t53_164249358725037825439277, phi_t53_164249358725037825439278,
    phi_t53_164249358725037825439279, phi_t53_164249358725037825439280, phi_t53_164249358725037825439281]

end TotientTailPeriodKiller
end Erdos249257
