import ErdosProblems.Erdos1041.PaperCubicCompletion

/-!
# Cubic connectors from the usual polynomial hypotheses

The fundamental theorem of algebra supplies the root enumeration, with
multiplicities. This adapter exposes the existing polygonal connector under
monicity, degree three, and the open-disc condition alone.

The adapter uses the existing cubic estimates; it introduces no new analytic estimate.
-/

noncomputable section
namespace ErdosProblems.Erdos1041.PaperCubicMonic

open Polynomial Set PaperAnalyticTargets PaperCurve PaperCubicCompletion
open scoped BigOperators

/-- Every monic complex cubic has three root occurrences, including repeats. -/
theorem exists_root_enumeration (p : ℂ[X]) (hm : p.Monic)
    (hd : p.natDegree = 3) : ∃ z : Fin 3 → ℂ, RootEnumeration p z := by
  have hc : p.roots.card = 3 := IsAlgClosed.card_roots_eq_natDegree.trans hd
  obtain ⟨a, b, c, hr⟩ := Multiset.card_eq_three.mp hc
  refine ⟨![a, b, c], ?_⟩
  change p = ∏ i : Fin 3, (X - C (![a, b, c] i))
  rw [(IsAlgClosed.splits p).eq_prod_roots_of_monic hm, hr]
  simp [Fin.prod_univ_three, mul_assoc]

/-- A monic cubic with all roots in the open unit disc has the actual
continuous, rectifiable polygonal connector supplied by the cubic theorem.
Its endpoints are roots, and are distinct when the polynomial is squarefree. -/
theorem monic_cubic_connector (p : ℂ[X]) (hm : p.Monic)
    (hd : p.natDegree = 3) (hz : RootsInOpenUnitDisc p) :
    ∃ a b c : ℂ, p.eval a = 0 ∧ p.eval b = 0 ∧
      Continuous (hub a c b) ∧
      BoundedVariationOn (hub a c b) (Icc (0 : ℝ) 2) ∧
      HubBelow p.eval 1 2 a c b ∧ ConnectedBelow p.eval 1 2 a b ∧
      (Squarefree p → a ≠ b) := by
  obtain ⟨z, hp⟩ := exists_root_enumeration p hm hd
  have hroot (i : Fin 3) : p.eval (z i) = 0 :=
    ((enumeration_facts p z hp).2.2 (z i)).mpr ⟨i, rfl⟩
  obtain ⟨i, j, c, _, hcont, hbv, hhub, hconn, hdistinct⟩ :=
    cubic_paper_complete p z hp (fun i => hz (z i) (hroot i))
  exact ⟨z i, z j, c, hroot i, hroot j, hcont, hbv, hhub, hconn, hdistinct⟩

/-- The squarefree monic cubic satisfies the distinct-connection target
without an assumed factorisation or an analytic supplier. -/
theorem squarefree_monic_cubic_connection (p : ℂ[X]) (hm : p.Monic)
    (hd : p.natDegree = 3) (hz : RootsInOpenUnitDisc p) (hs : Squarefree p) :
    HasDistinctConnection p 1 2 := by
  obtain ⟨a, b, c, ha, hb, _, _, _, hconn, hdistinct⟩ :=
    monic_cubic_connector p hm hd hz
  exact ⟨a, b, hdistinct hs, ha, hb, hconn⟩

end ErdosProblems.Erdos1041.PaperCubicMonic
