/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Logarithmic.Pairing.Coefficient
public import Mei.Algebra.Lie.Graded.Character

/-!
# Character twists of tropical pairings

A character on a coefficient monoid twists the tropical pairing map by
`z^n ∂_m ↦ χ(n) z^(T n) ∂_(S m)`. The resulting graded Lie map intertwines
the coefficient action with `r z^q ↦ r χ(q) z^(T q)`. Vanishing character values
are allowed, as are noninjective exponent maps. The positive degree map retains
its cutoff modulus, giving finite Lie maps and completed BCH maps through the
existing `GradedLieHom` API.

The construction combines `LieHom.ofGradingCharacter` with
`TropicalPairing.gradedLieHom`; the action comparison uses the monomial
derivations of `tropicalVertexCoefficientAction`. The logarithmic action follows
Mandel, *Scattering diagrams, theta functions, and refined tropical curve
counts*, Example 2.1(i), arXiv:1503.06183v5.
-/

public section

noncomputable section

namespace Mei.TropicalPairing

open LogarithmicVectorField _root_.AddMonoidAlgebra

variable {R Γ Λ Γ' Λ' : Type*} [CommRing R]
  [AddCommMonoid Γ] [AddCommMonoid Λ] [AddCommMonoid Γ'] [AddCommMonoid Λ']
  {d : PositiveDegrees Γ} {e : PositiveDegrees Γ'} {ρ : Γ →+ Λ} {ρ' : Γ' →+ Λ'}
  {U : Submodule R (Λ →+ R)}
  (p : TropicalPairing (d := d) (e := e) (ρ := ρ) (ρ' := ρ') U)
  {Q : AddSubmonoid Γ} (hQ : d.monoid ≤ Q) (χ : Multiplicative Q →* R)

include hQ in
private theorem grading_eq_bot_outside {n : Γ} (hn : n ∉ Q) :
    tropicalSubalgebraGrading ρ U d n = ⊥ :=
  IsPositiveGrading.eq_bot n (Or.inl (fun hn' => hn (hQ hn')))

/-- A tropical pairing twisted by a character on the coefficient monoid.
The Lie map has the original positive degree map and its original cutoff modulus. -/
def twistedGradedLieHom :
    GradedLieHom p.degreeMap (tropicalSubalgebraGrading ρ U d)
      (tropicalVertexGrading (R := R) e ρ') := by
  classical
  let f := LieHom.ofGradingCharacter (tropicalSubalgebraGrading ρ U d) Q
    (fun n hn => grading_eq_bot_outside hQ hn) χ
  exact
    { toLieHom := p.gradedLieHom.toLieHom.comp f
      map_mem := fun hx => p.gradedLieHom.map_mem
        (LieHom.ofGradingCharacter_mem _ _ _ _ hx) }

/-- A homogeneous twisted field is the character value times the ordinary
tropical pairing image. -/
theorem twistedGradedLieHom_apply_of_mem {n : Γ} (hn : n ∈ d.monoid)
    {x : tropicalSubalgebra ρ U d} (hx : x ∈ tropicalSubalgebraGrading ρ U d n) :
    p.twistedGradedLieHom hQ χ x =
      χ (Multiplicative.ofAdd ⟨n, hQ hn⟩) • p.gradedLieHom x := by
  classical
  calc
    _ = p.gradedLieHom (LieHom.ofGradingCharacter (tropicalSubalgebraGrading ρ U d) Q
        (fun n hn => grading_eq_bot_outside hQ hn) χ x) := (rfl)
    _ = _ := by rw [LieHom.ofGradingCharacter_apply _ _ _ χ (hQ hn) hx, map_smul]

/-- On a positive tangent generator the twist multiplies the transported character. -/
@[simp]
theorem coe_twistedGradedLieHom_tropicalSingle {n : Γ}
    (hn : n ∈ d.monoid) (hne : n ≠ 0) (m : U) (hm : m.val (ρ n) = 0) :
    (p.twistedGradedLieHom hQ χ (tropicalSingle d ρ U hn hne m hm)).val =
      χ (Multiplicative.ofAdd ⟨n, hQ hn⟩) •
        single ρ' (p.degreeMap n) (p.characterMap m) := by
  rw [twistedGradedLieHom_apply_of_mem p hQ χ hn
    ((mem_tropicalSubalgebraGrading_iff _ _ _ _ _).mpr
      ⟨m, (coe_tropicalSingle d ρ U hn hne m hm).symm⟩)]
  simp

/-- The trivial character recovers the original tropical pairing Lie map. -/
@[simp]
theorem twistedGradedLieHom_one : p.twistedGradedLieHom hQ 1 = p.gradedLieHom := by
  classical
  apply GradedLieHom.ext
  intro x
  simp [twistedGradedLieHom]

/-- Character-weighted monomial transport intertwines the tropical coefficient
actions when the pairing identity holds on the coefficient monoid. -/
theorem characterMap_tropicalVertexCoefficientAction
    {Q' : AddSubmonoid Γ'} (hQ' : e.monoid ≤ Q')
    (hT : Q.map p.degreeMap.toAddMonoidHom ≤ Q')
    (heval : ∀ (m : U) {q : Γ}, q ∈ Q →
      p.characterMap m (ρ' (p.degreeMap q)) = m.val (ρ q))
    (x : tropicalSubalgebra ρ U d) (a : R[Q]) :
    AddMonoidAlgebra.characterMap R
        ((AddSubmonoid.inclusion hT).comp (p.degreeMap.toAddMonoidHom.addSubmonoidMap Q)) χ
        (tropicalVertexCoefficientAction d ρ Q hQ x a) =
      tropicalVertexCoefficientAction e ρ' Q' hQ' (p.twistedGradedLieHom hQ χ x)
        (AddMonoidAlgebra.characterMap R
          ((AddSubmonoid.inclusion hT).comp
            (p.degreeMap.toAddMonoidHom.addSubmonoidMap Q)) χ a) := by
  classical
  induction x using DirectSum.Decomposition.inductionOn (tropicalSubalgebraGrading ρ U d) with
  | zero => simp
  | @homogeneous n x =>
    by_cases hn : n ∈ d.monoid
    · obtain ⟨m, hm⟩ := (mem_tropicalSubalgebraGrading_iff d ρ U n x).mp x.property
      rw [p.twistedGradedLieHom_apply_of_mem hQ χ hn x.property]
      simp only [map_smul, Derivation.smul_apply]
      rw [tropicalVertexCoefficientAction_of_homogeneous d ρ Q hQ hn _ m.val hm,
        tropicalVertexCoefficientAction_of_homogeneous e ρ' Q' hQ' (p.degreeMap.map_mem hn) _
          (p.characterMap m) (p.coe_gradedLieHom_of_homogeneous x m hm).symm]
      induction a using AddMonoidAlgebra.induction_linear with
      | zero => simp
      | add a b ha hb => simp only [map_add, smul_add, ha, hb]
      | single q r =>
        simp only [AddMonoidAlgebra.monomialDerivation_single,
          AddMonoidAlgebra.characterMap_single, AddMonoidHom.comp_apply,
          AddSubmonoid.subtype_apply, AddSubmonoid.coe_inclusion,
          AddMonoidHom.addSubmonoidMap_apply_coe, map_add,
          AddMonoidAlgebra.smul_single, smul_eq_mul]
        congr 1
        rw [heval m q.2]
        have hc := χ.map_mul (Multiplicative.ofAdd (⟨n, hQ hn⟩ : Q))
          (Multiplicative.ofAdd q)
        rw [← ofAdd_add] at hc
        rw [hc]
        ring
    · have hx : (x : tropicalSubalgebra ρ U d) = 0 := by
        simpa only [IsPositiveGrading.eq_bot (d := d)
          (ℒ := tropicalSubalgebraGrading ρ U d) n (Or.inl hn), Submodule.mem_bot]
          using x.property
      simp [hx]
  | add x y hx hy =>
    simp only [AddMemClass.coe_add, map_add, Derivation.add_apply, hx, hy]

end Mei.TropicalPairing
