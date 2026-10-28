/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Algebra.Lie.Logarithmic.Grading
public import Mei.Algebra.MonoidAlgebra.Filtration
public import Mei.Algebra.Lie.Filtered.BCH

/-!
# Tropical vertex actions on coefficient monoids

Positive formal logarithmic fields act on `R[Q]` for every additive coefficient
monoid `Q` containing the positive monoid. The action retains the formal Lie
algebra even when some characters act trivially. It raises the allowed-increment
filtration, so its BCH group acts on the completed coefficient algebra.
With the `TropicalVertexCoefficientAction` scope open, use
`AlgFiltration.completedBCHAction` and `AlgFiltration.projection_completedBCHAction`
with `TropicalVertexCoefficientAction.filtration` and `tropicalVertexGrading`.

For a positive degree map `T`, character-weighted monomial maps on coefficient
algebras carry the filtration term above the cutoff modulus of `T` into the target
term, so they extend to completed coefficient algebras with that modulus.
`Mei.Algebra.Lie.Logarithmic.Pairing.Coefficient` shows that tropical pairings
intertwine the coefficient actions with ordinary monomial maps;
`Mei.Algebra.Lie.Logarithmic.Pairing.Twist` treats character-weighted maps.

The construction uses `LogarithmicVectorField.action`, the monomial derivations
and filtration bounds in `Mei.Algebra.MonoidAlgebra.Filtration`, and the existing
filtered BCH action. The coefficient action is that of Mandel, *Scattering
diagrams, theta functions, and refined tropical curve counts*, Example 2.1(i),
arXiv:1503.06183v5.
-/

public section

noncomputable section

namespace Mei

open _root_.AddMonoidAlgebra

variable {R Γ Λ : Type*} [CommRing R] [AddCommMonoid Γ] [AddCommMonoid Λ]
  (d : PositiveDegrees Γ) (ρ : Γ →+ Λ) (Q : AddSubmonoid Γ)

namespace LogarithmicVectorField

private def coefficientLinear : LogarithmicVectorField R Γ Λ ρ →ₗ[R]
    Derivation R R[Q] R[Q] :=
  (action (ρ.comp Q.subtype)).toLinearMap.comp
    ((toFinsupp (ρ.comp Q.subtype)).symm.toLinearMap.comp
      ((Finsupp.lsubtypeDomain (Q : Set Γ)).comp (toFinsupp ρ).toLinearMap))

private theorem coefficientLinear_single {n : Γ} (hn : n ∈ Q) (m : Λ →+ R) :
    coefficientLinear (R := R) ρ Q (single ρ n m) =
      AddMonoidAlgebra.monomialDerivation (⟨n, hn⟩ : Q) (m.comp (ρ.comp Q.subtype)) := by
  classical
  have hs : Finsupp.lsubtypeDomain (R := R) (Q : Set Γ) (Finsupp.single n m) =
      Finsupp.single (⟨n, hn⟩ : Q) m := by
    rw [Finsupp.lsubtypeDomain_apply]
    ext p
    simp [Finsupp.single_apply, Subtype.ext_iff]
  simp only [coefficientLinear, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LieHom.coe_toLinearMap, toFinsupp_single, hs]
  simpa only [single_def, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    Finsupp.lsingle_apply] using action_single (ρ.comp Q.subtype) (⟨n, hn⟩ : Q) m

private theorem coefficientLinear_mapDomain (hQ : d.monoid ≤ Q)
    (x : tropicalVertexLieAlgebra (R := R) d ρ) (a : R[Q]) :
    mapDomainRingHom R Q.subtype (coefficientLinear ρ Q x a) =
      action ρ x (mapDomainRingHom R Q.subtype a) := by
  classical
  induction x using DirectSum.Decomposition.inductionOn
    (tropicalVertexGrading (R := R) d ρ) with
  | zero => simp
  | @homogeneous n x =>
    by_cases hn : n ∈ d.monoid
    · obtain ⟨m, hm⟩ := (mem_tropicalVertexGrading_iff d ρ n
        (x : tropicalVertexLieAlgebra (R := R) d ρ)).mp x.property
      rw [← hm, coefficientLinear_single ρ Q (hQ hn), action_single]
      induction a using induction_linear with
      | zero => simp
      | add a b ha hb => simp_all [mapDomain_add]
      | single p r => simp [mapDomainRingHom_apply]
    · have hx : (x : tropicalVertexLieAlgebra (R := R) d ρ) = 0 := by
        simpa only [IsPositiveGrading.eq_bot (d := d)
          (ℒ := tropicalVertexGrading (R := R) d ρ) n (Or.inl hn), Submodule.mem_bot]
          using x.property
      simp [hx]
  | add x y hx hy => simp_all [mapDomain_add]

end LogarithmicVectorField

/-- The tropical vertex Lie algebra acts on any coefficient monoid containing its
positive degrees, by logarithmic derivations. -/
def tropicalVertexCoefficientAction (hQ : d.monoid ≤ Q) :
    tropicalVertexLieAlgebra (R := R) d ρ →ₗ⁅R⁆ Derivation R R[Q] R[Q] :=
  { (LogarithmicVectorField.coefficientLinear ρ Q).comp
      (tropicalVertexLieAlgebra d ρ).incl.toLinearMap with
    map_lie' := by
      intro x y
      apply Derivation.ext
      intro a
      apply mapDomain_injective Q.subtype_injective
      simp only [LinearMap.toFun_eq_coe, LinearMap.comp_apply,
        LieHom.coe_toLinearMap, LieSubalgebra.coe_incl, Derivation.commutator_apply]
      simp only [← mapDomainRingHom_apply, map_sub]
      simp only [LogarithmicVectorField.coefficientLinear_mapDomain d ρ Q hQ]
      simp only [LieSubalgebra.coe_bracket, LieHom.map_lie, Derivation.commutator_apply] }

/-- Embedding coefficients into the ambient monoid algebra intertwines the restricted
and ordinary formal actions. -/
theorem mapDomain_tropicalVertexCoefficientAction (hQ : d.monoid ≤ Q)
    (x : tropicalVertexLieAlgebra (R := R) d ρ) (a : R[Q]) :
    mapDomainRingHom R Q.subtype (tropicalVertexCoefficientAction d ρ Q hQ x a) =
      LogarithmicVectorField.action ρ x (mapDomainRingHom R Q.subtype a) :=
  LogarithmicVectorField.coefficientLinear_mapDomain d ρ Q hQ x a

/-- A homogeneous field acts by its character restricted to the coefficient monoid. -/
theorem tropicalVertexCoefficientAction_of_homogeneous (hQ : d.monoid ≤ Q)
    {n : Γ} (hn : n ∈ d.monoid) (x : tropicalVertexLieAlgebra (R := R) d ρ)
    (m : Λ →+ R) (hx : LogarithmicVectorField.single ρ n m = x.val) :
    tropicalVertexCoefficientAction d ρ Q hQ x =
      AddMonoidAlgebra.monomialDerivation (⟨n, hQ hn⟩ : Q) (m.comp (ρ.comp Q.subtype)) := by
  exact (congrArg (LogarithmicVectorField.coefficientLinear ρ Q) hx).symm.trans
    (LogarithmicVectorField.coefficientLinear_single ρ Q (hQ hn) m)

/-- A positive tangent generator acts by the restricted monomial logarithmic derivation. -/
@[simp]
theorem tropicalVertexCoefficientAction_single (hQ : d.monoid ≤ Q)
    {n : Γ} (hn : n ∈ d.monoid) (hne : n ≠ 0) (m : Λ →+ R) (hm : m (ρ n) = 0) :
    tropicalVertexCoefficientAction d ρ Q hQ
        ⟨LogarithmicVectorField.single ρ n m,
          single_mem_tropicalVertexLieAlgebra d ρ hn hne m hm⟩ =
      AddMonoidAlgebra.monomialDerivation (⟨n, hQ hn⟩ : Q) (m.comp (ρ.comp Q.subtype)) :=
  tropicalVertexCoefficientAction_of_homogeneous d ρ Q hQ hn _ m rfl

namespace TropicalVertexCoefficientAction

/-- The positive-increment filtration on the coefficient monoid algebra. -/
def filtration {R : Type*} [Semiring R] : AlgFiltration R[Q] :=
  (d.monoid.comap Q.subtype).monoidAlgebraFiltration (d.degree.comp Q.subtype)

/-- The filtration is measured by positive increments in `Q`. -/
@[simp]
theorem filtration_ideal {R : Type*} [Semiring R] (k : ℕ) :
    (filtration (R := R) d Q).ideal k =
      (d.monoid.comap Q.subtype).monoidAlgebraIdeal (d.degree.comp Q.subtype) k := by
  rw [filtration, AddSubmonoid.monoidAlgebraFiltration_ideal]

section Map

variable {Γ' : Type*} [AddCommMonoid Γ'] {e : PositiveDegrees Γ'} {Q' : AddSubmonoid Γ'}

variable {d Q} in
/-- Character-weighted monomial transport carries the coefficient filtration
above the original cutoff modulus into the target filtration. Character values
may vanish. -/
theorem filtration_ideal_le_comap_characterMap {R : Type*} [CommSemiring R]
    (T : PositiveDegreeMap d e) (χ : Multiplicative Q →* R)
    (hT : Q.map T.toAddMonoidHom ≤ Q') (k : ℕ) :
    (filtration (R := R) d Q).ideal (T.modulus k + 1) ≤
      ((filtration e Q').ideal (k + 1)).comap (characterMap R
        ((AddSubmonoid.inclusion hT).comp (T.toAddMonoidHom.addSubmonoidMap Q)) χ) := by
  intro a ha
  rw [filtration_ideal] at ha
  rw [Ideal.mem_comap, filtration_ideal]
  refine (d.monoid.comap Q.subtype).monoidAlgebraIdeal_le_comap_characterMap
    (d.degree.comp Q.subtype) (e.monoid.comap Q'.subtype) (e.degree.comp Q'.subtype)
    _ χ (fun n hn => ?_) (fun n hn hd => ?_) ha
  · simpa only [AddSubmonoid.mem_comap, AddMonoidHom.comp_apply, AddSubmonoid.subtype_apply,
      AddSubmonoid.coe_inclusion, AddMonoidHom.addSubmonoidMap_apply_coe]
      using T.map_mem (AddSubmonoid.mem_comap.mp hn)
  · have h := T.degree_gt k (AddSubmonoid.mem_comap.mp hn) (by
      simpa only [Nat.cast_add, Nat.cast_one, Int.add_one_le_iff, AddMonoidHom.comp_apply]
        using hd)
    simpa only [Nat.cast_add, Nat.cast_one, Int.add_one_le_iff, AddMonoidHom.comp_apply,
      AddSubmonoid.subtype_apply, AddSubmonoid.coe_inclusion,
      AddMonoidHom.addSubmonoidMap_apply_coe] using h

variable {d Q} in
/-- The monomial map `z^q ↦ z^(T q)` along a positive degree map carries the
coefficient filtration term above the cutoff modulus into the target term. Thus
`Mei.AlgFiltration.mapCompletionₐ` extends it to the completed coefficient algebras
with the original modulus of `T`. -/
theorem filtration_ideal_le_comap_mapDomainAlgHom {R : Type*} [CommSemiring R]
    (T : PositiveDegreeMap d e)
    (hT : Q.map T.toAddMonoidHom ≤ Q') (k : ℕ) :
    (filtration (R := R) d Q).ideal (T.modulus k + 1) ≤
      ((filtration e Q').ideal (k + 1)).comap (mapDomainAlgHom R R
        ((AddSubmonoid.inclusion hT).comp (T.toAddMonoidHom.addSubmonoidMap Q))) := by
  simpa only [characterMap_one] using filtration_ideal_le_comap_characterMap T 1 hT k

end Map

variable [Fact (d.monoid ≤ Q)]

/-- The logarithmic derivation representation, as a Lie action on coefficients.
Open this scope to select this action. -/
scoped instance instLieRingModule :
    LieRingModule (tropicalVertexLieAlgebra (R := R) d ρ) R[Q] :=
  LieRingModule.compLieHom _ (tropicalVertexCoefficientAction d ρ Q Fact.out)

/-- The logarithmic coefficient action is linear over the coefficient ring. -/
scoped instance instLieModule :
    LieModule R (tropicalVertexLieAlgebra (R := R) d ρ) R[Q] :=
  LieModule.compLieHom _ (tropicalVertexCoefficientAction d ρ Q Fact.out)

/-- The selected Lie action evaluates the coefficient derivation. -/
@[simp]
theorem lie_eq (x : tropicalVertexLieAlgebra (R := R) d ρ) (a : R[Q]) :
    ⁅x, a⁆ = tropicalVertexCoefficientAction d ρ Q Fact.out x a := (rfl)

/-- A positive homogeneous logarithmic field shifts the ambient coefficient degree. -/
scoped instance instGradedBracket :
    SetLike.GradedBracket (tropicalVertexGrading (R := R) d ρ)
      (gradeBy R Q.subtype) where
  bracket_mem := by
    intro n p x a hx ha
    by_cases hn : n ∈ d.monoid
    · obtain ⟨m, hm⟩ := (mem_tropicalVertexGrading_iff d ρ n x).mp hx
      rw [lie_eq, tropicalVertexCoefficientAction_of_homogeneous d ρ Q Fact.out hn x m hm]
      rw [← sum_coeff_single a, Finsupp.sum, map_sum]
      apply Submodule.sum_mem
      intro q hq
      rw [AddMonoidAlgebra.monomialDerivation_single]
      have hp : (q : Γ) = p := ha q hq
      simpa only [AddMonoidHom.comp_apply, AddSubmonoid.subtype_apply,
        AddSubmonoid.coe_add, hp, vadd_eq_add] using
        single_mem_gradeBy Q.subtype
          ((⟨n, (Fact.out : d.monoid ≤ Q) hn⟩ : Q) + q)
          (a.coeff q * m (ρ q))
    · have hx0 : x = 0 := by
        simpa only [IsPositiveGrading.eq_bot (d := d)
          (ℒ := tropicalVertexGrading (R := R) d ρ) n (Or.inl hn), Submodule.mem_bot]
          using hx
      simp [hx0]


/-- Logarithmic fields act by derivations of coefficient multiplication. -/
scoped instance instIsDerivationAction :
    IsDerivationAction (tropicalVertexLieAlgebra (R := R) d ρ) R[Q] where
  lie_mul x a b := by simp [lie_eq, Derivation.leibniz, mul_comm]

/-- A positive field above cutoff `a` raises coefficient order by `a + 1`. -/
scoped instance instIsFiltrationRaising :
    IsFiltrationRaising d (tropicalVertexGrading (R := R) d ρ)
      ((filtration (R := R) d Q).toModuleFiltration R) where
  lie_mem {a b x f} hx hf := by
    classical
    have hQ : d.monoid ≤ Q := Fact.out
    simp only [filtration_ideal, Submodule.restrictScalars_mem] at hf ⊢
    rw [d.degreeSubmodule_def (tropicalVertexGrading (R := R) d ρ) a] at hx
    refine Submodule.iSup_induction
      (fun n : {n : Γ // (a : ℤ) < d.degree n} => tropicalVertexGrading (R := R) d ρ n)
      (motive := fun x => ⁅x, f⁆ ∈
        (d.monoid.comap Q.subtype).monoidAlgebraIdeal (d.degree.comp Q.subtype)
          (a + b + 1)) hx ?_ (by simp) ?_
    · intro n x hx
      by_cases hn : n.val ∈ d.monoid
      · obtain ⟨m, hm⟩ := (mem_tropicalVertexGrading_iff d ρ n x).mp hx
        rw [lie_eq, tropicalVertexCoefficientAction_of_homogeneous d ρ Q hQ hn x m hm]
        have hi : (⟨n.val, hQ hn⟩ : Q) ∈ d.monoid.comap Q.subtype := hn
        have hd : ((a + 1 : ℕ) : ℤ) ≤
            (d.degree.comp Q.subtype) (⟨n.val, hQ hn⟩ : Q) := by
          simpa only [AddMonoidHom.comp_apply, AddSubmonoid.subtype_apply, Nat.cast_add,
            Nat.cast_one] using (Int.add_one_le_iff.mpr n.property)
        simpa only [Nat.add_assoc, Nat.add_comm 1 b] using
          (d.monoid.comap Q.subtype).monomialDerivation_mem_monoidAlgebraIdeal
            (d.degree.comp Q.subtype) hi (m.comp (ρ.comp Q.subtype)) hd hf
      · have hx0 : x = 0 := by
          simpa only [IsPositiveGrading.eq_bot (d := d)
            (ℒ := tropicalVertexGrading (R := R) d ρ) n (Or.inl hn), Submodule.mem_bot]
            using hx
        simp [hx0]
    · intro x y hx hy
      simpa only [add_lie] using
        (d.monoid.comap Q.subtype).monoidAlgebraIdeal (d.degree.comp Q.subtype)
          (a + b + 1) |>.add_mem hx hy

end TropicalVertexCoefficientAction

end Mei
