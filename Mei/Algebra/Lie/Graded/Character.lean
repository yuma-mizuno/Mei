/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.Lie.Graded

/-!
# Characters acting on supported Lie gradings

A multiplicative character on an additive monoid of supported degrees scales each
homogeneous Lie element by its character value. The character may vanish, even
when the ambient grading group has inverses: it is defined only on the supporting
monoid. These endomorphisms implement coefficient specializations that can kill
positive homogeneous pieces.

The linear construction uses `DirectSum.toModule` and the internal decomposition,
as in Mathlib's `LieDerivation.ofGrading`; multiplicativity replaces the additive
degree identity used for a derivation.
-/

public section

noncomputable section

namespace LieHom

variable {Γ R L : Type*} [AddCommMonoid Γ] [DecidableEq Γ] [CommRing R]
  [LieRing L] [LieAlgebra R L] (ℒ : Γ → Submodule R L) [GradedLieAlgebra ℒ]
  (P : AddSubmonoid Γ) (hP : ∀ n, n ∉ P → ℒ n = ⊥)
  (χ : Multiplicative P →* R)

private def gradingCharacterLinear : L →ₗ[R] L := by
  classical
  exact (DirectSum.toModule R Γ L (fun n =>
    (if hn : n ∈ P then χ (Multiplicative.ofAdd ⟨n, hn⟩) else 0) • (ℒ n).subtype)).comp
      (DirectSum.decomposeLinearEquiv ℒ).toLinearMap

private theorem gradingCharacterLinear_apply {n : Γ} (hn : n ∈ P) {x : L}
    (hx : x ∈ ℒ n) :
    gradingCharacterLinear ℒ P χ x = χ (Multiplicative.ofAdd ⟨n, hn⟩) • x := by
  simp only [gradingCharacterLinear, LinearMap.comp_apply,
    LinearEquiv.coe_coe, DirectSum.decomposeLinearEquiv_apply,
    DirectSum.decompose_of_mem ℒ hx, ← DirectSum.lof_eq_of R,
    DirectSum.toModule_lof, dite_eq_left hn, LinearMap.smul_apply, Submodule.subtype_apply]

include hP in
private theorem gradingCharacterLinear_map_lie (x y : L) :
    gradingCharacterLinear ℒ P χ ⁅x, y⁆ =
      ⁅gradingCharacterLinear ℒ P χ x, gradingCharacterLinear ℒ P χ y⁆ := by
  induction x using DirectSum.Decomposition.inductionOn ℒ with
  | zero => simp
  | @homogeneous n x =>
    by_cases hn : n ∈ P
    · induction y using DirectSum.Decomposition.inductionOn ℒ with
      | zero => simp
      | @homogeneous m y =>
        by_cases hm : m ∈ P
        · rw [gradingCharacterLinear_apply ℒ P χ (P.add_mem hn hm)
            (SetLike.GradedBracket.bracket_mem x.property y.property),
            gradingCharacterLinear_apply ℒ P χ hn x.property,
            gradingCharacterLinear_apply ℒ P χ hm y.property]
          have hc := χ.map_mul (Multiplicative.ofAdd ⟨n, hn⟩)
            (Multiplicative.ofAdd ⟨m, hm⟩)
          simpa only [← ofAdd_add, AddSubmonoid.mk_add_mk,
            smul_lie, lie_smul, smul_smul, mul_comm] using
            congrArg (fun r : R => r • ⁅(x : L), (y : L)⁆) hc
        · have hy : (y : L) = 0 := by simpa only [hP m hm, Submodule.mem_bot] using y.property
          simp [hy]
      | add y z hy hz => simp_all
    · have hx : (x : L) = 0 := by simpa only [hP n hn, Submodule.mem_bot] using x.property
      simp [hx]
  | add x z hx hz => simp_all

/-- Scale a supported Lie grading by a multiplicative character, allowing zero values. -/
def ofGradingCharacter : L →ₗ⁅R⁆ L where
  toLinearMap := gradingCharacterLinear ℒ P χ
  map_lie' := by intros; exact gradingCharacterLinear_map_lie ℒ P hP χ _ _

/-- The character endomorphism scales each supported homogeneous piece. -/
theorem ofGradingCharacter_apply {n : Γ} (hn : n ∈ P) {x : L} (hx : x ∈ ℒ n) :
    ofGradingCharacter ℒ P hP χ x = χ (Multiplicative.ofAdd ⟨n, hn⟩) • x :=
  gradingCharacterLinear_apply ℒ P χ hn hx

/-- Character endomorphisms preserve every homogeneous piece. -/
theorem ofGradingCharacter_mem {n : Γ} {x : L} (hx : x ∈ ℒ n) :
    ofGradingCharacter ℒ P hP χ x ∈ ℒ n := by
  by_cases hn : n ∈ P
  · rw [ofGradingCharacter_apply ℒ P hP χ hn hx]
    exact (ℒ n).smul_mem _ hx
  · have hx0 : x = 0 := by simpa only [hP n hn, Submodule.mem_bot] using hx
    simp [hx0]

/-- The trivial character acts as the identity. -/
@[simp]
theorem ofGradingCharacter_one : ofGradingCharacter ℒ P hP 1 = LieHom.id := by
  ext x
  induction x using DirectSum.Decomposition.inductionOn ℒ with
  | zero => simp
  | @homogeneous n x =>
    by_cases hn : n ∈ P
    · simp [ofGradingCharacter_apply ℒ P hP 1 hn x.property]
    · have hx : (x : L) = 0 := by simpa only [hP n hn, Submodule.mem_bot] using x.property
      simp [hx]
  | add x y hx hy => simpa only [map_add, LieHom.id_apply] using congrArg₂ (· + ·) hx hy

/-- Multiplying characters composes their homogeneous scaling endomorphisms. -/
theorem ofGradingCharacter_mul (ψ : Multiplicative P →* R) :
    ofGradingCharacter ℒ P hP (χ * ψ) =
      (ofGradingCharacter ℒ P hP χ).comp (ofGradingCharacter ℒ P hP ψ) := by
  ext x
  induction x using DirectSum.Decomposition.inductionOn ℒ with
  | zero => simp
  | @homogeneous n x =>
    by_cases hn : n ∈ P
    · simp [ofGradingCharacter_apply ℒ P hP (χ * ψ) hn x.property,
        ofGradingCharacter_apply ℒ P hP ψ hn x.property,
        ofGradingCharacter_apply ℒ P hP χ hn x.property, smul_smul, mul_comm]
    · have hx : (x : L) = 0 := by simpa only [hP n hn, Submodule.mem_bot] using x.property
      simp [hx]
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

end LieHom
