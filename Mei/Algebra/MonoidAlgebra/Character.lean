/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Character-weighted maps of monoid algebras

An additive exponent map and a multiplicative character induce the map
`r z^q ↦ r χ(q) z^(T q)`. Character values need not be units: specialization
can delete monomials. The construction uses `AddMonoidAlgebra.lift`, retaining
the algebra structure and allowing exponent maps with kernels.
-/

public section

noncomputable section

namespace AddMonoidAlgebra

variable (R : Type*) {M N P : Type*} [CommSemiring R]
  [AddMonoid M] [AddMonoid N] [AddMonoid P]

/-- The algebra map `r z^q ↦ r χ(q) z^(T q)`, allowing vanishing character values. -/
def characterMap (T : M →+ N) (χ : Multiplicative M →* R) : R[M] →ₐ[R] R[N] :=
  lift R R[N] M
    { toFun := fun q => single (T q.toAdd) (χ q)
      map_one' := by simp [one_def]
      map_mul' := by intros; simp [single_mul_single] }

/-- Character-weighted exponent transport on a basis monomial. -/
@[simp]
theorem characterMap_single (T : M →+ N) (χ : Multiplicative M →* R) (q : M) (r : R) :
    characterMap R T χ (single q r) = single (T q) (r * χ (Multiplicative.ofAdd q)) := by
  simp [characterMap, smul_single, smul_eq_mul]

/-- The trivial character recovers ordinary exponent transport. -/
@[simp]
theorem characterMap_one (T : M →+ N) :
    characterMap R T 1 = mapDomainAlgHom R R T := by
  ext q
  simp [mapDomainAlgHom_apply]

/-- Character-weighted maps compose by pulling the second character back along
the first exponent map and multiplying the two characters. -/
theorem characterMap_comp (T : M →+ N) (U : N →+ P)
    (χ : Multiplicative M →* R) (ψ : Multiplicative N →* R) :
    (characterMap R U ψ).comp (characterMap R T χ) =
      characterMap R (U.comp T) (χ * ψ.comp T.toMultiplicative) := by
  ext q
  simp

end AddMonoidAlgebra
