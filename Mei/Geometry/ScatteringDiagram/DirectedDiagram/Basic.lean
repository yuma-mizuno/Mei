/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedWall
public import Mei.Geometry.Convex.Polyhedron.Path.Product

/-!
# Directed diagrams and finite-order path products

A directed diagram is an indexed family of directed affine walls, only finitely
many of whose labels survive at each order. The active supports at a fixed order
therefore admit the existing admissible polygonal paths. Their path products use
all signed labels at simultaneous coplanar crossings, without enumerating those
walls. Coplanar commutation follows from `DirectedWall.commute_label_of_direction_eq`.

The product uses `Quiver.Path.wallPathProduct` and its grouped crossing events.
It has the left-action convention: the first crossing is rightmost, concatenation
multiplies in the opposite order, and reversal inverts the product. Finite indexed
families are included, while no local finiteness of all supports is imposed.
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei

variable {Γ Λ R L V : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} (h : TauCeti.Toric.IsIntegralLattice i)
  (H : DirectedWallSpaces ρ ℒ)

/-- An indexed directed wall family with finite activity at every degree cutoff.
Repeated walls retain distinct indices. -/
@[ext]
structure DirectedDiagram (ι : Type*) where
  /-- The directed walls, including their supports and completed labels. -/
  wall : ι → DirectedWall (d := d) h H
  /-- Only finitely many indexed labels are nonidentity at any fixed order. -/
  finite_active : CompletedGroup.HasFiniteSupport (fun j => (wall j).label)

namespace DirectedDiagram

variable {h H} {ι : Type*} (D : DirectedDiagram (d := d) h H ι)

/-- Every finite indexed family is a directed diagram. -/
def ofFinite [Finite ι] (W : ι → DirectedWall (d := d) h H) :
    DirectedDiagram (d := d) h H ι where
  wall := W
  finite_active _ := Set.toFinite _

@[simp]
theorem ofFinite_wall [Finite ι] (W : ι → DirectedWall (d := d) h H) (j : ι) :
    (ofFinite W).wall j = W j := (rfl)

/-- The indices whose labels survive the order-`k` projection. -/
def active (k : ℕ) : Set ι :=
  Function.mulSupport (fun j => CompletedGroup.projection k (D.wall j).label)

/-- Activity is exactly nontriviality of the projected label. -/
@[simp]
theorem mem_active (k : ℕ) (j : ι) :
    j ∈ D.active k ↔ CompletedGroup.projection k (D.wall j).label ≠ 1 := Iff.rfl

/-- The active wall index type is finite at every order. -/
instance finiteActive (k : ℕ) : Finite (D.active k) :=
  Set.finite_coe_iff.mpr (D.finite_active k)

/-- A label active at a lower order is also active at every higher order. -/
theorem active_mono : Monotone D.active := by
  intro k l hkl j hj
  simp only [mem_active] at hj ⊢
  intro he
  apply hj
  have hp := CompletedGroup.map_projection k l hkl (D.wall j).label
  rw [he, map_one] at hp
  exact hp.symm

/-- The projected labels of active walls with the same affine span commute. -/
theorem commute_projection_label (k : ℕ) (a b : D.active k)
    (hab : affineSpan ℝ (D.wall a).support = affineSpan ℝ (D.wall b).support) :
    Commute (CompletedGroup.projection k (D.wall a).label)
      (CompletedGroup.projection k (D.wall b).label) :=
  ((D.wall a).commute_label_of_direction_eq (D.wall b)
    (congrArg AffineSubspace.direction hab)).map (CompletedGroup.projection k)

/-- The order-`k` transport along a path admissible for the finite active wall family. -/
def levelPathProduct (k : ℕ)
    {x y : WallComplement (fun j : D.active k => (D.wall j).support)}
    (p : AdmissiblePLPath x y) : d.truncatedGroup ℒ k :=
  p.wallPathProduct (fun j : D.active k => h.realCharacter (D.wall j).normal)
    (fun j => CompletedGroup.projection k (D.wall j).label) (D.commute_projection_label k)

/-- The grouped wall-family product characterizes finite-order transport, independently
of which proof of coplanar commutation is used. -/
theorem levelPathProduct_eq_wallPathProduct (k : ℕ)
    {x y : WallComplement (fun j : D.active k => (D.wall j).support)}
    (p : AdmissiblePLPath x y)
    (comm : ∀ a b : D.active k,
      affineSpan ℝ (D.wall a).support = affineSpan ℝ (D.wall b).support →
        Commute (CompletedGroup.projection k (D.wall a).label)
          (CompletedGroup.projection k (D.wall b).label)) :
    D.levelPathProduct k p =
      p.wallPathProduct (fun j : D.active k => h.realCharacter (D.wall j).normal)
        (fun j => CompletedGroup.projection k (D.wall j).label) comm := (rfl)

@[simp]
theorem levelPathProduct_nil (k : ℕ)
    (x : WallComplement (fun j : D.active k => (D.wall j).support)) :
    D.levelPathProduct k (Quiver.Path.nil : AdmissiblePLPath x x) = 1 := by
  unfold levelPathProduct
  exact Quiver.Path.wallPathProduct_nil _ _ _

/-- Appending a segment places its transport on the left. -/
@[simp]
theorem levelPathProduct_cons (k : ℕ)
    {x y z : WallComplement (fun j : D.active k => (D.wall j).support)}
    (p : AdmissiblePLPath x y) (e : y ⟶ z) :
    D.levelPathProduct k (p.cons e) =
      D.levelPathProduct k e.toPath * D.levelPathProduct k p := by
  unfold levelPathProduct
  exact p.wallPathProduct_comp _ _ _ e.toPath

/-- Concatenated paths multiply with the second transport on the left. -/
@[simp]
theorem levelPathProduct_comp (k : ℕ)
    {x y z : WallComplement (fun j : D.active k => (D.wall j).support)}
    (p : AdmissiblePLPath x y) (q : AdmissiblePLPath y z) :
    D.levelPathProduct k (p.comp q) = D.levelPathProduct k q * D.levelPathProduct k p := by
  unfold levelPathProduct
  exact p.wallPathProduct_comp _ _ _ q

/-- Reversing a path inverts its finite-order transport. -/
@[simp]
theorem levelPathProduct_reverse (k : ℕ)
    {x y : WallComplement (fun j : D.active k => (D.wall j).support)}
    (p : AdmissiblePLPath x y) :
    D.levelPathProduct k p.reverse = (D.levelPathProduct k p)⁻¹ := by
  unfold levelPathProduct
  exact p.wallPathProduct_reverse _ _ _
    (fun j : D.active k => (D.wall j).direction_support.symm)

end DirectedDiagram
end Mei
