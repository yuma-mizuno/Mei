/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.ScatteringDiagram.DirectedDiagram.Basic
public import Mei.Geometry.Convex.Polyhedron.CommonPath
import Mei.Geometry.Convex.Polyhedron.Path.Restriction

/-!
# Compatible directed path products

Lowering the cutoff restricts an admissible path to the smaller active wall family
and projects its transport. This remains true when only some labels of a simultaneous
crossing survive. The finite products along a common all-order path consequently
define a completed BCH label, with the usual concatenation and reversal laws.

The construction uses `Quiver.Path.wallPathProduct_restrict` to remove labels killed
by the quotient homomorphism, and `CommonWallComplement` to retain the same geometric
path at every cutoff. Its target is the existing compatible-family completed group.
No stabilization of the active supports or local finiteness of all walls is required.
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei.DirectedDiagram

variable {Γ Λ R L V ι : Type*} [AddCommGroup Γ] [AddCommGroup Λ]
  [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]
  [LieAlgebra ℚ L] [IsScalarTower ℚ R L] [DecidableEq Γ]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {ρ : Γ →+ Λ} {ℒ : Γ → Submodule R L} {d : PositiveDegrees Γ}
  [GradedLieAlgebra ℒ] [IsPositiveGrading d ℒ]
  {i : Λ →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {H : DirectedWallSpaces ρ ℒ} (D : DirectedDiagram (d := d) h H ι)

/-- Lowering the cutoff projects transport and forgets exactly the walls that become inactive. -/
theorem truncation_levelPathProduct {k l : ℕ} (hkl : k ≤ l)
    {x y : WallComplement (fun j : D.active l => (D.wall j).support)}
    (p : AdmissiblePLPath x y) :
    (d.truncationMap ℒ hkl).bchGroupMap (D.levelPathProduct l p) =
      D.levelPathProduct k
        ((WallComplement.restrictPrefunctor (fun j : D.active l => (D.wall j).support)
          (Set.inclusion (D.active_mono hkl))).mapPath p) := by
  let f := Set.inclusion (D.active_mono hkl)
  let q := (WallComplement.restrictPrefunctor
    (fun j : D.active l => (D.wall j).support) f).mapPath p
  let F := (d.truncationMap ℒ hkl).bchGroupMap
  have hproj (j : D.active l) : F (CompletedGroup.projection l (D.wall j).label) =
      CompletedGroup.projection k (D.wall j).label :=
    CompletedGroup.map_projection k l hkl (D.wall j).label
  have hlabel : ∀ j : D.active l, j ∉ range f →
      F (CompletedGroup.projection l (D.wall j).label) = 1 := by
    intro j hj
    rw [hproj]
    by_contra hne
    exact hj ⟨⟨j.val, (D.mem_active k j.val).mpr hne⟩, Subtype.ext rfl⟩
  have he := p.wallPathProduct_restrict (G := d.truncatedGroup ℒ k)
    (fun j : D.active l => h.realCharacter (D.wall j).normal)
    (fun j => F (CompletedGroup.projection l (D.wall j).label))
    (fun a b hab => (D.commute_projection_label l a b hab).map F)
    f (Set.inclusion_injective _) hlabel
  have hq := D.levelPathProduct_eq_wallPathProduct k q
    (D.commute_projection_label k)
  calc
    _ = F (p.wallPathProduct (G := d.truncatedGroup ℒ l)
        (fun j : D.active l => h.realCharacter (D.wall j).normal)
        (fun j => CompletedGroup.projection l (D.wall j).label)
        (D.commute_projection_label l)) :=
      congrArg F (D.levelPathProduct_eq_wallPathProduct l p (D.commute_projection_label l))
    _ = _ := Quiver.Path.map_wallPathProduct (G := d.truncatedGroup ℒ l)
      (K := d.truncatedGroup ℒ k) _ _ _ F p
    _ = _ := he.symm
    _ = _ := by
      simp only [Function.comp_def, hproj]
      convert hq.symm using 1
      -- Restricted indices coerce to the original wall; tower operations are BCH operations.
      rfl

/-- Endpoints lying on no wall active at any cutoff. Identity-labelled walls impose
no condition on endpoints or paths. -/
abbrev Point :=
  CommonWallComplement (fun k => fun j : D.active k => (D.wall j).support)

variable {D}

private theorem projection_path_restrict {x y : D.Point} (p : Quiver.Path x y)
    {k l : ℕ} (hkl : k ≤ l) :
    (WallComplement.restrictPrefunctor (fun j : D.active l => (D.wall j).support)
      (Set.inclusion (D.active_mono hkl))).mapPath
        ((CommonWallComplement.projectionPrefunctor l).mapPath p) =
      (CommonWallComplement.projectionPrefunctor k).mapPath p := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    simp only [Prefunctor.mapPath_cons, ih]
    rfl

variable (D)

/-- All-order allowed endpoints admit a common admissible path through the finite
active wall families, without a local finiteness hypothesis on their union. -/
theorem exists_path (x y : D.Point) : Nonempty (Quiver.Path x y) := by
  let := h.finiteDimensional
  obtain ⟨p, _⟩ := CommonWallComplement.exists_length_eq_two
    (W := fun k => fun j : D.active k => (D.wall j).support)
    (fun k j => (D.wall j).isConvexPolyhedron)
    (fun k j => (D.wall j).finrank_direction_add_one) x y
  exact ⟨p⟩

variable {x y z : D.Point}

/-- The finite-order products of an all-order path form a compatible family. -/
theorem truncation_pathProduct (p : Quiver.Path x y) {k l : ℕ} (hkl : k ≤ l) :
    (d.truncationMap ℒ hkl).bchGroupMap
      (D.levelPathProduct l ((CommonWallComplement.projectionPrefunctor l).mapPath p)) =
        D.levelPathProduct k ((CommonWallComplement.projectionPrefunctor k).mapPath p) := by
  have hp := D.truncation_levelPathProduct hkl
    ((CommonWallComplement.projectionPrefunctor l).mapPath p)
  rw [projection_path_restrict p hkl] at hp
  convert hp using 1
  -- Rewriting the path leaves the categorical and concrete quotient-group presentations.
  rfl

/-- The completed product of the finite active-wall transports along one all-order path. -/
def pathProduct (p : Quiver.Path x y) : d.completedBCHGroup ℒ :=
  ⟨fun k => D.levelPathProduct k ((CommonWallComplement.projectionPrefunctor k).mapPath p),
    (mem_completedGroup_iff _ _).mpr (fun _ _ hkl => D.truncation_pathProduct p hkl)⟩

/-- Projection of the completed product recovers its actual finite geometric transport. -/
@[simp]
theorem projection_pathProduct (k : ℕ) (p : Quiver.Path x y) :
    CompletedGroup.projection k (D.pathProduct p) =
      D.levelPathProduct k ((CommonWallComplement.projectionPrefunctor k).mapPath p) := by
  rw [CompletedGroup.projection_apply]
  rfl

-- Reflexivity identifies the categorical tower operations with the concrete BCH operations.
@[simp]
theorem pathProduct_nil : D.pathProduct (Quiver.Path.nil : Quiver.Path x x) = 1 := by
  apply CompletedGroup.ext
  intro k
  simp
  rfl

/-- The second path acts on the left of the first path's completed product. -/
@[simp]
theorem pathProduct_comp (p : Quiver.Path x y) (q : Quiver.Path y z) :
    D.pathProduct (p.comp q) = D.pathProduct q * D.pathProduct p := by
  apply CompletedGroup.ext
  intro k
  simp
  rfl

/-- Reversal inverts the completed directed product. -/
@[simp]
theorem pathProduct_reverse (p : Quiver.Path x y) :
    D.pathProduct p.reverse = (D.pathProduct p)⁻¹ := by
  apply CompletedGroup.ext
  intro k
  simp
  rfl

end Mei.DirectedDiagram
