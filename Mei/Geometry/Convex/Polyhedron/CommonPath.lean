/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.SimultaneousPath
public import Mathlib.Combinatorics.Quiver.Path.Vertices
public import Mei.Combinatorics.Quiver.Path

/-!
# Common admissible paths for wall families

`CommonWallComplement W` consists of the points allowed for every family `W j`.
An edge is a segment admissible for each family separately. Thus a quiver path
records one vertex list, with an admissible realization in every family. No
transversality to intersections between different families is imposed.

Projection to a family preserves vertices, concatenation and reversal. For
countably many finite codimension-one polyhedral families, any two common
allowed points are joined by such a path with two edges. This applies
`dense_setOf_forall_admissiblePairs`, based on Mathlib's Baire theorem, to the
existing `WallComplement.AdmissibleSegment` predicates.
-/

public section

open Set

namespace Mei.Convex

variable {V J : Type*} {I : J → Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A point allowed for every wall family. Edges are admissible in each family
separately, rather than in their union. -/
@[ext]
structure CommonWallComplement (W : ∀ j, I j → Set V) where
  /-- The common ambient point. -/
  val : V
  /-- The point lies on no wall in any family. -/
  notMem : ∀ j i, val ∉ W j i

namespace CommonWallComplement

variable {W : ∀ j, I j → Set V}

/-- View a common allowed point in one wall complement. -/
-- Endpoints must compute when restricting a projected path to a smaller family.
@[expose]
def projection (j : J) (x : CommonWallComplement W) : WallComplement (W j) :=
  ⟨x.val, x.notMem j⟩

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
@[simp]
theorem projection_val (j : J) (x : CommonWallComplement W) :
    (projection j x).val = x.val := (rfl)

/-- A common edge is one geometric segment admissible in every family. -/
instance : Quiver (CommonWallComplement W) where
  Hom x y := PLift (∀ j, WallComplement.AdmissibleSegment (projection j x) (projection j y))

/-- Forget all admissibility conditions except those for the selected family. -/
-- Objects must compute to the projected endpoints in dependent path types.
@[expose]
def projectionPrefunctor (j : J) : CommonWallComplement W ⥤q WallComplement (W j) where
  obj := projection j
  map e := ⟨e.down j⟩

@[simp]
theorem projectionPrefunctor_obj (j : J) (x : CommonWallComplement W) :
    (projectionPrefunctor j).obj x = projection j x := (rfl)

/-- Reversal preserves simultaneous admissibility. -/
instance : Quiver.HasInvolutiveReverse (CommonWallComplement W) where
  reverse' e := ⟨fun j => (e.down j).symm⟩
  inv' _ := PLift.ext (Subsingleton.elim _ _)

/-- Projections preserve reversal of edges, hence also reversal of paths. -/
instance (j : J) : (projectionPrefunctor (W := W) j).MapReverse where
  map_reverse' _ := PLift.ext (Subsingleton.elim _ _)

variable {x y : CommonWallComplement W}

/-- Every projected path has precisely the original ambient vertex list. -/
@[simp]
theorem vertices_projection (j : J) (p : Quiver.Path x y) :
    ((projectionPrefunctor j).mapPath p).vertices.map WallComplement.val =
      p.vertices.map CommonWallComplement.val := by
  induction p with
  | nil => simp
  | cons p e ih => simp [ih]

/-- Countably many finite polyhedral wall families admit a common two-edge path
between any common allowed endpoints. -/
theorem exists_length_eq_two [FiniteDimensional ℝ V] [Countable J]
    [∀ j, Finite (I j)]
    (hpoly : ∀ j i, TauCeti.IsConvexPolyhedron (W j i))
    (hdim : ∀ j i, Module.finrank ℝ (affineSpan ℝ (W j i)).direction + 1 =
      Module.finrank ℝ V)
    (x y : CommonWallComplement W) : ∃ p : Quiver.Path x y, p.length = 2 := by
  obtain ⟨v, hv⟩ := (dense_setOf_forall_admissiblePairs W hpoly hdim x.notMem y.notMem).nonempty
  have hvW : ∀ j i, v ∉ W j i := by
    intro j
    obtain ⟨_, hvj, _⟩ := mem_admissiblePairs.mp (hv j).1
    exact hvj
  let z : CommonWallComplement W := ⟨v, hvW⟩
  have hxz : x ⟶ z := ⟨fun j => (mem_admissiblePairs_iff _ _).mp (hv j).1⟩
  have hzy : z ⟶ y := ⟨fun j => (mem_admissiblePairs_iff _ _).mp (hv j).2⟩
  exact ⟨(Quiver.Path.nil.cons hxz).cons hzy, rfl⟩

end CommonWallComplement
end Mei.Convex
