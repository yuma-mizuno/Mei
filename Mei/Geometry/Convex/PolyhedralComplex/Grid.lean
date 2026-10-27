/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.CrossingWord
public import Mei.GroupTheory.Grid

/-!
# Crossing words under rectangular subdivision

For a rectangular grid of admissible segments, the word around the outer
boundary lies in the normal closure of the words around its cells. Interior
edges cancel with their reverses without requiring commutative wall labels.
This permits a subdivided filling to be reduced to its local boundary relations.

The construction uses `Mei.grid_boundary_mem_normalClosure`, the sequence-path
API, and the concatenation and reversal laws for crossing words. Inverting the
edge words changes from the group-product convention to the convention that
the first crossing is the rightmost factor. No geometric filling or local
consistency condition is assumed by this combinatorial subdivision result.
-/

public section

open Set Mei.Convex

namespace Quiver.Path

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}
  {C : Mei.FinitePolyhedralComplex h}

/-- The word along a sequence of edges is the inverse of the increasing-order
product of the inverse edge words, so the first crossing is the rightmost factor. -/
@[simp]
theorem crossingWord_ofSeq
    (x : ℕ → WallComplement (fun P : C.walls => (P : Set V)))
    (e : ∀ j, x j ⟶ x (j + 1)) (n : ℕ) (ν : C.walls → V →ₗ[ℝ] ℝ) :
    (ofSeq x e n).crossingWord ν =
      (((List.range n).map fun j => (C.segmentCrossingWord ν (e j))⁻¹).prod)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, List.prod_range_succ]

end Quiver.Path

namespace Mei.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- The actual outer crossing word of an admissible rectangular grid is generated
normally by its actual four-edge cell words. The geometry may be degenerate or
self-overlapping, and empty rows and columns are allowed. -/
theorem crossingWord_grid_boundary_mem_normalClosure (C : FinitePolyhedralComplex h)
    (ν : C.walls → V →ₗ[ℝ] ℝ)
    (hν : ∀ P, (ν P).ker = (affineSpan ℝ (P : Set V)).direction)
    (x : ℕ → ℕ → WallComplement (fun P : C.walls => (P : Set V)))
    (e : ∀ i j, x i j ⟶ x i (j + 1))
    (f : ∀ i j, x i j ⟶ x (i + 1) j) (m n : ℕ) :
    let row := fun i => Quiver.Path.ofSeq (x i) (e i) n
    let col := fun j => Quiver.Path.ofSeq (fun i => x i j) (f · j) m
    let cell := fun i j => (((e i j).toPath.cons (f i (j + 1))).cons
      (Quiver.reverse (e (i + 1) j))).cons (Quiver.reverse (f i j))
    (((row 0).comp (col n)).comp ((row m).reverse.comp (col 0).reverse)).crossingWord ν ∈
      Subgroup.normalClosure {g | ∃ i < m, ∃ j < n, g = (cell i j).crossingWord ν} := by
  dsimp only
  let a := fun i j => (C.segmentCrossingWord ν (e i j))⁻¹
  let b := fun i j => (C.segmentCrossingWord ν (f i j))⁻¹
  let cell := fun i j => (((e i j).toPath.cons (f i (j + 1))).cons
    (Quiver.reverse (e (i + 1) j))).cons (Quiver.reverse (f i j))
  let K := Subgroup.normalClosure {g | ∃ i < m, ∃ j < n, g = (cell i j).crossingWord ν}
  -- The increasing-order algebraic cell word is the inverse of its geometric word.
  have hle : Subgroup.normalClosure
      {g | ∃ i < m, ∃ j < n,
        g = a i j * b i (j + 1) * (a (i + 1) j)⁻¹ * (b i j)⁻¹} ≤ K := by
    apply Subgroup.normalClosure_le_normal
    rintro g ⟨i, hi, j, hj, rfl⟩
    have hc : (cell i j).crossingWord ν ∈ K :=
      Subgroup.subset_normalClosure ⟨i, hi, j, hj, rfl⟩
    have he : a i j * b i (j + 1) * (a (i + 1) j)⁻¹ * (b i j)⁻¹ =
        ((cell i j).crossingWord ν)⁻¹ := by
      simp only [cell, Quiver.Path.crossingWord_cons, Quiver.Hom.toPath,
        Quiver.Path.crossingWord_nil, mul_one, C.segmentCrossingWord_reverse ν hν,
        mul_inv_rev, inv_inv, a, b, mul_assoc]
    rw [he]
    exact K.inv_mem hc
  have hm := K.inv_mem (hle (Mei.grid_boundary_mem_normalClosure a b m n))
  simpa only [Quiver.Path.crossingWord_comp, Quiver.Path.crossingWord_reverse _ ν hν,
    Quiver.Path.crossingWord_ofSeq, mul_inv_rev, inv_inv, a, b, mul_assoc] using hm

end Mei.FinitePolyhedralComplex
