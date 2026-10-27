/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Noncommutative boundary relations for rectangular grids

If the two routes around each grid cell have equal products, the two routes
around the whole rectangle have equal products. More generally, the outer
boundary word lies in the normal closure of the cell boundary words. This is
the cancellation of internal edges needed when subdividing a polygonal filling
into local relations. Products here put the first edge on the left; inverting
all edge labels gives the convention for labels acting on the left.

The proof uses Mathlib's `List.prod_range_succ` and the quotient by a normal
subgroup. No commutation between unrelated edge labels is assumed.
-/

public section

namespace Mei

variable {G : Type*}

/-- Equality of the two routes through each cell implies equality of the two
outer routes through a rectangular grid. Horizontal and vertical labels are
multiplied in increasing index order, with the first edge on the left. -/
theorem grid_boundary_eq_of_cell_eq [Monoid G] (a b : ℕ → ℕ → G) (m n : ℕ)
    (hcell : ∀ i < m, ∀ j < n, a i j * b i (j + 1) = b i j * a (i + 1) j) :
    ((List.range n).map (a 0)).prod * ((List.range m).map (b · n)).prod =
      ((List.range m).map (b · 0)).prod * ((List.range n).map (a m)).prod := by
  -- First move one vertical edge through an entire horizontal row.
  have hrow (i : ℕ) (hi : i < m) : ∀ k ≤ n,
      ((List.range k).map (a i)).prod * b i k =
        b i 0 * ((List.range k).map (a (i + 1))).prod := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      calc
        _ = ((List.range k).map (a i)).prod * (a i k * b i (k + 1)) := by
          rw [List.prod_range_succ, mul_assoc]
        _ = ((List.range k).map (a i)).prod * (b i k * a (i + 1) k) := by
          rw [hcell i hi k (by omega)]
        _ = b i 0 * ((List.range (k + 1)).map (a (i + 1))).prod := by
          rw [← mul_assoc, ih (by omega), List.prod_range_succ, mul_assoc]
  -- Then move the bottom row past the successive vertical edges of the rectangle.
  have hrect : ∀ k ≤ m,
      ((List.range n).map (a 0)).prod * ((List.range k).map (b · n)).prod =
        ((List.range k).map (b · 0)).prod * ((List.range n).map (a k)).prod := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      calc
        _ = (((List.range n).map (a 0)).prod * ((List.range k).map (b · n)).prod) *
            b k n := by rw [List.prod_range_succ, mul_assoc]
        _ = (((List.range k).map (b · 0)).prod * ((List.range n).map (a k)).prod) *
            b k n := by rw [ih (by omega)]
        _ = ((List.range (k + 1)).map (b · 0)).prod *
            ((List.range n).map (a (k + 1))).prod := by
          rw [mul_assoc, hrow k (by omega) n le_rfl, List.prod_range_succ, mul_assoc]
  exact hrect m le_rfl

/-- The outer boundary of a rectangular grid lies in the normal closure of
its cell boundary words. Empty rows and columns are included. -/
theorem grid_boundary_mem_normalClosure [Group G] (a b : ℕ → ℕ → G) (m n : ℕ) :
    ((List.range n).map (a 0)).prod * ((List.range m).map (b · n)).prod *
        (((List.range n).map (a m)).prod)⁻¹ * (((List.range m).map (b · 0)).prod)⁻¹ ∈
      Subgroup.normalClosure
        {g | ∃ i < m, ∃ j < n,
          g = a i j * b i (j + 1) * (a (i + 1) j)⁻¹ * (b i j)⁻¹} := by
  let K := Subgroup.normalClosure
    {g | ∃ i < m, ∃ j < n,
      g = a i j * b i (j + 1) * (a (i + 1) j)⁻¹ * (b i j)⁻¹}
  let q := QuotientGroup.mk' K
  have hcell (i) (hi : i < m) (j) (hj : j < n) :
      q (a i j) * q (b i (j + 1)) = q (b i j) * q (a (i + 1) j) := by
    have hm : a i j * b i (j + 1) * (a (i + 1) j)⁻¹ * (b i j)⁻¹ ∈ K :=
      Subgroup.subset_normalClosure ⟨i, hi, j, hj, rfl⟩
    have he := (QuotientGroup.eq_one_iff _).mpr hm
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, mul_inv_eq_iff_eq_mul,
      one_mul] at he
    exact he
  have hrect := grid_boundary_eq_of_cell_eq
    (fun i j => q (a i j)) (fun i j => q (b i j)) m n hcell
  apply (QuotientGroup.eq_one_iff _).mp
  have he : q (((List.range n).map (a 0)).prod *
      ((List.range m).map (b · n)).prod * (((List.range n).map (a m)).prod)⁻¹ *
      (((List.range m).map (b · 0)).prod)⁻¹) = 1 := by
    simp only [map_mul, map_inv, map_list_prod, List.map_map, Function.comp_def]
    rw [hrect]
    simp [mul_assoc]
  exact he

end Mei
