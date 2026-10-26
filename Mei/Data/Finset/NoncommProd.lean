/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Data.Finset.NoncommProd

/-!
# Reindexing and identity factors in products of commuting elements

Mathlib's `Finset.noncommProd` multiplies a finite commuting family in an arbitrary
monoid. Here embeddings reindex these products, adjoining identity factors preserves
them, and inversion in a group inverts each factor. These formulas allow unordered
simultaneous wall crossings to be restricted, transported and reversed without
choosing an order on the walls.
-/

public section

namespace Finset

variable {α β G : Type*}

/-- Adjoining identity factors preserves an unordered product of commuting elements. -/
theorem noncommProd_subset [Monoid G] {s t : Finset α} (hst : s ⊆ t) (f : α → G)
    (comm : (t : Set α).Pairwise (fun a b => Commute (f a) (f b)))
    (hf : ∀ a ∈ t, a ∉ s → f a = 1) :
    s.noncommProd f (comm.mono (coe_subset.mpr hst)) = t.noncommProd f comm := by
  classical
  have hc : ((s ∪ t \ s : Finset α) : Set α).Pairwise (fun a b => Commute (f a) (f b)) := by
    simpa only [union_sdiff_of_subset hst] using comm
  have hz : (t \ s).noncommProd f (comm.mono (coe_subset.mpr sdiff_subset)) = 1 := by
    simpa using noncommProd_eq_pow_card (t \ s) f _ 1
      (fun a ha => hf a (mem_sdiff.mp ha).1 (mem_sdiff.mp ha).2)
  have hu := noncommProd_union_of_disjoint (disjoint_sdiff_self_right : Disjoint s (t \ s)) f hc
  simpa only [union_sdiff_of_subset hst, hz, mul_one] using hu.symm

/-- Reindex a product of commuting elements along an embedding. -/
theorem noncommProd_map [Monoid G] (s : Finset α) (e : α ↪ β) (f : β → G)
    (comm : (s.map e : Set β).Pairwise (fun a b => Commute (f a) (f b))) :
    (s.map e).noncommProd f comm = s.noncommProd (fun a => f (e a))
      (fun a ha b hb hab => comm (mem_map.mpr ⟨a, ha, rfl⟩)
        (mem_map.mpr ⟨b, hb, rfl⟩) (e.injective.ne hab)) := by
  simp only [noncommProd, map_val, Multiset.map_map, Function.comp_def]

/-- Inverting every member of a commuting family inverts its unordered product. -/
theorem noncommProd_inv [DivisionMonoid G] (s : Finset α) (f : α → G)
    (comm : (s : Set α).Pairwise (fun a b => Commute (f a) (f b))) :
    s.noncommProd (fun a => (f a)⁻¹) (fun _ ha _ hb hab => (comm ha hb hab).inv_inv) =
      (s.noncommProd f comm)⁻¹ := by
  induction s using Finset.cons_induction_on with
  | empty => exact (noncommProd_empty _ _).trans (inv_one.symm)
  | cons a s ha ih =>
    have hc : (s : Set α).Pairwise (fun a b => Commute (f a) (f b)) :=
      comm.mono (fun _ => mem_cons_of_mem)
    calc
      _ = (f a)⁻¹ * s.noncommProd (fun a => (f a)⁻¹)
          (fun _ hx _ hy hxy => (hc hx hy hxy).inv_inv) := noncommProd_cons _ _ _ _ _
      _ = (f a)⁻¹ * (s.noncommProd f hc)⁻¹ := by rw [ih]
      _ = (s.noncommProd f hc)⁻¹ * (f a)⁻¹ :=
        (noncommProd_commute s f hc (f a)
          (fun b hb => comm.forall₂ (mem_cons_self _ _) (mem_cons_of_mem hb))).inv_inv.eq
      _ = _ := by rw [noncommProd_cons, mul_inv_rev]

end Finset
