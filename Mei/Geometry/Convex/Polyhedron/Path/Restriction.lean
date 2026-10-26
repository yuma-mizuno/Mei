/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.Path.Product
import Mei.Algebra.BigOperators.Group.Finset.Ordered

/-!
# Deleting identity labels from indexed wall products

An injective restriction of a finite indexed wall family preserves transport if
every deleted label is the identity. At simultaneous crossings, only the deleted
factors disappear; an entire event disappears when none of its walls remain.
Vertices, segments, crossing parameters and the order of surviving events stay fixed.

The construction uses `WallComplement.restrictPrefunctor`,
`Finset.noncommProd_subset` for simultaneous factors, and
`Finset.prod_map_sort_subset` for ordered events. It applies to arbitrary wall
families with commuting coplanar labels, independently of polyhedral presentations.
-/

public section

noncomputable section

open Set Mei.Convex

namespace Mei.Convex.WallComplement

variable {V ι κ G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [Finite ι] [Finite κ] [Group G] {W : ι → Set V}
  (ν : ι → V →ₗ[ℝ] ℝ) (label : ι → G)
  (hcomm : ∀ i j, affineSpan ℝ (W i) = affineSpan ℝ (W j) →
    Commute (label i) (label j))
  (f : κ → ι) (hf : Function.Injective f)
  (hlabel : ∀ i, i ∉ range f → label i = 1)
  {x y : WallComplement W}

include hf hlabel in
/-- Removing identity-labelled walls preserves each combined simultaneous product. -/
@[simp]
theorem crossingEventProduct_restrict (e : x ⟶ y) (t : ℝ) :
    crossingEventProduct (ν ∘ f) (label ∘ f)
      (fun i j h => hcomm (f i) (f j) h) ((restrictPrefunctor W f).map e) t =
        crossingEventProduct ν label hcomm e t := by
  classical
  let emb : κ × ℤ ↪ ι × ℤ := ⟨fun a => (f a.1, a.2), by
    rintro ⟨a, r⟩ ⟨b, s⟩ hab
    exact Prod.ext (hf (Prod.mk.inj hab).1) (Prod.mk.inj hab).2⟩
  let S := signedCrossingEvent (ν ∘ f)
    ((restrictPrefunctor W f).obj x) ((restrictPrefunctor W f).obj y) t
  let T := signedCrossingEvent ν x y t
  have hs : S.map emb ⊆ T := by
    intro a ha
    obtain ⟨⟨j, r⟩, hj, rfl⟩ := Finset.mem_map.mp ha
    obtain ⟨hj, hr⟩ := (mem_signedCrossingEvent _ _ _ _ j r).mp hj
    exact (mem_signedCrossingEvent ν x y t (f j) r).mpr
      ⟨by simpa only [mem_crossings, restrictPrefunctor_obj_val, Function.comp_apply] using hj,
        by simpa using hr⟩
  have hz : ∀ a ∈ T, a ∉ S.map emb → label a.1 ^ a.2 = 1 := by
    intro ⟨i, r⟩ hi hnot
    have hir : i ∉ range f := by
      rintro ⟨j, rfl⟩
      apply hnot
      refine Finset.mem_map.mpr ⟨(j, r), ?_, rfl⟩
      obtain ⟨hi, hr⟩ := (mem_signedCrossingEvent ν x y t (f j) r).mp hi
      exact (mem_signedCrossingEvent _ _ _ _ j r).mpr
        ⟨by simpa only [mem_crossings, restrictPrefunctor_obj_val, Function.comp_apply] using hi,
          by simpa using hr⟩
    simp [hlabel i hir]
  have hc := signedCrossingEvent_pairwise ν label hcomm e t
  rw [crossingEventProduct_eq_noncommProd _ _ _ _ _
    (fun a ha b hb hab => hc (hs (Finset.mem_map.mpr ⟨a, ha, rfl⟩))
      (hs (Finset.mem_map.mpr ⟨b, hb, rfl⟩)) (emb.injective.ne hab))]
  exact (Finset.noncommProd_map S emb (fun a => label a.1 ^ a.2)
    (hc.mono (Finset.coe_subset.mpr hs))).symm.trans
      ((Finset.noncommProd_subset hs _ hc hz).trans
        (crossingEventProduct_eq_noncommProd ν label hcomm e t hc).symm)

include hf hlabel in
/-- Deleting identity walls preserves segment transport even when entire events vanish. -/
@[simp]
theorem segmentPathProduct_restrict (e : x ⟶ y) :
    segmentPathProduct (ν ∘ f) (label ∘ f)
      (fun i j h => hcomm (f i) (f j) h) ((restrictPrefunctor W f).map e) =
        segmentPathProduct ν label hcomm e := by
  classical
  let e' := (restrictPrefunctor W f).map e
  let S := (orderedCrossingTimes e').toFinset
  let T := (orderedCrossingTimes e).toFinset
  have hs : S ⊆ T := by
    intro t ht
    obtain ⟨j, hj⟩ := (mem_orderedCrossingTimes e' t).mp (List.mem_toFinset.mp ht)
    exact List.mem_toFinset.mpr ((mem_orderedCrossingTimes e t).mpr
      ⟨f j, by
        simpa only [mem_crossings, restrictPrefunctor_obj_val, Function.comp_apply] using hj⟩)
  have hz : ∀ t ∈ T, t ∉ S → (crossingEventProduct ν label hcomm e t)⁻¹ = 1 := by
    intro t _ ht
    have he : signedCrossingEvent (ν ∘ f)
        ((restrictPrefunctor W f).obj x) ((restrictPrefunctor W f).obj y) t = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      rintro ⟨j, r⟩ hj
      exact ht (List.mem_toFinset.mpr ((mem_orderedCrossingTimes e' t).mpr
        ⟨j, ((mem_signedCrossingEvent _ _ _ _ j r).mp hj).1⟩))
    rw [← crossingEventProduct_restrict ν label hcomm f hf hlabel e t,
      crossingEventProduct_empty _ _ _ _ _ he, inv_one]
  have hS : S.sort = orderedCrossingTimes e' := by
    exact (Finset.sortedLT_sort S).pairwise.eq_of_mem_iff
      (pairwise_orderedCrossingTimes e') (by simp [S])
  have hT : T.sort = orderedCrossingTimes e := by
    exact (Finset.sortedLT_sort T).pairwise.eq_of_mem_iff
      (pairwise_orderedCrossingTimes e) (by simp [T])
  have hevent : crossingEventProduct (ν ∘ f) (label ∘ f)
      (fun i j h => hcomm (f i) (f j) h) e' = crossingEventProduct ν label hcomm e :=
    funext (crossingEventProduct_restrict ν label hcomm f hf hlabel e)
  rw [segmentPathProduct_def, segmentPathProduct_def, hevent]
  simp only [List.map_reverse, List.prod_reverse_noncomm, List.map_map, Function.comp_def]
  exact congrArg Inv.inv (by
    simpa only [hS, hT] using Finset.prod_map_sort_subset hs
      (fun t => (crossingEventProduct ν label hcomm e t)⁻¹) hz)

end Mei.Convex.WallComplement

namespace Quiver.Path

open Mei.Convex.WallComplement

variable {V ι κ G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [Finite ι] [Finite κ] [Group G] {W : ι → Set V}

/-- An injective restriction retaining every nonidentity label preserves polygonal transport. -/
@[simp]
theorem wallPathProduct_restrict (ν : ι → V →ₗ[ℝ] ℝ) (label : ι → G)
    (hcomm : ∀ i j, affineSpan ℝ (W i) = affineSpan ℝ (W j) →
      Commute (label i) (label j)) (f : κ → ι) (hf : Function.Injective f)
    (hlabel : ∀ i, i ∉ range f → label i = 1)
    {x y : WallComplement W} (p : AdmissiblePLPath x y) :
    ((restrictPrefunctor W f).mapPath p).wallPathProduct (ν ∘ f) (label ∘ f)
      (fun i j h => hcomm (f i) (f j) h) = p.wallPathProduct ν label hcomm := by
  induction p with
  | nil => simp
  | cons p e ih =>
    simp only [Prefunctor.mapPath_cons, wallPathProduct_cons, ih,
      segmentPathProduct_restrict ν label hcomm f hf hlabel]

end Quiver.Path
