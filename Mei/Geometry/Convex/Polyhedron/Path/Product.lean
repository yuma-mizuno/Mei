/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.Polyhedron.CrossingEvents
public import Mei.Data.Finset.NoncommProd
public import Mathlib.Combinatorics.Quiver.Path.Weight

/-!
# Path products for indexed wall families

Labels of walls with the same affine span are assumed to commute. At each
crossing time the signed labels therefore have an unordered product, including
all coincident indexed walls. Multiplying these event products in reverse time
order gives the segment transport; concatenating segments gives polygonal
transport. The first crossing is rightmost and a positive normal velocity gives
the inverse label. Reversal inverts transport, and group homomorphisms preserve it.

This evaluates `WallComplement.signedCrossingEvent` using Mathlib's
`Finset.noncommProd`, rather than choosing an enumeration of simultaneous walls.
No commutation is required between events at different times. Polygonal transport
uses Mathlib's `Quiver.Path.weight` in the opposite group to reverse multiplication order.
-/

public section

noncomputable section

open Set

namespace Mei.Convex.WallComplement

variable {V ι G K : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι]
  [Group G] [Group K] {W : ι → Set V}
  (ν : ι → V →ₗ[ℝ] ℝ) (label : ι → G)
  (hcomm : ∀ i j, affineSpan ℝ (W i) =
    affineSpan ℝ (W j) → Commute (label i) (label j))
  {x y : WallComplement W}

include hcomm in
/-- All signed labels at one crossing time commute, including coincident walls. -/
theorem signedCrossingEvent_pairwise (e : x ⟶ y) (t : ℝ) :
    (signedCrossingEvent ν x y t : Set (ι × ℤ)).Pairwise
      (fun a b => Commute (label a.1 ^ a.2) (label b.1 ^ b.2)) := by
  intro a ha b hb _
  have ha := ((mem_signedCrossingEvent ν x y t a.1 a.2).mp ha).1
  have hb := ((mem_signedCrossingEvent ν x y t b.1 b.2).mp hb).1
  exact (hcomm a.1 b.1
    (affineSpan_eq_of_mem_crossingWalls e
      ((mem_crossingWalls x y t a.1).mpr ha)
      ((mem_crossingWalls x y t b.1).mpr hb))).zpow_zpow _ _

/-- Multiply all signed labels at a single time, without ordering simultaneous walls. -/
def crossingEventProduct (e : x ⟶ y) (t : ℝ) : G :=
  (signedCrossingEvent ν x y t).noncommProd (fun a => label a.1 ^ a.2)
    (signedCrossingEvent_pairwise ν label hcomm e t)

/-- Any proof that the signed factors commute computes the same event product. -/
theorem crossingEventProduct_eq_noncommProd (e : x ⟶ y) (t : ℝ)
    (comm : (signedCrossingEvent ν x y t : Set (ι × ℤ)).Pairwise
      (fun a b => Commute (label a.1 ^ a.2) (label b.1 ^ b.2))) :
    crossingEventProduct ν label hcomm e t =
      (signedCrossingEvent ν x y t).noncommProd (fun a => label a.1 ^ a.2) comm := (rfl)

/-- A time with no signed crossing contributes the identity. -/
@[simp]
theorem crossingEventProduct_empty (e : x ⟶ y) (t : ℝ)
    (ht : signedCrossingEvent ν x y t = ∅) :
    crossingEventProduct ν label hcomm e t = 1 := by
  unfold crossingEventProduct
  exact (Finset.noncommProd_congr ht (fun _ _ => rfl) _).trans
    (Finset.noncommProd_empty _ _)

/-- Every enumeration without repetitions gives the same simultaneous crossing product. -/
theorem crossingEventProduct_eq_prod (e : x ⟶ y) (t : ℝ) (l : List (ι × ℤ))
    (hl : l.Nodup) (hm : ∀ a, a ∈ l ↔ a ∈ signedCrossingEvent ν x y t) :
    crossingEventProduct ν label hcomm e t = (l.map fun a => label a.1 ^ a.2).prod := by
  classical
  have hs : l.toFinset = signedCrossingEvent ν x y t := by ext a; simpa using hm a
  unfold crossingEventProduct
  exact (Finset.noncommProd_congr hs.symm (fun _ _ => rfl) _).trans
    (Finset.noncommProd_toFinset l _ _ hl)

/-- An isolated signed crossing contributes precisely the corresponding power of its label. -/
theorem crossingEventProduct_singleton (e : x ⟶ y) (t : ℝ) (a : ι × ℤ)
    (ha : signedCrossingEvent ν x y t = {a}) :
    crossingEventProduct ν label hcomm e t = label a.1 ^ a.2 := by
  unfold crossingEventProduct
  simp only [ha, Finset.noncommProd_singleton]

/-- Relabelling commutes with the simultaneous product. -/
@[simp]
theorem map_crossingEventProduct (f : G →* K) (e : x ⟶ y) (t : ℝ) :
    f (crossingEventProduct ν label hcomm e t) =
      crossingEventProduct ν (fun i => f (label i))
        (fun i j h => (hcomm i j h).map f) e t := by
  simp only [crossingEventProduct, Finset.map_noncommProd, map_zpow]

/-- Reversing a segment inverts each combined event and reflects its time. -/
theorem crossingEventProduct_reverse
    (hν : ∀ i, LinearMap.ker (ν i) = (affineSpan ℝ (W i)).direction)
    (e : x ⟶ y) (t : ℝ) :
    crossingEventProduct ν label hcomm (Quiver.reverse e) t =
      (crossingEventProduct ν label hcomm e (1 - t))⁻¹ := by
  let S := signedCrossingEvent ν x y (1 - t)
  let f : ι × ℤ → G := fun a => label a.1 ^ a.2
  let emb := (Equiv.prodCongr (Equiv.refl ι) (Equiv.neg ℤ)).toEmbedding
  have hc := signedCrossingEvent_pairwise ν label hcomm e (1 - t)
  have hc' : (S.map emb : Set (ι × ℤ)).Pairwise (fun a b => Commute (f a) (f b)) := by
    intro a ha b hb _
    obtain ⟨a', ha', haa⟩ := Finset.mem_map.mp ha
    obtain ⟨b', hb', hbb⟩ := Finset.mem_map.mp hb
    simpa only [← haa, ← hbb, f, emb, Equiv.toEmbedding_apply, Equiv.prodCongr_apply,
      Equiv.refl_apply, Equiv.neg_apply, Prod.map_fst, Prod.map_snd, zpow_neg] using
      (hc.forall₂ ha' hb').inv_inv
  calc
    _ = (S.map emb).noncommProd f hc' :=
      Finset.noncommProd_congr (signedCrossingEvent_swap ν hν e t) (fun _ _ => rfl) _
    _ = S.noncommProd (fun a => f (emb a)) _ :=
      Finset.noncommProd_map S emb f hc'
    _ = _ := by
      simpa only [f, emb, Equiv.toEmbedding_apply, Equiv.prodCongr_apply,
        Prod.map_fst, Prod.map_snd,
        Equiv.refl_apply, Equiv.neg_apply, zpow_neg, crossingEventProduct, S] using
          Finset.noncommProd_inv S f hc

/-- The segment product, with the first crossing rightmost. -/
def segmentPathProduct (e : x ⟶ y) : G :=
  ((orderedCrossingTimes e).reverse.map (crossingEventProduct ν label hcomm e)).prod

/-- Segment transport is the reverse-time product of the simultaneous events. -/
theorem segmentPathProduct_def (e : x ⟶ y) :
    segmentPathProduct ν label hcomm e =
      ((orderedCrossingTimes e).reverse.map (crossingEventProduct ν label hcomm e)).prod := (rfl)

/-- Homomorphisms preserve the segment transport. -/
@[simp]
theorem map_segmentPathProduct (f : G →* K) (e : x ⟶ y) :
    f (segmentPathProduct ν label hcomm e) =
      segmentPathProduct ν (fun i => f (label i))
        (fun i j h => (hcomm i j h).map f) e := by
  simp only [segmentPathProduct, map_list_prod, List.map_map, Function.comp_def,
    map_crossingEventProduct]

/-- Reversal inverts segment transport, including simultaneous crossings. -/
@[simp]
theorem segmentPathProduct_reverse
    (hν : ∀ i, LinearMap.ker (ν i) = (affineSpan ℝ (W i)).direction)
    (e : x ⟶ y) :
    segmentPathProduct ν label hcomm (Quiver.reverse e) =
      (segmentPathProduct ν label hcomm e)⁻¹ := by
  simp only [segmentPathProduct, orderedCrossingTimes_reverse, List.map_reverse,
    List.reverse_reverse, List.map_map, Function.comp_def,
    crossingEventProduct_reverse ν label hcomm hν,
    sub_sub_cancel, List.prod_inv_reverse]

end Mei.Convex.WallComplement

namespace Quiver.Path

open Mei.Convex WallComplement

variable {V ι G K : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Finite ι]
  [Group G] [Group K] {W : ι → Set V}
  (ν : ι → V →ₗ[ℝ] ℝ) (label : ι → G)
  (hcomm : ∀ i j, affineSpan ℝ (W i) =
    affineSpan ℝ (W j) → Commute (label i) (label j))
  {x y z : WallComplement W}

/-- Polygonal wall transport, retaining repeated visits and combined simultaneous events. -/
def wallPathProduct (p : AdmissiblePLPath x y) : G :=
  MulOpposite.unop (p.weight (fun e => MulOpposite.op (segmentPathProduct ν label hcomm e)))

@[simp]
theorem wallPathProduct_nil :
    (Quiver.Path.nil : AdmissiblePLPath x x).wallPathProduct ν label hcomm = 1 := by
  simp only [wallPathProduct, weight_nil, MulOpposite.unop_one]

@[simp]
theorem wallPathProduct_cons (p : AdmissiblePLPath x y) (e : y ⟶ z) :
    (p.cons e).wallPathProduct ν label hcomm =
      segmentPathProduct ν label hcomm e * p.wallPathProduct ν label hcomm := by
  simp only [wallPathProduct, weight_cons, MulOpposite.unop_mul, MulOpposite.unop_op]

@[simp]
theorem wallPathProduct_toPath (e : x ⟶ y) :
    e.toPath.wallPathProduct ν label hcomm = segmentPathProduct ν label hcomm e := by
  simp [Quiver.Hom.toPath]

/-- The second path acts on the left of the first path's transport. -/
@[simp]
theorem wallPathProduct_comp (p : AdmissiblePLPath x y) (q : AdmissiblePLPath y z) :
    (p.comp q).wallPathProduct ν label hcomm =
      q.wallPathProduct ν label hcomm * p.wallPathProduct ν label hcomm := by
  simp only [wallPathProduct, weight_comp, MulOpposite.unop_mul]

/-- Reversing every segment reverses the total transport. -/
@[simp]
theorem wallPathProduct_reverse
    (hν : ∀ i, LinearMap.ker (ν i) = (affineSpan ℝ (W i)).direction)
    (p : AdmissiblePLPath x y) :
    p.reverse.wallPathProduct ν label hcomm = (p.wallPathProduct ν label hcomm)⁻¹ := by
  induction p with
  | nil => simp [Quiver.Path.reverse]
  | cons p e ih =>
    simp [Quiver.Path.reverse, ih, segmentPathProduct_reverse ν label hcomm hν, mul_inv_rev]

/-- Group homomorphisms preserve all polygonal transports. -/
@[simp]
theorem map_wallPathProduct (f : G →* K) (p : AdmissiblePLPath x y) :
    f (p.wallPathProduct ν label hcomm) =
      p.wallPathProduct ν (fun i => f (label i)) (fun i j h => (hcomm i j h).map f) := by
  induction p with
  | nil => simp
  | cons p e ih => simp [map_segmentPathProduct, ih]

end Quiver.Path
