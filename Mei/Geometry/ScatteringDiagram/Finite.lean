/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mei.Geometry.Convex.PolyhedralComplex.CrossingWord

/-!
# Finite labelled wall diagrams

A finite wall diagram assigns a normal and a group element to each wall of a
finite polyhedral complex. Its path product evaluates the geometric crossing
word by Mathlib's `FreeGroup.lift`. The first crossing is the rightmost factor:
a crossing with positive normal velocity contributes the inverse wall label.

Path products respect concatenation, reversal and homomorphisms of label groups.
Positive rescaling of normals, or reversing a normal while inverting its label,
preserves every path product. Consistency means endpoint independence and is
equivalent to triviality of all admissible loop products. No commutativity of
labels or faithful coefficient action is assumed.

Normals are explicit linear functionals presenting the coorientations. Products
are independent of their positive scale.
-/

public section

noncomputable section

open Mei.Convex

namespace Mei

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : TauCeti.Toric.IsIntegralLattice i}

/-- Group-labelled cooriented walls on a fixed finite polyhedral complex. -/
@[ext]
structure FiniteWallDiagram (C : FinitePolyhedralComplex h) (G : Type*) where
  /-- A linear normal presenting each wall's coorientation. -/
  normal : C.walls → V →ₗ[ℝ] ℝ
  /-- The normal vanishes precisely in the wall direction. -/
  ker_normal : ∀ P, LinearMap.ker (normal P) = (affineSpan ℝ (P : Set V)).direction
  /-- The wall label, acting on coefficients from the left. -/
  label : C.walls → G

namespace FiniteWallDiagram

variable {C : FinitePolyhedralComplex h} {G H K : Type*} [Group G] [Group H] [Group K]
  (D : FiniteWallDiagram C G)
  {x y z : WallComplement (fun P : C.walls => (P : Set V))}

omit [Group G] in
/-- Every chosen wall normal is nonzero, since its kernel has codimension one. -/
@[simp]
theorem normal_ne_zero (P : C.walls) : D.normal P ≠ 0 := by
  intro hz
  have hd := C.finrank_direction_add_one_of_mem_walls P.property
  have he : (affineSpan ℝ (P : Set V)).direction = ⊤ := by
    rw [← D.ker_normal P, hz, LinearMap.ker_zero]
  rw [he, finrank_top] at hd
  omega

/-- Evaluate the signed crossing word in the wall-label group. -/
def pathProduct (p : AdmissiblePLPath x y) : G :=
  FreeGroup.lift D.label (p.crossingWord D.normal)

/-- Path products are the free-group evaluation of geometric crossing words. -/
theorem pathProduct_def (p : AdmissiblePLPath x y) :
    D.pathProduct p = FreeGroup.lift D.label (p.crossingWord D.normal) := (rfl)

/-- Constant paths have identity product. -/
@[simp]
theorem pathProduct_nil : D.pathProduct (Quiver.Path.nil : AdmissiblePLPath x x) = 1 := by
  simp [pathProduct]

/-- The first path acts first, so its product occurs on the right. -/
@[simp]
theorem pathProduct_comp (p : AdmissiblePLPath x y) (q : AdmissiblePLPath y z) :
    D.pathProduct (p.comp q) = D.pathProduct q * D.pathProduct p := by
  simp [pathProduct]

/-- Appending a segment places its product on the left. -/
@[simp]
theorem pathProduct_cons (p : AdmissiblePLPath x y) (e : y ⟶ z) :
    D.pathProduct (p.cons e) = D.pathProduct e.toPath * D.pathProduct p := by
  simp [pathProduct, Quiver.Hom.toPath]

/-- Reversing an admissible path inverts its product. -/
@[simp]
theorem pathProduct_reverse (p : AdmissiblePLPath x y) :
    D.pathProduct p.reverse = (D.pathProduct p)⁻¹ := by
  simp [pathProduct, p.crossingWord_reverse D.normal D.ker_normal]

/-- A segment product is the reverse time-ordered product of its signed wall labels. -/
theorem pathProduct_toPath (e : x ⟶ y) :
    D.pathProduct e.toPath = ((C.orderedCrossings e).reverse.map fun a =>
      if 0 < D.normal a.1 (y.val - x.val) then (D.label a.1)⁻¹ else D.label a.1).prod := by
  simp only [pathProduct, Quiver.Hom.toPath, Quiver.Path.crossingWord_cons,
    Quiver.Path.crossingWord_nil, mul_one, C.segmentCrossingWord_def, map_list_prod,
    List.map_map, Function.comp_def, C.crossingLetter_def]
  congr 1
  apply List.map_congr_left
  intro a _
  split_ifs <;> simp

/-- Change wall labels by a group homomorphism, preserving the coorientations. -/
def relabel (f : G →* H) : FiniteWallDiagram C H where
  normal := D.normal
  ker_normal := D.ker_normal
  label P := f (D.label P)

@[simp]
theorem relabel_normal (f : G →* H) : (D.relabel f).normal = D.normal := (rfl)

@[simp]
theorem relabel_label (f : G →* H) (P : C.walls) :
    (D.relabel f).label P = f (D.label P) := (rfl)

@[simp]
theorem relabel_id : D.relabel (MonoidHom.id G) = D := by ext <;> rfl

@[simp]
theorem relabel_comp (f : G →* H) (g : H →* K) :
    (D.relabel f).relabel g = D.relabel (g.comp f) := by ext <;> rfl

/-- Relabelling carries a path product to its homomorphic image. -/
@[simp]
theorem pathProduct_relabel (f : G →* H) (p : AdmissiblePLPath x y) :
    (D.relabel f).pathProduct p = f (D.pathProduct p) := by
  exact (FreeGroup.lift_unique (f.comp (FreeGroup.lift D.label))
    (fun P => by simp) (x := p.crossingWord D.normal)).symm

omit [Group G] in
/-- Positively rescale the chosen representatives of the coorientations. -/
def rescale (r : C.walls → ℝ) (hr : ∀ P, 0 < r P) : FiniteWallDiagram C G where
  normal P := r P • D.normal P
  ker_normal P := by
    rw [LinearMap.ker_smul _ _ (ne_of_gt (hr P)), D.ker_normal P]
  label := D.label

omit [Group G] in
@[simp]
theorem rescale_normal (r : C.walls → ℝ) (hr : ∀ P, 0 < r P) (P : C.walls) :
    (D.rescale r hr).normal P = r P • D.normal P := (rfl)

omit [Group G] in
@[simp]
theorem rescale_label (r : C.walls → ℝ) (hr : ∀ P, 0 < r P) :
    (D.rescale r hr).label = D.label := (rfl)

/-- Positive rescaling of each normal preserves every path product. -/
@[simp]
theorem pathProduct_rescale (r : C.walls → ℝ) (hr : ∀ P, 0 < r P)
    (p : AdmissiblePLPath x y) : (D.rescale r hr).pathProduct p = D.pathProduct p := by
  simp only [pathProduct, rescale, p.crossingWord_smul D.normal r hr]

/-- Reverse the coorientation of one wall and invert its label. -/
def flip (P : C.walls) : FiniteWallDiagram C G := by
  classical
  exact
    { normal Q := if Q = P then -D.normal Q else D.normal Q
      ker_normal Q := by
        split_ifs <;> simp [D.ker_normal Q]
      label Q := if Q = P then (D.label Q)⁻¹ else D.label Q }

@[simp]
theorem flip_normal (P Q : C.walls) :
    (D.flip P).normal Q = if Q = P then -D.normal Q else D.normal Q := (rfl)

@[simp]
theorem flip_label (P Q : C.walls) :
    (D.flip P).label Q = if Q = P then (D.label Q)⁻¹ else D.label Q := (rfl)

/-- Reversing one coorientation twice restores the labelled diagram. -/
@[simp]
theorem flip_flip (P : C.walls) : (D.flip P).flip P = D := by
  ext Q <;> by_cases hQ : Q = P <;> simp [hQ]

/-- Reversing a coorientation while inverting its label preserves path products. -/
@[simp]
theorem pathProduct_flip (P : C.walls) (p : AdmissiblePLPath x y) :
    (D.flip P).pathProduct p = D.pathProduct p := by
  have he {u v : WallComplement (fun Q : C.walls => (Q : Set V))} (e : u ⟶ v) :
      (D.flip P).pathProduct e.toPath = D.pathProduct e.toPath := by
    rw [pathProduct_toPath, pathProduct_toPath]
    congr 1
    apply List.map_congr_left
    intro a ha
    have hn := C.normal_velocity_ne_zero (D.normal a.1) e (List.mem_reverse.mp ha)
      (D.ker_normal a.1)
    by_cases hP : a.1 = P
    · simp only [flip_normal, flip_label, ite_eq_left hP, LinearMap.neg_apply, neg_pos, inv_inv]
      split_ifs <;> first | rfl | exact (hn (by linarith)).elim
    · simp [flip_normal, flip_label, hP]
  induction p with
  | nil => simp
  | cons p e ih => simp only [pathProduct_cons, he, ih]

/-- A diagram is consistent if its path products depend only on the endpoints. -/
def Consistent : Prop :=
  ∀ ⦃x y : WallComplement (fun P : C.walls => (P : Set V))⦄
    (p q : AdmissiblePLPath x y), D.pathProduct p = D.pathProduct q

/-- In a consistent diagram, any two admissible paths with the same endpoints
have the same product. -/
theorem Consistent.pathProduct_eq {D : FiniteWallDiagram C G} (hD : D.Consistent)
    (p q : AdmissiblePLPath x y) : D.pathProduct p = D.pathProduct q := hD p q

/-- Consistency is equivalent to triviality of every admissible loop product. -/
theorem consistent_iff_loop_pathProduct_eq_one :
    D.Consistent ↔ ∀ (x : WallComplement (fun P : C.walls => (P : Set V)))
      (p : AdmissiblePLPath x x), D.pathProduct p = 1 := by
  constructor
  · intro hD x p
    simpa only [pathProduct_nil] using hD p Quiver.Path.nil
  · intro hD x y p q
    have h := hD x (p.comp q.reverse)
    have he : D.pathProduct q = D.pathProduct p := by
      simpa only [pathProduct_comp, pathProduct_reverse, inv_mul_eq_one] using h
    exact he.symm

/-- Homomorphic images of consistent diagrams remain consistent. -/
theorem Consistent.relabel {D : FiniteWallDiagram C G} (hD : D.Consistent) (f : G →* H) :
    (D.relabel f).Consistent := by
  intro x y p q
  simpa only [pathProduct_relabel] using congrArg f (hD p q)

/-- Injective relabelling also reflects consistency. -/
theorem consistent_relabel_iff (f : G →* H) (hf : Function.Injective f) :
    (D.relabel f).Consistent ↔ D.Consistent := by
  constructor
  · intro hD x y p q
    apply hf
    simpa only [← pathProduct_relabel] using hD p q
  · exact fun hD => hD.relabel f

end FiniteWallDiagram
end Mei
