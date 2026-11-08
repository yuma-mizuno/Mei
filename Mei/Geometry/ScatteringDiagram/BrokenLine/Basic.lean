/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mei.Data.Fin.HEq
public import Mei.LinearAlgebra.GradedCorrespondence.Basic
public import Mathlib.Algebra.Category.ModuleCat.Semi
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Topology.OpenPartialHomeomorph.Defs

/-!
# Decorated broken lines in a chart and face presentation

A `BrokenLineData` records what a broken line needs from a base: chamber charts into a
real normed space, their coefficient semimodules with homogeneous gradings, a velocity
for each degree, and, for every face between two chambers, a `GradedCorrespondence`
between the two chamber modules together with the active normals at its points and a
set of singular points.

A `BrokenLine` for such data is a proper continuous path `Iic 0 → B` with finitely
many strictly increasing crossing times. On each open segment it is affine in the
chart of the segment's chamber with velocity the negative of the momentum of the
segment's degree, and it misses all faces. Every crossing lies on a face, is transverse
to and preserves the velocity along every active normal, and sends the decoration of
the previous segment to the whole homogeneous component of its transfer across the
face's correspondence. All decorations are nonzero. The first segment is not
constrained here: an incoming datum is imposed as the `incoming` value of a fiber.

Crossing times are determined by the path (`mem_range_eventTime_iff`), and every
decoration is determined by the first one and the degrees along the line. The final
decoration at a fixed chamber and its finite sums over families (`weightedEvaluation`)
are the common evaluation of the affine, slab and focus-focus presentations of broken
lines.

The definition follows Gross–Hacking–Keel–Kontsevich, *Canonical bases for cluster
algebras*, Definitions 3.1–3.3 (arXiv:1411.1394v2), with the whole-component transfers
of Gross–Hacking–Siebert, *Theta functions on varieties with effective anti-canonical
class*, Definitions 3.1–3.3 (arXiv:1601.07081v4), and Mandel, *Scattering diagrams,
theta functions, and refined tropical curve counts*, Definition 2.10
(arXiv:1503.06183v5).
-/

public section

open Set

universe uS uD uM uF

namespace Mei

/-- The open time interval of segment `j` of a path with crossing times `T`: it lies
after all earlier crossings and before all later ones and the endpoint at time zero. -/
def segmentInterior {k : ℕ} (T : Fin k → ℝ) (j : Fin (k + 1)) : Set ℝ :=
  {t | t < 0 ∧ (∀ b : Fin k, b.castSucc < j → T b < t) ∧ ∀ b : Fin k, j ≤ b.castSucc → t < T b}

@[simp]
theorem mem_segmentInterior {k : ℕ} {T : Fin k → ℝ} {j : Fin (k + 1)} {t : ℝ} :
    t ∈ segmentInterior T j ↔
      t < 0 ∧ (∀ b : Fin k, b.castSucc < j → T b < t) ∧ ∀ b : Fin k, j ≤ b.castSucc → t < T b :=
  Iff.rfl

variable (R B V : Type*) [Semiring R] [TopologicalSpace B]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The chamber, face and coefficient data of a base in which broken lines live. A chamber
`u` has a chart and a region of the base, a homogeneously graded coefficient semimodule and a
momentum for each degree. A face from `u` to `v` has a support, active normals in the two
charts at each of its points, and a correspondence between the two chamber modules with
admissible degrees on each side. Distinct chambers may share a region, and distinct faces
may share a support. -/
structure BrokenLineData where
  /-- The chambers. -/
  State : Type uS
  /-- The homogeneous degrees of the coefficients of a chamber. -/
  Degree : State → Type uD
  /-- The coefficient semimodule of a chamber. -/
  coefficient : State → SemimoduleCat.{uM} R
  /-- The homogeneous pieces of a chamber's coefficients. -/
  grading : ∀ u, Degree u → Submodule R (coefficient u)
  /-- Equality of homogeneous degrees is decidable. -/
  decidableDegree : ∀ u, DecidableEq (Degree u)
  /-- The pieces `grading u p` decompose the coefficients of a chamber. -/
  decomposition : ∀ u, DirectSum.Decomposition (grading u)
  /-- The chart of a chamber into the model vector space. -/
  chart : State → OpenPartialHomeomorph B V
  /-- The part of the base where a chamber's coefficients are used. -/
  region : State → Set B
  /-- A region lies in the source of the chart of its chamber. -/
  region_subset_source : ∀ u, region u ⊆ (chart u).source
  /-- The momentum in chart coordinates of a homogeneous degree; a path moves with the
  negative of the momentum. -/
  momentum : ∀ u, Degree u → V
  /-- The faces from one chamber to another. -/
  Face : State → State → Type uF
  /-- The middle module of the correspondence of a face. -/
  faceCoefficient : ∀ {u v}, Face u v → SemimoduleCat.{uM} R
  /-- The support of a face in the base, which lies in both adjacent charts. -/
  support : ∀ {u v}, Face u v → Set B
  /-- A face lies in the chart of its source chamber. -/
  support_subset_source_left : ∀ {u v} (e : Face u v), support e ⊆ (chart u).source
  /-- A face lies in the chart of its target chamber. -/
  support_subset_source_right : ∀ {u v} (e : Face u v), support e ⊆ (chart v).source
  /-- The active normals at a point of a face, as pairs of functionals in the charts of
  the two adjacent chambers. -/
  normals : ∀ {u v}, Face u v → B → Set (Module.Dual ℝ V × Module.Dual ℝ V)
  /-- The admissible degrees on the left of a face. -/
  admissibleLeft : ∀ {u v}, Face u v → Set (Degree u)
  /-- The admissible degrees on the right of a face. -/
  admissibleRight : ∀ {u v}, Face u v → Set (Degree v)
  /-- The correspondence of a face between the modules of its adjacent chambers. -/
  span : ∀ {u v} (e : Face u v),
    GradedCorrespondence (B := faceCoefficient e) (grading u) (grading v)
      (admissibleLeft e) (admissibleRight e)
  /-- The points where paths are not allowed. -/
  singular : Set B

attribute [instance] BrokenLineData.decidableDegree BrokenLineData.decomposition

variable {R B V}

namespace BrokenLineData

/-- The union of the supports of all faces. -/
def faceSupport (D : BrokenLineData.{uS, uD, uM, uF} R B V) : Set B :=
  {x | ∃ (u v : D.State) (e : D.Face u v), x ∈ D.support e}

@[simp]
theorem mem_faceSupport {D : BrokenLineData.{uS, uD, uM, uF} R B V} {x : B} :
    x ∈ D.faceSupport ↔ ∃ (u v : D.State) (e : D.Face u v), x ∈ D.support e := Iff.rfl

theorem support_subset_faceSupport {D : BrokenLineData.{uS, uD, uM, uF} R B V} {u v : D.State}
    (e : D.Face u v) : D.support e ⊆ D.faceSupport :=
  fun _ hx => ⟨u, v, e, hx⟩

end BrokenLineData

/-- A decorated broken line for chart and face data `D`. Crossings are indexed forwards in
time, and segment `j` lies between crossings `j - 1` and `j`. All crossings are recorded,
including those at faces that fix the decoration. -/
structure BrokenLine (D : BrokenLineData.{uS, uD, uM, uF} R B V) where
  /-- The number of crossings. -/
  numEvents : ℕ
  /-- The crossing times, all before the endpoint at time zero. -/
  eventTime : Fin numEvents → ℝ
  /-- Crossings are strictly ordered in time. -/
  eventTime_strictMono : StrictMono eventTime
  /-- All crossings precede the endpoint. -/
  eventTime_neg : ∀ j, eventTime j < 0
  /-- The chamber of each segment. -/
  state : Fin (numEvents + 1) → D.State
  /-- The homogeneous degree of each segment. -/
  degree : ∀ j, D.Degree (state j)
  /-- The whole homogeneous decoration of each segment. -/
  decoration : ∀ j, D.coefficient (state j)
  /-- Each decoration is homogeneous of the degree of its segment. -/
  decoration_mem : ∀ j, decoration j ∈ D.grading (state j) (degree j)
  /-- Every decoration is nonzero. -/
  decoration_ne_zero : ∀ j, decoration j ≠ 0
  /-- The path, ending at time zero. -/
  path : Iic (0 : ℝ) → B
  /-- The path is continuous and proper, so its first segment leaves every compact set. -/
  proper : IsProperMap path
  /-- The endpoint is not on a face. -/
  path_zero_off_faces : path ⟨0, le_rfl⟩ ∉ D.faceSupport
  /-- The endpoint lies in the region of the last chamber. -/
  path_zero_mem_region : path ⟨0, le_rfl⟩ ∈ D.region (state (Fin.last numEvents))
  /-- The path avoids the singular set. -/
  avoids_singular : ∀ t, path t ∉ D.singular
  /-- The interior of a segment lies in the region of its chamber. -/
  interior_mem_region : ∀ j (t : Iic (0 : ℝ)), (t : ℝ) ∈ segmentInterior eventTime j →
    path t ∈ D.region (state j)
  /-- On the interior of a segment the path is affine in the chart of its chamber, with
  velocity the negative of the momentum of its degree. -/
  interior_affine : ∀ j (s t : Iic (0 : ℝ)), (s : ℝ) ∈ segmentInterior eventTime j →
    (t : ℝ) ∈ segmentInterior eventTime j →
    D.chart (state j) (path t) =
      D.chart (state j) (path s) - ((t : ℝ) - s) • D.momentum (state j) (degree j)
  /-- The interior of a segment misses all faces. -/
  interior_off_faces : ∀ j (t : Iic (0 : ℝ)), (t : ℝ) ∈ segmentInterior eventTime j →
    path t ∉ D.faceSupport
  /-- The face crossed at each event. -/
  face : ∀ j : Fin numEvents, D.Face (state j.castSucc) (state j.succ)
  /-- Each crossing lies on its face. -/
  event_mem_support : ∀ j, path ⟨eventTime j, (eventTime_neg j).le⟩ ∈ D.support (face j)
  /-- Every active normal at a crossing is transverse to the incoming segment. -/
  transverse : ∀ j n, n ∈ D.normals (face j) (path ⟨eventTime j, (eventTime_neg j).le⟩) →
    n.1 (D.momentum (state j.castSucc) (degree j.castSucc)) ≠ 0
  /-- A crossing preserves the velocity along every active normal. -/
  normal_velocity : ∀ j n,
    n ∈ D.normals (face j) (path ⟨eventTime j, (eventTime_neg j).le⟩) →
    n.1 (D.momentum (state j.castSucc) (degree j.castSucc)) =
      n.2 (D.momentum (state j.succ) (degree j.succ))
  /-- The degree before a crossing is admissible for the face. -/
  admissible : ∀ j, degree j.castSucc ∈ D.admissibleLeft (face j)
  /-- A crossing replaces the decoration by the entire component of the transfer. -/
  propagate : ∀ j, decoration j.succ =
    (D.span (face j)).transfer ⟨degree j.castSucc, admissible j⟩ (degree j.succ)
      ⟨decoration j.castSucc, decoration_mem j.castSucc⟩

namespace BrokenLine

variable {D : BrokenLineData.{uS, uD, uM, uF} R B V} (b : BrokenLine D)

/-- The endpoint of the path. -/
def endpoint : B := b.path ⟨0, le_rfl⟩

/-- The chamber of the last segment, which contains the endpoint. -/
def finalState : D.State := b.state (Fin.last b.numEvents)

theorem finalState_def : b.finalState = b.state (Fin.last b.numEvents) := (rfl)

/-- The decoration of the last segment. -/
def finalDecoration : D.coefficient b.finalState :=
  b.finalState_def ▸ b.decoration (Fin.last b.numEvents)

/-- The chamber, degree and decoration of the first segment, imposed on the fibers of
evaluation. -/
def incoming : Σ u : D.State, Σ _ : D.Degree u, D.coefficient u :=
  ⟨b.state 0, b.degree 0, b.decoration 0⟩

theorem endpoint_def : b.endpoint = b.path ⟨0, le_rfl⟩ := (rfl)

theorem finalDecoration_def : b.finalState_def ▸ b.finalDecoration =
    b.decoration (Fin.last b.numEvents) := by
  simp only [finalDecoration]

theorem incoming_def : b.incoming = ⟨b.state 0, b.degree 0, b.decoration 0⟩ := (rfl)

theorem endpoint_mem_region : b.endpoint ∈ D.region b.finalState := by
  rw [finalState_def]
  exact b.path_zero_mem_region

theorem endpoint_off_faces : b.endpoint ∉ D.faceSupport := b.path_zero_off_faces

theorem finalDecoration_ne_zero : b.finalDecoration ≠ 0 := b.decoration_ne_zero _

/-- The degree of the last segment. -/
def finalDegree : D.Degree b.finalState :=
  b.finalState_def ▸ b.degree (Fin.last b.numEvents)

theorem finalDegree_def : b.finalState_def ▸ b.finalDegree =
    b.degree (Fin.last b.numEvents) := by
  simp only [finalDegree]

theorem finalDecoration_mem : b.finalDecoration ∈ D.grading b.finalState b.finalDegree :=
  b.decoration_mem _

/-- The final decoration read in a chamber equal to the final one. -/
def decorationIn {u : D.State} (h : b.finalState = u) : D.coefficient u := h ▸ b.finalDecoration

@[simp]
theorem decorationIn_rfl : b.decorationIn rfl = b.finalDecoration := (rfl)

theorem decorationIn_ne_zero {u : D.State} (h : b.finalState = u) : b.decorationIn h ≠ 0 := by
  subst h
  exact b.finalDecoration_ne_zero

/-- The crossing times are exactly the times at which the path meets a face: the path
determines them. -/
theorem mem_range_eventTime_iff (t : Iic (0 : ℝ)) :
    (t : ℝ) ∈ range b.eventTime ↔ b.path t ∈ D.faceSupport := by
  constructor
  · rintro ⟨j, hj⟩
    have ht : t = ⟨b.eventTime j, (b.eventTime_neg j).le⟩ := Subtype.ext hj.symm
    rw [ht]
    exact D.support_subset_faceSupport _ (b.event_mem_support j)
  · intro hface
    by_contra hnot
    have hne : (t : ℝ) ≠ 0 := fun h => b.path_zero_off_faces (by
      have : t = ⟨0, le_rfl⟩ := Subtype.ext h
      rwa [this] at hface)
    have hlt : (t : ℝ) < 0 := lt_of_le_of_ne t.property hne
    classical
    by_cases hex : ∃ j, (t : ℝ) < b.eventTime j
    · have hj := Fin.find_spec (p := fun j => (t : ℝ) < b.eventTime j) hex
      refine b.interior_off_faces (Fin.find _ hex).castSucc t
        ⟨hlt, fun i hi => ?_, fun i hi => ?_⟩ hface
      · exact lt_of_le_of_ne (not_lt.mp (Fin.find_min hex (Fin.castSucc_lt_castSucc_iff.mp hi)))
          (fun h => hnot ⟨i, h⟩)
      · exact hj.trans_le (b.eventTime_strictMono.monotone (Fin.castSucc_le_castSucc_iff.mp hi))
    · refine b.interior_off_faces (Fin.last b.numEvents) t
        ⟨hlt, fun i _ => lt_of_le_of_ne (not_lt.mp fun h => hex ⟨i, h⟩)
          (fun h => hnot ⟨i, h⟩), fun i hi => ?_⟩
        hface
      exact absurd hi (not_le.mpr (Fin.castSucc_lt_last i))

/-- Without crossings the first and last segments coincide. -/
theorem finalState_eq_state_zero (hn : b.numEvents = 0) : b.finalState = b.state 0 :=
  congrArg b.state (Fin.ext (by simp [hn]))

/-- Without crossings the final decoration is the incoming decoration, read in the incoming
chamber. -/
theorem exists_decorationIn_eq_of_numEvents_eq_zero (hn : b.numEvents = 0) {u : D.State}
    {p : D.Degree u} {a : D.coefficient u} (hinc : b.incoming = ⟨u, p, a⟩) :
    ∃ h : b.finalState = u, b.decorationIn h = a := by
  have hl : Fin.last b.numEvents = 0 := Fin.ext (by simp [hn])
  have key : ∀ j : Fin (b.numEvents + 1), j = 0 → ∀ h : b.state j = b.state 0,
      h ▸ b.decoration j = b.decoration 0 := by
    rintro j rfl h
    rfl
  rw [b.incoming_def] at hinc
  obtain ⟨hu, hp⟩ := Sigma.mk.inj_iff.mp hinc
  subst hu
  simp only [Sigma.mk.injEq, heq_eq_eq] at hp
  exact ⟨b.finalState_eq_state_zero hn, (key _ hl _).trans hp.2⟩

/-- Without crossings the last segment moves with the momentum of the incoming degree. -/
theorem momentum_final_eq_of_numEvents_eq_zero (hn : b.numEvents = 0) {u : D.State}
    {p : D.Degree u} {a : D.coefficient u} (hinc : b.incoming = ⟨u, p, a⟩) :
    D.momentum b.finalState b.finalDegree = D.momentum u p := by
  have hl : Fin.last b.numEvents = 0 := Fin.ext (by simp [hn])
  have h0 : D.momentum b.finalState b.finalDegree = D.momentum (b.state 0) (b.degree 0) :=
    congrArg (fun j => D.momentum (b.state j) (b.degree j)) hl
  rw [h0]
  rw [b.incoming_def] at hinc
  obtain ⟨hu, hp⟩ := Sigma.mk.inj_iff.mp hinc
  subst hu
  simp only [Sigma.mk.injEq, heq_eq_eq] at hp
  rw [hp.1]

/-- The momentum of the final segment. -/
theorem momentum_final_def : D.momentum b.finalState b.finalDegree =
    D.momentum (b.state (Fin.last b.numEvents)) (b.degree (Fin.last b.numEvents)) := by
  have hs : b.state (Fin.last b.numEvents) = b.finalState := b.finalState_def.symm
  have hdp : (⟨b.state (Fin.last b.numEvents), b.degree (Fin.last b.numEvents)⟩ :
      Σ u, D.Degree u) = ⟨b.finalState, b.finalDegree⟩ := Sigma.eq hs b.finalDegree_def
  rw [congrArg (fun dp : Σ u, D.Degree u => D.momentum dp.1 dp.2) hdp]

/-- Broken lines with the same crossings, path, segment chambers, degrees and decorations are
equal. -/
@[ext]
protected theorem ext {b c : BrokenLine D} (hn : b.numEvents = c.numEvents)
    (hT : HEq b.eventTime c.eventTime) (hpath : b.path = c.path)
    (hstate : HEq b.state c.state)
    (hdegree : HEq b.degree c.degree) (hdecoration : HEq b.decoration c.decoration)
    (hface : HEq b.face c.face) : b = c := by
  cases b
  cases c
  simp only [BrokenLine.mk.injEq]
  exact ⟨hn, hT, hstate, hdegree, hdecoration, hpath, hface⟩

/-- Broken lines without crossings are determined by their path and incoming datum. -/
theorem ext_of_numEvents_eq_zero {b c : BrokenLine D} (hb : b.numEvents = 0)
    (hc : c.numEvents = 0) (hpath : b.path = c.path) (hinc : b.incoming = c.incoming) :
    b = c := by
  rw [b.incoming_def, c.incoming_def] at hinc
  have hstate : HEq b.state c.state :=
    Fin.zero_index_heq hb hc b.state c.state (Sigma.mk.inj hinc).1
  obtain ⟨hdegree, hdecoration⟩ :=
    Fin.zero_index_dep_heq (B := fun u p => D.coefficient u) (f := b.degree) (g := c.degree)
      (df := b.decoration) (dg := c.decoration) hb hc hstate (Sigma.mk.inj hinc).2
  have hn : b.numEvents = c.numEvents := hb.trans hc.symm
  have hbc : Fin b.numEvents = Fin c.numEvents := congrArg Fin hn
  refine BrokenLine.ext hn ?_ hpath hstate hdegree hdecoration ?_
  · apply Function.hfunext hbc
    intro j j' _
    have : j'.val < 0 := by simpa [hc] using j'.isLt
    omega
  · apply Function.hfunext hbc
    intro j j' _
    have : j'.val < 0 := by simpa [hc] using j'.isLt
    omega

/-- Evaluation of a finite family of broken lines in a chamber `u` that contains all their
endpoints: the sum of their final decorations. -/
noncomputable def weightedEvaluation {ι : Type*} [Finite ι] (family : ι → BrokenLine D)
    (u : D.State) (hu : ∀ j, (family j).finalState = u) : D.coefficient u :=
  let := Fintype.ofFinite ι
  ∑ j, (family j).decorationIn (hu j)

theorem weightedEvaluation_def {ι : Type*} [Finite ι] (family : ι → BrokenLine D)
    (u : D.State) (hu : ∀ j, (family j).finalState = u) :
    weightedEvaluation family u hu =
      let := Fintype.ofFinite ι
      ∑ j, (family j).decorationIn (hu j) := by
  unfold weightedEvaluation
  congr

/-- Reindexing a family does not change its evaluation. -/
theorem weightedEvaluation_comp_equiv {ι κ : Type*} [Finite ι] [Finite κ] (e : ι ≃ κ)
    (family : κ → BrokenLine D) (u : D.State) (hu : ∀ j, (family j).finalState = u) :
    weightedEvaluation (family ∘ e) u (fun j => hu (e j)) = weightedEvaluation family u hu := by
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite κ
  rw [weightedEvaluation_def, weightedEvaluation_def]
  exact Fintype.sum_equiv e _ _ fun _ => rfl

/-- The empty family evaluates to zero. -/
@[simp]
theorem weightedEvaluation_isEmpty {ι : Type*} [Finite ι] [IsEmpty ι] (family : ι → BrokenLine D)
    (u : D.State) (hu : ∀ j, (family j).finalState = u) : weightedEvaluation family u hu = 0 := by
  let := Fintype.ofFinite ι
  rw [weightedEvaluation_def]
  exact Finset.sum_of_isEmpty _

/-- Evaluation adds over a disjoint union of finite families. -/
@[simp]
theorem weightedEvaluation_sum {ι κ : Type*} [Finite ι] [Finite κ]
    (family₁ : ι → BrokenLine D) (family₂ : κ → BrokenLine D) (u : D.State)
    (hu : ∀ j, (Sum.elim family₁ family₂ j).finalState = u) :
    weightedEvaluation (Sum.elim family₁ family₂) u hu =
      weightedEvaluation family₁ u (fun j => hu (Sum.inl j)) +
        weightedEvaluation family₂ u (fun j => hu (Sum.inr j)) := by
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite κ
  let _ : Fintype (ι ⊕ κ) := inferInstance
  have hu₁ : ∀ j, (family₁ j).finalState = u := fun j => hu (Sum.inl j)
  have hu₂ : ∀ j, (family₂ j).finalState = u := fun j => hu (Sum.inr j)
  simp only [weightedEvaluation_def]
  rw [show Fintype.ofFinite (ι ⊕ κ) = (inferInstance : Fintype (ι ⊕ κ)) from
    Subsingleton.elim _ _]
  apply Fintype.sum_sum_type

/-- A single broken line evaluates to its final decoration. -/
@[simp]
theorem weightedEvaluation_unique {ι : Type*} [Unique ι] (family : ι → BrokenLine D)
    (u : D.State) (hu : ∀ j, (family j).finalState = u) :
    weightedEvaluation family u hu = (family default).decorationIn (hu default) := by
  let := Fintype.ofFinite ι
  rw [weightedEvaluation_def]
  exact Fintype.sum_unique _

end BrokenLine

end Mei
