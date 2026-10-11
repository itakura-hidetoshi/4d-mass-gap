import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFiniteVolumeLinkMassLowerBound
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonMarginalCondExpComparison
import Mathlib.Tactic

/-!
# P4-Q2-CQ: finite tensorization for commuting real-Hilbert one-link projections

CP proves the original positive-beta Wilson one-link fiber mass floor.
Finite product Haar tensorization requires the Hilbert algebra of pairwise
commuting orthogonal averaging operators, which is established here.

For any ordered list of commuting, symmetric, idempotent, contractive
real-Hilbert projections P_i:

  ‖x - sweep(P, list) x‖² ≤ sum over list i of ‖x - P_i x‖².

This gives exact Fintype tensorization and a specialization to the TRUE
spatial pair-Haar L² carrier. Remaining independent pair-Haar obligations
are: construct actual single-coordinate Haar averaging projections,
prove their pairwise commutation, and identify the all-coordinate sweep
with constant expectation. They are NOT silently inferred for interacting
positive-beta Wilson conditional laws.

No fake Wilson law, reverse physical Poincare, uniform spectral gap,
or continuum four-dimensional Yang--Mills mass gap is claimed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators InnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 850000

noncomputable def p4Q2CQ_projectionSweep
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : ι → E →L[ℝ] E) : List ι → (E →L[ℝ] E)
  | [] => ContinuousLinearMap.id ℝ E
  | i :: rest => (p4Q2CQ_projectionSweep P rest).comp (P i)

@[simp] theorem p4Q2CQ_projectionSweep_nil
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : ι → E →L[ℝ] E) (x : E) :
    p4Q2CQ_projectionSweep P [] x = x := rfl

@[simp] theorem p4Q2CQ_projectionSweep_cons
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : ι → E →L[ℝ] E) (i : ι) (rest : List ι) (x : E) :
    p4Q2CQ_projectionSweep P (i :: rest) x =
      p4Q2CQ_projectionSweep P rest (P i x) := rfl

section GeneralRealHilbert

variable {E ι : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (P : ι → E →L[ℝ] E)
  (hId : ∀ i x, P i (P i x) = P i x)
  (hSymm : ∀ i x y, inner ℝ (P i x) y = inner ℝ x (P i y))
  (hComm : ∀ i j x, P i (P j x) = P j (P i x))
  (hNorm : ∀ i x, ‖P i x‖ ≤ ‖x‖)

include hId hSymm hComm hNorm

omit hId hSymm hNorm in
/-- A coordinate projection commutes with an entire ordered sweep. -/
theorem p4Q2CQ_projection_commute_sweep
    (i : ι) (rest : List ι) (x : E) :
    P i (p4Q2CQ_projectionSweep P rest x) =
      p4Q2CQ_projectionSweep P rest (P i x) := by
  induction rest generalizing x with
  | nil => rfl
  | cons j tail ih =>
      calc
        P i (p4Q2CQ_projectionSweep P (j :: tail) x) =
            P i (p4Q2CQ_projectionSweep P tail (P j x)) := rfl
        _ = p4Q2CQ_projectionSweep P tail (P i (P j x)) := ih (P j x)
        _ = p4Q2CQ_projectionSweep P tail (P j (P i x)) := by
          rw [hComm i j x]
        _ = p4Q2CQ_projectionSweep P (j :: tail) (P i x) := rfl

omit hSymm hNorm in
/-- The defect after the first coordinate is fixed by that projection. -/
theorem p4Q2CQ_sweep_tail_defect_fixed
    (i : ι) (rest : List ι) (x : E) :
    P i (P i x - p4Q2CQ_projectionSweep P rest (P i x)) =
      P i x - p4Q2CQ_projectionSweep P rest (P i x) := by
  rw [map_sub, hId i x,
    p4Q2CQ_projection_commute_sweep P hComm
      i rest (P i x), hId i x]

omit hNorm in
/-- Exact Pythagoras for the first projection and the rest of the sweep. -/
theorem p4Q2CQ_sweep_cons_defect_norm_sq
    (i : ι) (rest : List ι) (x : E) :
    ‖x - p4Q2CQ_projectionSweep P (i :: rest) x‖ ^ 2 =
      ‖x - P i x‖ ^ 2 +
        ‖P i x - p4Q2CQ_projectionSweep P rest (P i x)‖ ^ 2 := by
  rw [p4Q2CQ_projectionSweep_cons]
  have hsplit :
      x - p4Q2CQ_projectionSweep P rest (P i x) =
        (x - P i x) +
          (P i x - p4Q2CQ_projectionSweep P rest (P i x)) := by
    abel
  have hfixed :=
    p4Q2CQ_sweep_tail_defect_fixed P hId hComm i rest x
  have horth :
      inner ℝ (x - P i x)
        (P i x - p4Q2CQ_projectionSweep P rest (P i x)) = 0 := by
    rw [inner_sub_left]
    have hS :
        inner ℝ (P i x)
            (P i x - p4Q2CQ_projectionSweep P rest (P i x)) =
          inner ℝ x
            (P i (P i x - p4Q2CQ_projectionSweep P rest (P i x))) :=
      hSymm i x (P i x - p4Q2CQ_projectionSweep P rest (P i x))
    rw [hS, hfixed, sub_self]
  rw [hsplit, norm_add_sq_real, horth]
  ring

omit hId hSymm in
/-- Projected coordinate defects contract, solely by commutation. -/
theorem p4Q2CQ_projected_coordinate_defect_norm_le
    (i j : ι) (x : E) :
    ‖P i x - P j (P i x)‖ ≤ ‖x - P j x‖ := by
  calc
    ‖P i x - P j (P i x)‖ =
        ‖P i (x - P j x)‖ := by
      rw [map_sub, hComm i j x]
    _ ≤ ‖x - P j x‖ := hNorm i (x - P j x)

omit hId hSymm in
theorem p4Q2CQ_projected_coordinate_defect_sq_le
    (i j : ι) (x : E) :
    ‖P i x - P j (P i x)‖ ^ 2 ≤ ‖x - P j x‖ ^ 2 := by
  have h :=
    p4Q2CQ_projected_coordinate_defect_norm_le
      P hComm hNorm i j x
  nlinarith [norm_nonneg (P i x - P j (P i x)),
    norm_nonneg (x - P j x)]

omit hId hSymm in
theorem p4Q2CQ_projected_coordinate_defect_list_sum_le
    (i : ι) (rest : List ι) (x : E) :
    (rest.map fun j => ‖P i x - P j (P i x)‖ ^ 2).sum ≤
      (rest.map fun j => ‖x - P j x‖ ^ 2).sum := by
  induction rest with
  | nil => simp
  | cons j tail ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add
        (p4Q2CQ_projected_coordinate_defect_sq_le
          P hComm hNorm i j x) ih

/-- General finite tensorization (algebraic Efron--Stein Hilbert lemma). -/
theorem p4Q2CQ_projectionSweep_tensorization
    (rest : List ι) (x : E) :
    ‖x - p4Q2CQ_projectionSweep P rest x‖ ^ 2 ≤
      (rest.map fun i => ‖x - P i x‖ ^ 2).sum := by
  induction rest generalizing x with
  | nil => simp
  | cons i tail ih =>
      rw [p4Q2CQ_sweep_cons_defect_norm_sq
        P hId hSymm hComm i tail x]
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add_right
        ((ih (P i x)).trans
          (p4Q2CQ_projected_coordinate_defect_list_sum_le
            P hComm hNorm i tail x)) _

/-- Canonical Fintype coordinate sweep, with no duplicated coordinates. -/
theorem p4Q2CQ_finiteProjectionTensorization
    [Fintype ι] (x : E) :
    ‖x -
        p4Q2CQ_projectionSweep P (Finset.univ.toList : List ι) x‖ ^ 2 ≤
      ∑ i : ι, ‖x - P i x‖ ^ 2 := by
  have h :=
    p4Q2CQ_projectionSweep_tensorization
      P hId hSymm hComm hNorm (Finset.univ.toList : List ι) x
  calc
    ‖x - p4Q2CQ_projectionSweep P (Finset.univ.toList : List ι) x‖ ^ 2 ≤
        ((Finset.univ.toList : List ι).map fun i => ‖x - P i x‖ ^ 2).sum := h
    _ = ∑ i : ι, ‖x - P i x‖ ^ 2 := by
      exact
        (Finset.sum_toList
          (s := (Finset.univ : Finset ι))
          (f := fun i : ι => ‖x - P i x‖ ^ 2)).symm

end GeneralRealHilbert

section PhysicalPairHaar

local instance p4Q2CQ_actualJointIndexFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H) :=
  Fintype.ofFinite _

variable (H N : ℕ)

local notation "muPair" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
local notation "I" =>
  PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H
local notation "JH" => Lp ℝ 2 muPair

/-- The exact original pair-Haar L² carrier, with explicit orthogonal
coordinate-projection laws as premises. Identifying those laws with
concrete Haar integrations is the subsequent physical coordinate bridge. -/
theorem p4Q2CQ_actualPairHaar_finiteProjectionTensorization
    (P : I → JH →L[ℝ] JH)
    (hId : ∀ i x, P i (P i x) = P i x)
    (hSymm : ∀ i x y, inner ℝ (P i x) y = inner ℝ x (P i y))
    (hComm : ∀ i j x, P i (P j x) = P j (P i x))
    (hNorm : ∀ i x, ‖P i x‖ ≤ ‖x‖)
    (x : JH) :
    ‖x - p4Q2CQ_projectionSweep P (Finset.univ.toList : List I) x‖ ^ 2 ≤
      ∑ i : I, ‖x - P i x‖ ^ 2 := by
  classical
  letI : Fintype I := Fintype.ofFinite _
  exact p4Q2CQ_finiteProjectionTensorization P hId hSymm hComm hNorm x

end PhysicalPairHaar
end

end MathlibAnalytic
end MGAP4D
