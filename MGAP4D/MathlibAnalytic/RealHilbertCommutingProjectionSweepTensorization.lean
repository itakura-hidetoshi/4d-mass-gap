import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenEightColorHeatBathProjectionSweepL2
import Mathlib.Tactic

/-!
# Tensorization for finite commuting Hilbert projections

This file abstracts the beta-zero coordinate tensorization mechanism from any
particular Wilson system.

For a finite family of pairwise commuting self-adjoint idempotent continuous
linear endomorphisms of a real Hilbert space, an ordered sweep satisfies

  norm(x - sweep x)^2 <= sum_c norm(x - P_c x)^2.

The proof is finite and elementary. It uses only orthogonal-projection
Pythagoras, pairwise commutation, and norm contraction of each projection.

This result is intended for the beta-zero ground-state six-spatial block
family and for any later commuting block decomposition. No probabilistic,
Dobrushin, spectral-gap, or continuum statement is asserted here.
-/

namespace MGAP4D.MathlibAnalytic

open scoped BigOperators InnerProductSpace InnerProduct

noncomputable section

/-- A self-adjoint idempotent continuous linear map is norm-contracting. -/
theorem realHilbertProjection_norm_le
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (P : E →L[ℝ] E)
    (hIdem : P.comp P = P)
    (hSymm : ∀ x y : E, inner ℝ (P x) y = inner ℝ x (P y))
    (x : E) :
    ‖P x‖ ≤ ‖x‖ := by
  have hres :=
    realHilbertProjection_residual_norm_sq P hIdem hSymm x
  have hsq : ‖P x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    nlinarith [sq_nonneg ‖x - P x‖]
  exact
    (sq_le_sq₀ (norm_nonneg (P x)) (norm_nonneg x)).mp hsq

/-- The defect of an orthogonal projection is orthogonal to every vector fixed
by that projection. -/
theorem realHilbertProjection_defect_inner_eq_zero_of_fixed
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (P : E →L[ℝ] E)
    (hSymm : ∀ x y : E, inner ℝ (P x) y = inner ℝ x (P y))
    (f g : E)
    (hFixed : P g = g) :
    inner ℝ (f - P f) g = 0 := by
  rw [inner_sub_left, hSymm, hFixed, sub_self]

/-- One member of a pairwise commuting family commutes through every ordered
finite sweep of that family. -/
theorem realHilbertProjectionSweep_commute
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (P : C → E →L[ℝ] E)
    (hComm : ∀ (c d : C) (x : E), P c (P d x) = P d (P c x))
    (c : C)
    (cs : List C)
    (x : E) :
    P c (realHilbertProjectionSweep P cs x) =
      realHilbertProjectionSweep P cs (P c x) := by
  induction cs generalizing x with
  | nil =>
      simp [realHilbertProjectionSweep]
  | cons d ds ih =>
      simp only [realHilbertProjectionSweep, ContinuousLinearMap.comp_apply]
      calc
        P c (realHilbertProjectionSweep P ds (P d x)) =
            realHilbertProjectionSweep P ds (P c (P d x)) :=
          ih (P d x)
        _ = realHilbertProjectionSweep P ds (P d (P c x)) := by
          rw [hComm c d x]

/-- After first projecting in c, the remaining commuting-sweep defect is fixed
by P c. -/
theorem realHilbertProjectionSweep_tailDefect_fixed
    {E C : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (P : C → E →L[ℝ] E)
    (hIdem : ∀ c : C, (P c).comp (P c) = P c)
    (hComm : ∀ (c d : C) (x : E), P c (P d x) = P d (P c x))
    (c : C)
    (cs : List C)
    (x : E) :
    P c
        (P c x -
          realHilbertProjectionSweep P cs (P c x)) =
      P c x -
        realHilbertProjectionSweep P cs (P c x) := by
  have hcc : P c (P c x) = P c x := by
    have h := congrArg (fun Q : E →L[ℝ] E => Q x) (hIdem c)
    simpa using h
  rw [map_sub, hcc, realHilbertProjectionSweep_commute P hComm c cs (P c x),
    hcc]

/-- One commuting orthogonal-projection sweep step has an exact Pythagorean
decomposition of its total defect. -/
theorem realHilbertProjectionSweep_cons_defect_norm_sq_eq
    {E C : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (P : C → E →L[ℝ] E)
    (hIdem : ∀ c : C, (P c).comp (P c) = P c)
    (hSymm : ∀ (c : C) (x y : E),
      inner ℝ (P c x) y = inner ℝ x (P c y))
    (hComm : ∀ (c d : C) (x : E), P c (P d x) = P d (P c x))
    (c : C)
    (cs : List C)
    (x : E) :
    ‖x - realHilbertProjectionSweep P (c :: cs) x‖ ^ 2 =
      ‖x - P c x‖ ^ 2 +
        ‖P c x - realHilbertProjectionSweep P cs (P c x)‖ ^ 2 := by
  simp only [realHilbertProjectionSweep, ContinuousLinearMap.comp_apply]
  have hSplit :
      x - realHilbertProjectionSweep P cs (P c x) =
        (x - P c x) +
          (P c x - realHilbertProjectionSweep P cs (P c x)) := by
    abel
  have hFixed :=
    realHilbertProjectionSweep_tailDefect_fixed
      P hIdem hComm c cs x
  have hOrth :
      inner ℝ
          (x - P c x)
          (P c x - realHilbertProjectionSweep P cs (P c x)) = 0 :=
    realHilbertProjection_defect_inner_eq_zero_of_fixed
      (P c) (hSymm c) x
      (P c x - realHilbertProjectionSweep P cs (P c x))
      hFixed
  rw [hSplit, norm_add_sq_real, hOrth]
  ring

/-- Pairwise commutation lets a projected coordinate defect be written as the
projection of the original coordinate defect, hence it cannot increase. -/
theorem realHilbertProjection_projectedDefect_norm_le
    {E C : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (P : C → E →L[ℝ] E)
    (hIdem : ∀ c : C, (P c).comp (P c) = P c)
    (hSymm : ∀ (c : C) (x y : E),
      inner ℝ (P c x) y = inner ℝ x (P c y))
    (hComm : ∀ (c d : C) (x : E), P c (P d x) = P d (P c x))
    (c d : C)
    (x : E) :
    ‖P c x - P d (P c x)‖ ≤
      ‖x - P d x‖ := by
  calc
    ‖P c x - P d (P c x)‖ =
        ‖P c (x - P d x)‖ := by
      rw [map_sub, hComm c d x]
    _ ≤ ‖x - P d x‖ :=
      realHilbertProjection_norm_le
        (P c) (hIdem c) (hSymm c) (x - P d x)

/-- Squared form of projected-defect contraction. -/
theorem realHilbertProjection_projectedDefect_norm_sq_le
    {E C : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (P : C → E →L[ℝ] E)
    (hIdem : ∀ c : C, (P c).comp (P c) = P c)
    (hSymm : ∀ (c : C) (x y : E),
      inner ℝ (P c x) y = inner ℝ x (P c y))
    (hComm : ∀ (c d : C) (x : E), P c (P d x) = P d (P c x))
    (c d : C)
    (x : E) :
    ‖P c x - P d (P c x)‖ ^ 2 ≤
      ‖x - P d x‖ ^ 2 := by
  have h :=
    realHilbertProjection_projectedDefect_norm_le
      P hIdem hSymm hComm c d x
  nlinarith [
    norm_nonneg (P c x - P d (P c x)),
    norm_nonneg (x - P d x)]

/-- The sum of all remaining projection defects cannot increase after applying
one member of a pairwise commuting orthogonal-projection family. -/
theorem realHilbertProjectionSweep_projectedDefectSum_le
    {E C : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (P : C → E →L[ℝ] E)
    (hIdem : ∀ c : C, (P c).comp (P c) = P c)
    (hSymm : ∀ (c : C) (x y : E),
      inner ℝ (P c x) y = inner ℝ x (P c y))
    (hComm : ∀ (c d : C) (x : E), P c (P d x) = P d (P c x))
    (c : C)
    (cs : List C)
    (x : E) :
    (cs.map fun d => ‖P c x - P d (P c x)‖ ^ 2).sum ≤
      (cs.map fun d => ‖x - P d x‖ ^ 2).sum := by
  induction cs with
  | nil =>
      simp
  | cons d ds ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add
        (realHilbertProjection_projectedDefect_norm_sq_le
          P hIdem hSymm hComm c d x)
        ih

/-- Finite tensorization for an ordered list of pairwise commuting
self-adjoint idempotents. -/
theorem realHilbertProjectionSweep_tensorization
    {E C : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (P : C → E →L[ℝ] E)
    (hIdem : ∀ c : C, (P c).comp (P c) = P c)
    (hSymm : ∀ (c : C) (x y : E),
      inner ℝ (P c x) y = inner ℝ x (P c y))
    (hComm : ∀ (c d : C) (x : E), P c (P d x) = P d (P c x))
    (cs : List C)
    (x : E) :
    ‖x - realHilbertProjectionSweep P cs x‖ ^ 2 ≤
      (cs.map fun c => ‖x - P c x‖ ^ 2).sum := by
  induction cs generalizing x with
  | nil =>
      simp [realHilbertProjectionSweep]
  | cons c ds ih =>
      rw [realHilbertProjectionSweep_cons_defect_norm_sq_eq
        P hIdem hSymm hComm c ds x]
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add_right
        ((ih (P c x)).trans
          (realHilbertProjectionSweep_projectedDefectSum_le
            P hIdem hSymm hComm c ds x))
        _

/-- Fintype form: sweeping every member exactly once gives a defect bounded by
the sum of the original projection defects. -/
theorem realHilbertProjectionFullSweep_tensorization
    {E C : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [Fintype C]
    [DecidableEq C]
    (P : C → E →L[ℝ] E)
    (hIdem : ∀ c : C, (P c).comp (P c) = P c)
    (hSymm : ∀ (c : C) (x y : E),
      inner ℝ (P c x) y = inner ℝ x (P c y))
    (hComm : ∀ (c d : C) (x : E), P c (P d x) = P d (P c x))
    (x : E) :
    ‖x -
        realHilbertProjectionSweep P
          ((Finset.univ : Finset C).toList) x‖ ^ 2 ≤
      ∑ c : C, ‖x - P c x‖ ^ 2 := by
  simpa using
    realHilbertProjectionSweep_tensorization
      P hIdem hSymm hComm
      ((Finset.univ : Finset C).toList) x

end

end MGAP4D.MathlibAnalytic
