import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenEightColorHeatBathProjectionSweepL2
import Mathlib.Tactic

/-!
# Link-indexed stage profile for an ordered Hilbert projection sweep

The recursive path-loss functional already records the squared defect at each
successive sweep stage.  This file turns that stagewise information into a
profile indexed by the projection label itself.

For an ordered list `cs`, the squared profile at label `d` is the sum of the
squared defects of all stages carrying label `d`.  Hence, without any
commutativity or idempotence assumption,

  sum_d stageProfile(d)^2 = sweepPathLoss.

The square-root amplitude form is the receiver-ready object for later Schur
and one-sided profile estimates.
-/

namespace MGAP4D.MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Squared sweep-stage residual mass attributed to one projection label.
Repeated labels, if present, simply accumulate their successive stage losses. -/
def realHilbertProjectionSweepStageResidualSqProfile
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [DecidableEq C]
    (P : C → E →L[ℝ] E) :
    List C → E → C → ℝ
  | [], _, _ => 0
  | c :: cs, x, d =>
      (if d = c then ‖x - P c x‖ ^ 2 else 0) +
        realHilbertProjectionSweepStageResidualSqProfile P cs (P c x) d

/-- Every label-attributed squared stage profile is nonnegative. -/
theorem realHilbertProjectionSweepStageResidualSqProfile_nonneg
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [DecidableEq C]
    (P : C → E →L[ℝ] E)
    (cs : List C)
    (x : E)
    (d : C) :
    0 ≤ realHilbertProjectionSweepStageResidualSqProfile P cs x d := by
  induction cs generalizing x with
  | nil =>
      simp [realHilbertProjectionSweepStageResidualSqProfile]
  | cons c cs ih =>
      simp only [realHilbertProjectionSweepStageResidualSqProfile]
      exact add_nonneg
        (by
          split_ifs
          · exact sq_nonneg _
          · exact le_rfl)
        (ih (P c x))

/-- Summing the squared stage profile over all labels exactly recovers the
recursive sweep path loss. -/
theorem realHilbertProjectionSweepStageResidualSqProfile_sum_eq_pathLoss
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [Fintype C]
    [DecidableEq C]
    (P : C → E →L[ℝ] E)
    (cs : List C)
    (x : E) :
    (∑ d : C, realHilbertProjectionSweepStageResidualSqProfile P cs x d) =
      realHilbertProjectionSweepPathLoss P cs x := by
  induction cs generalizing x with
  | nil =>
      simp [realHilbertProjectionSweepStageResidualSqProfile,
        realHilbertProjectionSweepPathLoss]
  | cons c cs ih =>
      simp only [realHilbertProjectionSweepStageResidualSqProfile,
        realHilbertProjectionSweepPathLoss, Finset.sum_add_distrib]
      rw [ih]
      simp

/-- Nonnegative amplitude associated with the label-attributed squared stage
profile. -/
noncomputable def realHilbertProjectionSweepStageResidualAmplitude
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [DecidableEq C]
    (P : C → E →L[ℝ] E)
    (cs : List C)
    (x : E)
    (d : C) : ℝ :=
  Real.sqrt (realHilbertProjectionSweepStageResidualSqProfile P cs x d)

/-- The stage residual amplitude is nonnegative. -/
theorem realHilbertProjectionSweepStageResidualAmplitude_nonneg
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [DecidableEq C]
    (P : C → E →L[ℝ] E)
    (cs : List C)
    (x : E)
    (d : C) :
    0 ≤ realHilbertProjectionSweepStageResidualAmplitude P cs x d := by
  exact Real.sqrt_nonneg _

/-- Squaring the stage residual amplitude recovers its attributed squared
stage mass. -/
theorem realHilbertProjectionSweepStageResidualAmplitude_sq
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [DecidableEq C]
    (P : C → E →L[ℝ] E)
    (cs : List C)
    (x : E)
    (d : C) :
    realHilbertProjectionSweepStageResidualAmplitude P cs x d ^ 2 =
      realHilbertProjectionSweepStageResidualSqProfile P cs x d := by
  unfold realHilbertProjectionSweepStageResidualAmplitude
  exact Real.sq_sqrt
    (realHilbertProjectionSweepStageResidualSqProfile_nonneg P cs x d)

/-- Receiver-ready exact energy identity: the sum of squared local amplitudes
is precisely the ordered sweep path loss. -/
theorem realHilbertProjectionSweepStageResidualAmplitude_sq_sum_eq_pathLoss
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [Fintype C]
    [DecidableEq C]
    (P : C → E →L[ℝ] E)
    (cs : List C)
    (x : E) :
    (∑ d : C, realHilbertProjectionSweepStageResidualAmplitude P cs x d ^ 2) =
      realHilbertProjectionSweepPathLoss P cs x := by
  calc
    (∑ d : C, realHilbertProjectionSweepStageResidualAmplitude P cs x d ^ 2) =
        ∑ d : C, realHilbertProjectionSweepStageResidualSqProfile P cs x d := by
      apply Finset.sum_congr rfl
      intro d _hd
      exact realHilbertProjectionSweepStageResidualAmplitude_sq P cs x d
    _ = realHilbertProjectionSweepPathLoss P cs x :=
      realHilbertProjectionSweepStageResidualSqProfile_sum_eq_pathLoss P cs x

end

end MGAP4D.MathlibAnalytic
