import MGAP4D.MathlibAnalytic.RealHilbertProjectionSweepTargetResidualForcingBudgetTrajectory
import Mathlib.Tactic

/-!
# Exact trajectory sums for the existing residual-forcing budget

Concatenation retains the actual intermediate sweep vector. A duplicate-free
trajectory whose forcing equals a fixed source cost has exactly that finite
source sum. Neither the original telescope nor its budget is redefined.
-/

namespace MGAP4D.MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Concatenating source lists starts the second budget at the actual first
terminal vector, not at the original vector. -/
theorem realHilbertProjectionSweepTargetResidualForcingBudget_append
    {E C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : C → E →L[ℝ] E) (forcing : C → E → ℝ)
    (first second : List C) (x : E) :
    realHilbertProjectionSweepTargetResidualForcingBudget P forcing (first ++ second) x =
      realHilbertProjectionSweepTargetResidualForcingBudget P forcing first x +
        realHilbertProjectionSweepTargetResidualForcingBudget P forcing second
          (realHilbertProjectionSweep P first x) := by
  induction first generalizing x with
  | nil =>
      simp only [List.nil_append, realHilbertProjectionSweepTargetResidualForcingBudget,
        realHilbertProjectionSweep, ContinuousLinearMap.id_apply, zero_add]
  | cons source first ih =>
      change forcing source x +
          realHilbertProjectionSweepTargetResidualForcingBudget P forcing (first ++ second) (P source x) =
        (forcing source x +
          realHilbertProjectionSweepTargetResidualForcingBudget P forcing first (P source x)) +
          realHilbertProjectionSweepTargetResidualForcingBudget P forcing second
            (realHilbertProjectionSweep P first (P source x))
      rw [ih]
      exact (add_assoc _ _ _).symm

/-- Exact finite source sum; equality is required only at actual trajectory
stages. Nodup is essential: a repeated source is not silently counted once. -/
theorem realHilbertProjectionSweepTargetResidualForcingBudget_eq_sum_of_trajectory
    {E C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq C]
    (P : C → E →L[ℝ] E) (forcing : C → E → ℝ) (cost : C → ℝ)
    (sources : List C) (x : E) (hNodup : sources.Nodup)
    (hStage : ∀ (before : List C) (source : C) (after : List C),
      sources = before ++ source :: after →
      forcing source (realHilbertProjectionSweep P before x) = cost source) :
    realHilbertProjectionSweepTargetResidualForcingBudget P forcing sources x =
      ∑ source ∈ sources.toFinset, cost source := by
  induction sources generalizing x with
  | nil => simp [realHilbertProjectionSweepTargetResidualForcingBudget]
  | cons source sources ih =>
      have hHead : forcing source x = cost source := by
        simpa only [realHilbertProjectionSweep, ContinuousLinearMap.id_apply] using
          hStage [] source sources rfl
      have hTail : ∀ (before : List C) (next : C) (after : List C),
          sources = before ++ next :: after →
          forcing next (realHilbertProjectionSweep P before (P source x)) = cost next := by
        intro before next after hSplit
        have hFull : source :: sources = (source :: before) ++ next :: after := by
          rw [hSplit]
          rfl
        simpa only [realHilbertProjectionSweep, ContinuousLinearMap.comp_apply] using
          hStage (source :: before) next after hFull
      change forcing source x +
          realHilbertProjectionSweepTargetResidualForcingBudget P forcing sources (P source x) = _
      rw [hHead, ih (P source x) hNodup.of_cons hTail]
      rw [List.toFinset_cons, Finset.sum_insert (by simpa using hNodup.notMem)]

end

end MGAP4D.MathlibAnalytic
