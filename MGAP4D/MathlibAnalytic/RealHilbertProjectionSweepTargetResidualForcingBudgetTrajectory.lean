import MGAP4D.MathlibAnalytic.RealHilbertProjectionSweepTargetResidualForcingBudgetTelescope
import Mathlib.Tactic

/-!
# Forcing-budget comparison on the actual trajectory

The universal receiver from PR #4920 is not a bounded-core theorem. This file
supplies its domain-correct adapter without rebuilding its telescope or budget.

First compare two existing budgets only at the stages that the ordered list
actually visits. Then apply the existing universal receiver to the exact
increment of the target-residual norm. This increment satisfies its one-step
hypothesis identically on the ambient space; only its comparison with the
analytic forcing is restricted to the actual trajectory.

The auxiliary increment can be negative. No nonnegativity, invariant-domain
extension, off-trajectory analytic estimate, cardinality factor, or new budget
definition is needed.
-/

namespace MGAP4D.MathlibAnalytic

noncomputable section

/-- Pointwise comparison is needed only at actual before-source stage vectors. -/
theorem realHilbertProjectionSweepTargetResidualForcingBudget_mono_on_trajectory
    {E C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : C → E →L[ℝ] E) (forcing upper : C → E → ℝ)
    (sources : List C) (x : E)
    (hCompare : ∀ (before : List C) (source : C) (after : List C),
      sources = before ++ source :: after →
      forcing source (realHilbertProjectionSweep P before x) ≤
        upper source (realHilbertProjectionSweep P before x)) :
    realHilbertProjectionSweepTargetResidualForcingBudget P forcing sources x ≤
      realHilbertProjectionSweepTargetResidualForcingBudget P upper sources x := by
  induction sources generalizing x with
  | nil => exact le_rfl
  | cons source sources ih =>
      have hHead : forcing source x ≤ upper source x := by
        simpa only [realHilbertProjectionSweep, ContinuousLinearMap.id_apply] using
          hCompare [] source sources rfl
      have hTail : ∀ (before : List C) (next : C) (after : List C),
          sources = before ++ next :: after →
          forcing next (realHilbertProjectionSweep P before (P source x)) ≤
            upper next (realHilbertProjectionSweep P before (P source x)) := by
        intro before next after hSplit
        have hFull : source :: sources = (source :: before) ++ next :: after := by
          rw [hSplit]
          rfl
        simpa only [realHilbertProjectionSweep, ContinuousLinearMap.comp_apply] using
          hCompare (source :: before) next after hFull
      change
        forcing source x +
            realHilbertProjectionSweepTargetResidualForcingBudget P forcing sources (P source x) ≤
          upper source x +
            realHilbertProjectionSweepTargetResidualForcingBudget P upper sources (P source x)
      exact _root_.add_le_add hHead (ih (P source x) hTail)

/-- The analytic one-step estimate need only hold on the displayed trajectory.
The ambient universal receiver is used only for the exact residual increment. -/
theorem realHilbertProjectionSweep_targetResidual_norm_le_forcingBudget_add_initial_on_trajectory
    {E C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : C → E →L[ℝ] E) (target : C) (forcing : C → E → ℝ)
    (sources : List C) (x : E)
    (hStep : ∀ (before : List C) (source : C) (after : List C),
      sources = before ++ source :: after →
      ‖P source (realHilbertProjectionSweep P before x) -
          P target (P source (realHilbertProjectionSweep P before x))‖ ≤
        forcing source (realHilbertProjectionSweep P before x) +
          ‖realHilbertProjectionSweep P before x -
            P target (realHilbertProjectionSweep P before x)‖) :
    ‖realHilbertProjectionSweep P sources x -
        P target (realHilbertProjectionSweep P sources x)‖ ≤
      realHilbertProjectionSweepTargetResidualForcingBudget P forcing sources x +
        ‖x - P target x‖ := by
  let increment : C → E → ℝ := fun source y =>
    ‖P source y - P target (P source y)‖ - ‖y - P target y‖
  have hExact : ∀ (source : C) (y : E),
      ‖P source y - P target (P source y)‖ ≤
        increment source y + ‖y - P target y‖ := by
    intro source y
    exact le_of_eq (sub_add_cancel _ _).symm
  have hBudget :=
    realHilbertProjectionSweepTargetResidualForcingBudget_mono_on_trajectory
      P increment forcing sources x (by
        intro before source after hSplit
        exact (sub_le_iff_le_add).2 (hStep before source after hSplit))
  exact
    (realHilbertProjectionSweep_targetResidual_norm_le_forcingBudget_add_initial
      P target increment hExact sources x).trans
      (_root_.add_le_add hBudget le_rfl)

/-- Target-fixed specialization, without any off-trajectory analytic input. -/
theorem realHilbertProjectionSweep_targetResidual_norm_le_forcingBudget_of_fixed_on_trajectory
    {E C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : C → E →L[ℝ] E) (target : C) (forcing : C → E → ℝ)
    (sources : List C) (x : E)
    (hStep : ∀ (before : List C) (source : C) (after : List C),
      sources = before ++ source :: after →
      ‖P source (realHilbertProjectionSweep P before x) -
          P target (P source (realHilbertProjectionSweep P before x))‖ ≤
        forcing source (realHilbertProjectionSweep P before x) +
          ‖realHilbertProjectionSweep P before x -
            P target (realHilbertProjectionSweep P before x)‖)
    (hFixed : P target x = x) :
    ‖realHilbertProjectionSweep P sources x -
        P target (realHilbertProjectionSweep P sources x)‖ ≤
      realHilbertProjectionSweepTargetResidualForcingBudget P forcing sources x := by
  have h :=
    realHilbertProjectionSweep_targetResidual_norm_le_forcingBudget_add_initial_on_trajectory
      P target forcing sources x hStep
  simpa only [hFixed, sub_self, norm_zero, add_zero] using h

end

end MGAP4D.MathlibAnalytic
