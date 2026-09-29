import MGAP4D.MathlibAnalytic.RealHilbertProjectionSweepTargetResidualForcingBudgetTrajectory

namespace MGAP4D.MathlibAnalytic

#check realHilbertProjectionSweepTargetResidualForcingBudget_mono_on_trajectory
#check realHilbertProjectionSweep_targetResidual_norm_le_forcingBudget_add_initial_on_trajectory
#check realHilbertProjectionSweep_targetResidual_norm_le_forcingBudget_of_fixed_on_trajectory

-- A single actual step is sufficient: no estimate at other sources or vectors.
example {E C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : C → E →L[ℝ] E) (target source : C) (forcing : C → E → ℝ)
    (x : E) (hFixed : P target x = x)
    (hOne : ‖P source x - P target (P source x)‖ ≤
      forcing source x + ‖x - P target x‖) :
    ‖P source x - P target (P source x)‖ ≤ forcing source x := by
  have hTrajectory : ∀ (before : List C) (next : C) (after : List C),
      [source] = before ++ next :: after →
      ‖P next (realHilbertProjectionSweep P before x) -
          P target (P next (realHilbertProjectionSweep P before x))‖ ≤
        forcing next (realHilbertProjectionSweep P before x) +
          ‖realHilbertProjectionSweep P before x -
            P target (realHilbertProjectionSweep P before x)‖ := by
    intro before next after hSplit
    cases before with
    | nil =>
        have hEq : source = next ∧ [] = after := by
          simpa only [List.nil_append, List.cons.injEq] using hSplit
        rcases hEq with ⟨rfl, rfl⟩
        simpa only [realHilbertProjectionSweep, ContinuousLinearMap.id_apply] using hOne
    | cons first before =>
        have hLen := congrArg List.length hSplit
        simp only [List.length_cons, List.length_append, List.length_nil] at hLen
        omega
  have h := realHilbertProjectionSweep_targetResidual_norm_le_forcingBudget_of_fixed_on_trajectory
    P target forcing [source] x hTrajectory hFixed
  simpa only [realHilbertProjectionSweep,
    realHilbertProjectionSweepTargetResidualForcingBudget,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, add_zero] using h

-- Empty trajectories require no analytic one-step input.
example {E C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : C → E →L[ℝ] E) (target : C) (forcing : C → E → ℝ)
    (x : E) (hFixed : P target x = x) :
    ‖realHilbertProjectionSweep P [] x -
        P target (realHilbertProjectionSweep P [] x)‖ ≤
      realHilbertProjectionSweepTargetResidualForcingBudget P forcing [] x := by
  apply realHilbertProjectionSweep_targetResidual_norm_le_forcingBudget_of_fixed_on_trajectory
    P target forcing [] x _ hFixed
  intro before source after hSplit
  have hLen := congrArg List.length hSplit
  simp only [List.length_cons, List.length_append, List.length_nil] at hLen
  omega

end MGAP4D.MathlibAnalytic
