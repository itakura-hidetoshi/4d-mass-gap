import MGAP4D.MathlibAnalytic.RealHilbertProjectionSweepTargetCrossResidualLinearDecomposition
import Mathlib.Tactic

/-!
# Target/source commutator as the beta-small forcing carrier

For idempotent target projection P_t, the target-cross residual generated from
a target-fixed vector is exactly the target/source commutator applied to that
vector:

  cross(t,s,P_t x)
    = [P_t,P_s](P_t x).

Thus the exact forcing/feedback split becomes

  cross(t,s,x)
    = [P_t,P_s](P_t x)
      + cross(t,s,x-P_t x).

At beta zero the same-color one-link projections commute, so the forcing term
vanishes exactly.  At positive beta this commutator is therefore the natural
operator on which to preserve a beta-small coefficient.

This file introduces no probability estimate and no new coefficient.
-/

namespace MGAP4D.MathlibAnalytic

noncomputable section

/-- Continuous-linear target/source commutator with orientation
`target` first, `source` second. -/
noncomputable def realHilbertProjectionSweepTargetSourceCommutatorLinearMap
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (P : C → E →L[ℝ] E)
    (target source : C) :
    E →L[ℝ] E :=
  (P target).comp (P source) -
    (P source).comp (P target)

/-- Pointwise form of the target/source commutator. -/
theorem realHilbertProjectionSweepTargetSourceCommutatorLinearMap_apply
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (P : C → E →L[ℝ] E)
    (target source : C)
    (x : E) :
    realHilbertProjectionSweepTargetSourceCommutatorLinearMap
        P target source x =
      P target (P source x) -
        P source (P target x) := by
  simp [
    realHilbertProjectionSweepTargetSourceCommutatorLinearMap]

/-- On the target-fixed component, the exact cross residual is the commutator
forcing.  Only target idempotence is required. -/
theorem realHilbertProjectionSweepTargetCrossResidual_projected_eq_commutator_of_idempotent
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (P : C → E →L[ℝ] E)
    (target source : C)
    (hIdem :
      (P target).comp (P target) = P target)
    (x : E) :
    realHilbertProjectionSweepTargetCrossResidual
        P target source (P target x) =
      realHilbertProjectionSweepTargetSourceCommutatorLinearMap
        P target source (P target x) := by
  have hIdemApply : P target (P target x) = P target x := by
    have h :=
      congrArg
        (fun T : E →L[ℝ] E => T x)
        hIdem
    simpa using h
  unfold realHilbertProjectionSweepTargetCrossResidual
  rw [map_sub, hIdemApply]
  rw [realHilbertProjectionSweepTargetSourceCommutatorLinearMap_apply]
  rw [hIdemApply]
  abel

/-- Exact commutator-forcing plus residual-feedback decomposition. -/
theorem realHilbertProjectionSweepTargetCrossResidual_eq_commutator_add_feedback_of_idempotent
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (P : C → E →L[ℝ] E)
    (target source : C)
    (hIdem :
      (P target).comp (P target) = P target)
    (x : E) :
    realHilbertProjectionSweepTargetCrossResidual P target source x =
      realHilbertProjectionSweepTargetSourceCommutatorLinearMap
          P target source (P target x) +
        realHilbertProjectionSweepTargetCrossResidual
          P target source (x - P target x) := by
  rw [
    realHilbertProjectionSweepTargetCrossResidual_eq_projected_add_residual
      P target source x,
    realHilbertProjectionSweepTargetCrossResidual_projected_eq_commutator_of_idempotent
      P target source hIdem x]

/-- Receiver-ready amplitude inequality.  This uses only the ordinary norm
triangle inequality and therefore introduces no factor two. -/
theorem realHilbertProjectionSweepTargetCrossResidual_norm_le_commutator_add_feedback_of_idempotent
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (P : C → E →L[ℝ] E)
    (target source : C)
    (hIdem :
      (P target).comp (P target) = P target)
    (x : E) :
    ‖realHilbertProjectionSweepTargetCrossResidual
        P target source x‖ ≤
      ‖realHilbertProjectionSweepTargetSourceCommutatorLinearMap
          P target source (P target x)‖ +
        ‖realHilbertProjectionSweepTargetCrossResidual
          P target source (x - P target x)‖ := by
  rw [
    realHilbertProjectionSweepTargetCrossResidual_eq_commutator_add_feedback_of_idempotent
      P target source hIdem x]
  exact norm_add_le _ _

/-- If source and target commute, the commutator forcing is zero on every
vector. -/
theorem realHilbertProjectionSweepTargetSourceCommutatorLinearMap_eq_zero_of_commute
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (P : C → E →L[ℝ] E)
    (target source : C)
    (hComm :
      (P target).comp (P source) =
        (P source).comp (P target)) :
    realHilbertProjectionSweepTargetSourceCommutatorLinearMap
        P target source = 0 := by
  unfold realHilbertProjectionSweepTargetSourceCommutatorLinearMap
  rw [hComm]
  exact sub_self _

end

end MGAP4D.MathlibAnalytic
