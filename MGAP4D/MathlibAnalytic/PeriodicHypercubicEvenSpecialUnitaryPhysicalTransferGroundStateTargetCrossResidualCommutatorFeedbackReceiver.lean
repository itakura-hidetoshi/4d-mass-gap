import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateTargetSourceCommutatorCoefficient
import Mathlib.Tactic

/-!
# One-step target-cross-residual commutator/feedback receiver

PRs #4914--#4917 isolate one source step into two pieces:

* projected forcing, carried by the target/source commutator;
* feedback, carried by the pre-existing target residual.

This file exposes the coefficient-preserving one-step receiver

  ||cross(t,s,x)||
    <= c_comm(t,s;beta) * ||P_t x||
       + ||cross(t,s,x - P_t x)||,

and its genuine fixed-color physical form with the first term charged directly
to ||x|| by conditional-expectation contraction.

At beta zero the projected forcing vanishes exactly, so the one-step cross
residual is literally equal to the feedback term.

No square expansion, finite-cardinality Cauchy estimate, arbitrary factor two,
response symmetry, or positive-beta commutativity is used.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Generic coefficient-preserving one-step target-cross-residual receiver. -/
theorem realHilbertProjectionSweepTargetCrossResidual_norm_le_commutatorCoefficient_mul_projectedNorm_add_feedback
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
      realHilbertProjectionSweepTargetSourceCommutatorCoefficient
          P target source *
          ‖P target x‖ +
        ‖realHilbertProjectionSweepTargetCrossResidual
          P target source (x - P target x)‖ := by
  rw [
    realHilbertProjectionSweepTargetCrossResidual_eq_projected_add_residual
      P target source x]
  calc
    ‖realHilbertProjectionSweepTargetCrossResidual
          P target source (P target x) +
        realHilbertProjectionSweepTargetCrossResidual
          P target source (x - P target x)‖ ≤
      ‖realHilbertProjectionSweepTargetCrossResidual
          P target source (P target x)‖ +
        ‖realHilbertProjectionSweepTargetCrossResidual
          P target source (x - P target x)‖ :=
        norm_add_le _ _
    _ ≤
      realHilbertProjectionSweepTargetSourceCommutatorCoefficient
          P target source *
          ‖P target x‖ +
        ‖realHilbertProjectionSweepTargetCrossResidual
          P target source (x - P target x)‖ := by
      exact
        add_le_add_right
          (realHilbertProjectionSweepTargetCrossResidual_projected_norm_le_commutatorCoefficient_mul_norm
            P target source hIdem x)
          _

/-- Genuine fixed-color one-step receiver.  Conditional-expectation
contraction charges the commutator forcing to the original Hilbert norm with
the same beta-zero-vanishing coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTargetCrossResidual_norm_le_commutatorCoefficient_mul_norm_add_feedback
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (target source :
      PeriodicHypercubicEvenFixedSpatialColorLink H color)
    (x :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :
    ‖realHilbertProjectionSweepTargetCrossResidual
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN beta hbeta color)
        target source x‖ ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTargetSourceCommutatorCoefficient
          H N hN beta hbeta color target source *
          ‖x‖ +
        ‖realHilbertProjectionSweepTargetCrossResidual
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
            H N hN beta hbeta color)
          target source
          (x -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
              H N hN beta hbeta color target x)‖ := by
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
      H N hN beta hbeta color
  rw [
    realHilbertProjectionSweepTargetCrossResidual_eq_projected_add_residual
      P target source x]
  calc
    ‖realHilbertProjectionSweepTargetCrossResidual
          P target source (P target x) +
        realHilbertProjectionSweepTargetCrossResidual
          P target source (x - P target x)‖ ≤
      ‖realHilbertProjectionSweepTargetCrossResidual
          P target source (P target x)‖ +
        ‖realHilbertProjectionSweepTargetCrossResidual
          P target source (x - P target x)‖ :=
        norm_add_le _ _
    _ ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTargetSourceCommutatorCoefficient
          H N hN beta hbeta color target source *
          ‖x‖ +
        ‖realHilbertProjectionSweepTargetCrossResidual
          P target source (x - P target x)‖ := by
      exact
        add_le_add_right
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTargetCrossResidual_projected_norm_le_commutatorCoefficient_mul_norm
            H N hN beta hbeta color target source x)
          _
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTargetSourceCommutatorCoefficient
          H N hN beta hbeta color target source *
          ‖x‖ +
        ‖realHilbertProjectionSweepTargetCrossResidual
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
            H N hN beta hbeta color)
          target source
          (x -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
              H N hN beta hbeta color target x)‖ := by
      rfl

/-- Exact beta-zero specialization: the forcing term disappears and one source
step acts only on the already-existing target residual. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTargetCrossResidual_zero_eq_feedback
    (H N : ℕ)
    (hN : 0 < N)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (target source :
      PeriodicHypercubicEvenFixedSpatialColorLink H color)
    (x :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN 0 (by norm_num)) :
    realHilbertProjectionSweepTargetCrossResidual
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN 0 (by norm_num) color)
        target source x =
      realHilbertProjectionSweepTargetCrossResidual
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN 0 (by norm_num) color)
        target source
        (x -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
            H N hN 0 (by norm_num) color target x) := by
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
      H N hN 0 (by norm_num) color
  rw [
    realHilbertProjectionSweepTargetCrossResidual_eq_projected_add_residual
      P target source x]
  have hZero :
      realHilbertProjectionSweepTargetCrossResidual
          P target source (P target x) = 0 := by
    simpa [P] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTargetCrossResidual_projected_zero
        H N hN color target source x
  rw [hZero, zero_add]
  rfl

/-- Norm form of the exact beta-zero feedback identity. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTargetCrossResidual_zero_norm_eq_feedback_norm
    (H N : ℕ)
    (hN : 0 < N)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (target source :
      PeriodicHypercubicEvenFixedSpatialColorLink H color)
    (x :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN 0 (by norm_num)) :
    ‖realHilbertProjectionSweepTargetCrossResidual
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN 0 (by norm_num) color)
        target source x‖ =
      ‖realHilbertProjectionSweepTargetCrossResidual
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN 0 (by norm_num) color)
        target source
        (x -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
            H N hN 0 (by norm_num) color target x)‖ := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTargetCrossResidual_zero_eq_feedback
      H N hN color target source x]

end

end MGAP4D.MathlibAnalytic
