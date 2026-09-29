import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaZeroGroundStateTargetSourceCommutator
import Mathlib.Tactic

/-!
# Target/source commutator coefficient

PRs #4914--#4916 isolate the target-cross-residual forcing as the
target/source projection commutator and prove that this commutator vanishes
exactly at beta zero on the genuine ground-state joint L2 carrier.

This file packages the operator norm of that commutator as the coefficient
seen by the forcing term.  The resulting estimate uses only the standard
continuous-linear-map operator-norm inequality and the L2 contraction of
conditional expectation.

Thus no finite-cardinality loss, factor two, response symmetry, or positive-
beta commutativity assumption is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory

noncomputable section

/-- Operator-norm coefficient of one target/source projection commutator. -/
noncomputable def realHilbertProjectionSweepTargetSourceCommutatorCoefficient
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (P : C → E →L[ℝ] E)
    (target source : C) : ℝ :=
  ‖realHilbertProjectionSweepTargetSourceCommutatorLinearMap
      P target source‖

theorem realHilbertProjectionSweepTargetSourceCommutatorCoefficient_nonneg
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (P : C → E →L[ℝ] E)
    (target source : C) :
    0 ≤
      realHilbertProjectionSweepTargetSourceCommutatorCoefficient
        P target source := by
  exact norm_nonneg _

/-- The projected forcing is bounded by the commutator operator norm with no
additional numerical constant. -/
theorem realHilbertProjectionSweepTargetCrossResidual_projected_norm_le_commutatorCoefficient_mul_norm
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (P : C → E →L[ℝ] E)
    (target source : C)
    (hIdem :
      (P target).comp (P target) = P target)
    (x : E) :
    ‖realHilbertProjectionSweepTargetCrossResidual
        P target source (P target x)‖ ≤
      realHilbertProjectionSweepTargetSourceCommutatorCoefficient
          P target source *
        ‖P target x‖ := by
  rw [
    realHilbertProjectionSweepTargetCrossResidual_projected_eq_commutator_of_idempotent
      P target source hIdem x]
  exact
    ContinuousLinearMap.le_opNorm
      (realHilbertProjectionSweepTargetSourceCommutatorLinearMap
        P target source)
      (P target x)

/-- Genuine fixed-color physical commutator coefficient. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTargetSourceCommutatorCoefficient
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (target source :
      PeriodicHypercubicEvenFixedSpatialColorLink H color) : ℝ :=
  realHilbertProjectionSweepTargetSourceCommutatorCoefficient
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
      H N hN beta hbeta color)
    target source

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTargetSourceCommutatorCoefficient_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (target source :
      PeriodicHypercubicEvenFixedSpatialColorLink H color) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTargetSourceCommutatorCoefficient
        H N hN beta hbeta color target source := by
  exact
    realHilbertProjectionSweepTargetSourceCommutatorCoefficient_nonneg
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
        H N hN beta hbeta color)
      target source

/-- The physical projected forcing is bounded by its exact commutator
coefficient times the target-projected input norm. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTargetCrossResidual_projected_norm_le_commutatorCoefficient_mul_projectedNorm
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
        target source
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN beta hbeta color target x)‖ ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTargetSourceCommutatorCoefficient
          H N hN beta hbeta color target source *
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN beta hbeta color target x‖ := by
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
      H N hN beta hbeta color
  have hIdem : (P target).comp (P target) = P target := by
    simpa [
      P,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_idempotent
        H N hN beta hbeta target.1
  simpa [
    P,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTargetSourceCommutatorCoefficient] using
    realHilbertProjectionSweepTargetCrossResidual_projected_norm_le_commutatorCoefficient_mul_norm
      P target source hIdem x

/-- Conditional expectation is contractive, so the projected forcing may be
charged directly to the original Hilbert norm with the same commutator
coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTargetCrossResidual_projected_norm_le_commutatorCoefficient_mul_norm
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
        target source
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN beta hbeta color target x)‖ ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTargetSourceCommutatorCoefficient
          H N hN beta hbeta color target source *
        ‖x‖ := by
  have hForcing :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTargetCrossResidual_projected_norm_le_commutatorCoefficient_mul_projectedNorm
      H N hN beta hbeta color target source x
  have hProj :
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN beta hbeta color target x‖ ≤
        ‖x‖ := by
    simpa [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_apply] using
      (norm_condExpL2_coe_le
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace_le
          H N target.1)
        x)
  exact
    hForcing.trans
      (mul_le_mul_of_nonneg_left
        hProj
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTargetSourceCommutatorCoefficient_nonneg
          H N hN beta hbeta color target source))

/-- Exact endpoint anchor: every physical target/source commutator coefficient
vanishes at beta zero. -/
@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTargetSourceCommutatorCoefficient_zero
    (H N : ℕ)
    (hN : 0 < N)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (target source :
      PeriodicHypercubicEvenFixedSpatialColorLink H color) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTargetSourceCommutatorCoefficient
        H N hN 0 (by norm_num) color target source = 0 := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTargetSourceCommutatorCoefficient
    realHilbertProjectionSweepTargetSourceCommutatorCoefficient
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTargetSourceCommutator_zero
      H N hN color target source]
  exact norm_zero

end

end MGAP4D.MathlibAnalytic
