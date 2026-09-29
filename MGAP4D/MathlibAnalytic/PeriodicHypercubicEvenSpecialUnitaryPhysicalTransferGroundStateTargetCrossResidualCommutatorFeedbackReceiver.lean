import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateTargetSourceCommutatorCoefficient
import Mathlib.Tactic

/-!
# One-step target-cross-residual commutator/feedback receiver

The exact projected-forcing/residual-feedback split gives

  ||cross(t,s,x)|| <= c_comm(t,s) * ||P_t x|| + ||cross(t,s,x-P_t x)||.

On the genuine physical carrier conditional-expectation contraction also
bounds the forcing by c_comm(t,s) * ||x||. At beta zero it vanishes exactly.
No square expansion, cardinality loss, response symmetry, or positive-beta
commutativity is used. The feedback equalities are explicit rewrite lemmas,
not simp rules: their right-hand sides contain the same function at a larger
argument and must not be registered as unrestricted recursive rewrites.
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
    (hIdem : (P target).comp (P target) = P target)
    (x : E) :
    ‖realHilbertProjectionSweepTargetCrossResidual P target source x‖ ≤
      realHilbertProjectionSweepTargetSourceCommutatorCoefficient P target source *
          ‖P target x‖ +
        ‖realHilbertProjectionSweepTargetCrossResidual P target source (x - P target x)‖ := by
  rw [realHilbertProjectionSweepTargetCrossResidual_eq_projected_add_residual
    P target source x]
  exact (norm_add_le _ _).trans
    (_root_.add_le_add
      (realHilbertProjectionSweepTargetCrossResidual_projected_norm_le_commutatorCoefficient_mul_norm
        P target source hIdem x)
      le_rfl)

/-- Genuine fixed-color receiver with the same coefficient on the input norm. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTargetCrossResidual_norm_le_commutatorCoefficient_mul_norm_add_feedback
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (target source : PeriodicHypercubicEvenFixedSpatialColorLink H color)
    (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta) :
    ‖realHilbertProjectionSweepTargetCrossResidual
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN beta hbeta color) target source x‖ ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTargetSourceCommutatorCoefficient
          H N hN beta hbeta color target source * ‖x‖ +
        ‖realHilbertProjectionSweepTargetCrossResidual
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
            H N hN beta hbeta color) target source
          (x - periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
            H N hN beta hbeta color target x)‖ := by
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
      H N hN beta hbeta color
  rw [realHilbertProjectionSweepTargetCrossResidual_eq_projected_add_residual
    P target source x]
  exact (norm_add_le _ _).trans
    (_root_.add_le_add
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTargetCrossResidual_projected_norm_le_commutatorCoefficient_mul_norm
        H N hN beta hbeta color target source x)
      le_rfl)

/-- At beta zero one source step acts only on the existing target residual.
This expanding equality is intentionally not a simp rule. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTargetCrossResidual_zero_eq_feedback
    (H N : ℕ) (hN : 0 < N)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (target source : PeriodicHypercubicEvenFixedSpatialColorLink H color)
    (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN 0 le_rfl) :
    realHilbertProjectionSweepTargetCrossResidual
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN 0 le_rfl color) target source x =
      realHilbertProjectionSweepTargetCrossResidual
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN 0 le_rfl color) target source
        (x - periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN 0 le_rfl color target x) := by
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
      H N hN 0 le_rfl color
  have hZero :
      realHilbertProjectionSweepTargetCrossResidual P target source (P target x) = 0 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTargetCrossResidual_projected_zero
      H N hN color target source x
  simpa only [hZero, zero_add] using
    (realHilbertProjectionSweepTargetCrossResidual_eq_projected_add_residual
      P target source x)

/-- Norm form of the explicit beta-zero feedback identity. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTargetCrossResidual_zero_norm_eq_feedback_norm
    (H N : ℕ) (hN : 0 < N)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (target source : PeriodicHypercubicEvenFixedSpatialColorLink H color)
    (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN 0 le_rfl) :
    ‖realHilbertProjectionSweepTargetCrossResidual
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN 0 le_rfl color) target source x‖ =
      ‖realHilbertProjectionSweepTargetCrossResidual
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN 0 le_rfl color) target source
        (x - periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN 0 le_rfl color target x)‖ := by
  exact congrArg (fun y => ‖y‖)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTargetCrossResidual_zero_eq_feedback
      H N hN color target source x)

end

end MGAP4D.MathlibAnalytic
