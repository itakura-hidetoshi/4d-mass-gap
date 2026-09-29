import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateTargetCrossResidualCommutatorFeedbackReceiver
import Mathlib.Tactic

/-!
# Target residual update = commutator forcing + nonexpansive feedback

For self-adjoint idempotent projections, r_t(x) = x - P_t x satisfies

  r_t(P_s x) = -[P_t,P_s](P_t x) + r_t(P_s(r_t x)).

The feedback has norm at most ||r_t x||. Thus the commutator forcing
accumulates additively along an ordered sweep, without a cardinality factor.
The operator-norm coefficient still needs a volume-uniform beta-small bound;
its exact vanishing at beta zero alone does not supply that estimate.
No cross-projection commutativity is assumed at positive beta.
-/

namespace MGAP4D.MathlibAnalytic

open scoped InnerProductSpace InnerProduct

noncomputable section

/-- Exact one-step update of the distinguished target residual. -/
theorem realHilbertProjectionSweep_targetResidual_apply_eq_neg_commutator_add_feedback
    {E C : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : C → E →L[ℝ] E) (target source : C)
    (hTargetIdem : (P target).comp (P target) = P target) (x : E) :
    P source x - P target (P source x) =
      -realHilbertProjectionSweepTargetSourceCommutatorLinearMap P target source (P target x) +
        (P source (x - P target x) - P target (P source (x - P target x))) := by
  have hIdemApply : P target (P target x) = P target x := by
    have h := congrArg (fun T : E →L[ℝ] E => T x) hTargetIdem
    simpa only [ContinuousLinearMap.comp_apply] using h
  rw [realHilbertProjectionSweepTargetSourceCommutatorLinearMap_apply]
  simp only [map_sub]
  rw [hIdemApply]
  abel

/-- A self-adjoint idempotent projection is norm nonexpansive. -/
theorem realHilbertIdempotentSymmetricProjection_norm_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : E →L[ℝ] E) (hIdem : P.comp P = P)
    (hSymm : ∀ x y : E, inner ℝ (P x) y = inner ℝ x (P y)) (x : E) :
    ‖P x‖ ≤ ‖x‖ := by
  have hResidual := realHilbertProjection_residual_norm_sq P hIdem hSymm x
  have hSq : ‖P x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    nlinarith [sq_nonneg ‖x - P x‖]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hSq

/-- The complementary residual projection is also norm nonexpansive. -/
theorem realHilbertIdempotentSymmetricProjection_residual_norm_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : E →L[ℝ] E) (hIdem : P.comp P = P)
    (hSymm : ∀ x y : E, inner ℝ (P x) y = inner ℝ x (P y)) (x : E) :
    ‖x - P x‖ ≤ ‖x‖ := by
  have hResidual := realHilbertProjection_residual_norm_sq P hIdem hSymm x
  have hSq : ‖x - P x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    nlinarith [sq_nonneg ‖P x‖]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hSq

/-- One source step cannot increase the norm of the feedback term. -/
theorem realHilbertProjectionSweep_targetResidual_feedback_norm_le
    {E C : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : C → E →L[ℝ] E) (target source : C)
    (hIdem : ∀ c : C, (P c).comp (P c) = P c)
    (hSymm : ∀ (c : C) (x y : E), inner ℝ (P c x) y = inner ℝ x (P c y))
    (x : E) :
    ‖P source (x - P target x) - P target (P source (x - P target x))‖ ≤
      ‖x - P target x‖ := by
  exact
    (realHilbertIdempotentSymmetricProjection_residual_norm_le
      (P target) (hIdem target) (hSymm target) (P source (x - P target x))).trans
    (realHilbertIdempotentSymmetricProjection_norm_le
      (P source) (hIdem source) (hSymm source) (x - P target x))

/-- Commutator forcing plus nonexpansive transport of the initial residual. -/
theorem realHilbertProjectionSweep_targetResidual_apply_norm_le_commutatorCoefficient_mul_projectedNorm_add_residual
    {E C : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : C → E →L[ℝ] E) (target source : C)
    (hIdem : ∀ c : C, (P c).comp (P c) = P c)
    (hSymm : ∀ (c : C) (x y : E), inner ℝ (P c x) y = inner ℝ x (P c y))
    (x : E) :
    ‖P source x - P target (P source x)‖ ≤
      realHilbertProjectionSweepTargetSourceCommutatorCoefficient P target source *
        ‖P target x‖ + ‖x - P target x‖ := by
  rw [realHilbertProjectionSweep_targetResidual_apply_eq_neg_commutator_add_feedback
    P target source (hIdem target) x]
  calc
    ‖-realHilbertProjectionSweepTargetSourceCommutatorLinearMap P target source (P target x) +
        (P source (x - P target x) - P target (P source (x - P target x)))‖ ≤
      ‖realHilbertProjectionSweepTargetSourceCommutatorLinearMap P target source (P target x)‖ +
        ‖P source (x - P target x) - P target (P source (x - P target x))‖ := by
      simpa only [norm_neg] using
        (norm_add_le
          (-realHilbertProjectionSweepTargetSourceCommutatorLinearMap P target source (P target x))
          (P source (x - P target x) - P target (P source (x - P target x))))
    _ ≤ realHilbertProjectionSweepTargetSourceCommutatorCoefficient P target source *
        ‖P target x‖ + ‖x - P target x‖ :=
      _root_.add_le_add
        (ContinuousLinearMap.le_opNorm
          (realHilbertProjectionSweepTargetSourceCommutatorLinearMap P target source) (P target x))
        (realHilbertProjectionSweep_targetResidual_feedback_norm_le
          P target source hIdem hSymm x)

/-- Genuine fixed-color physical one-step target-residual recurrence. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLink_targetResidual_apply_norm_le_commutatorCoefficient_mul_norm_add_residual
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (target source : PeriodicHypercubicEvenFixedSpatialColorLink H color)
    (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN beta hbeta color source x -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN beta hbeta color target
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
            H N hN beta hbeta color source x)‖ ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTargetSourceCommutatorCoefficient
          H N hN beta hbeta color target source * ‖x‖ +
        ‖x - periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN beta hbeta color target x‖ := by
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
      H N hN beta hbeta color
  have hIdem : ∀ e, (P e).comp (P e) = P e := by
    intro e
    simpa only [P,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_idempotent
        H N hN beta hbeta e.1
  have hSymm : ∀ (e : PeriodicHypercubicEvenFixedSpatialColorLink H color)
      (u v : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta),
      inner ℝ (P e u) v = inner ℝ u (P e v) := by
    intro e u v
    simpa only [P,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_symmetric
        H N hN beta hbeta e.1 u v
  have hStep :=
    realHilbertProjectionSweep_targetResidual_apply_norm_le_commutatorCoefficient_mul_projectedNorm_add_residual
      P target source hIdem hSymm x
  have hProj := realHilbertIdempotentSymmetricProjection_norm_le
    (P target) (hIdem target) (hSymm target) x
  have hCoeff := realHilbertProjectionSweepTargetSourceCommutatorCoefficient_nonneg P target source
  exact hStep.trans
    (_root_.add_le_add (mul_le_mul_of_nonneg_left hProj hCoeff) le_rfl)

/-- At beta zero the commutator forcing coefficient is exactly zero. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLink_targetResidual_apply_norm_le_residual_zero
    (H N : ℕ) (hN : 0 < N)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (target source : PeriodicHypercubicEvenFixedSpatialColorLink H color)
    (x : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN 0 le_rfl) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN 0 le_rfl color source x -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN 0 le_rfl color target
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
            H N hN 0 le_rfl color source x)‖ ≤
      ‖x - periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
        H N hN 0 le_rfl color target x‖ := by
  have h :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLink_targetResidual_apply_norm_le_commutatorCoefficient_mul_norm_add_residual
      H N hN 0 le_rfl color target source x
  simpa only [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTargetSourceCommutatorCoefficient_zero,
    zero_mul, zero_add] using h

end

end MGAP4D.MathlibAnalytic
