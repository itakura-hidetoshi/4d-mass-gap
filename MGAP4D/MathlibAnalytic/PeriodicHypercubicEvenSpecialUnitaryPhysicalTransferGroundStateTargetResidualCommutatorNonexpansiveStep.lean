import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateTargetCrossResidualCommutatorFeedbackReceiver
import Mathlib.Tactic

/-!
# Target residual update = commutator forcing + nonexpansive feedback

For two self-adjoint idempotent projections `P_target` and `P_source`,
write

  r_target(x) = x - P_target x.

One source update has the exact decomposition

  r_target(P_source x)
    = -[P_target,P_source](P_target x)
      + r_target(P_source (r_target x)).

The second term is nonexpansive:

  ||r_target(P_source (r_target x))|| <= ||r_target x||.

Hence the only coefficient that must become small near beta zero is the
target/source commutator coefficient.  Iterating this inequality can
accumulate the forcing terms without multiplying by the number of source
links and without assigning an additional Schur coefficient to the feedback
transport.

No cross-projection commutativity is assumed at positive beta.
-/

namespace MGAP4D.MathlibAnalytic

open scoped InnerProductSpace InnerProduct

noncomputable section

/-- Exact one-step update of the distinguished target residual. -/
theorem realHilbertProjectionSweep_targetResidual_apply_eq_neg_commutator_add_feedback
    {E C : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (P : C → E →L[ℝ] E)
    (target source : C)
    (hTargetIdem :
      (P target).comp (P target) = P target)
    (x : E) :
    P source x - P target (P source x) =
      -realHilbertProjectionSweepTargetSourceCommutatorLinearMap
          P target source (P target x) +
        (P source (x - P target x) -
          P target (P source (x - P target x))) := by
  have hIdemApply :
      P target (P target x) = P target x := by
    have h :=
      congrArg (fun T : E →L[ℝ] E => T x) hTargetIdem
    simpa using h
  rw [realHilbertProjectionSweepTargetSourceCommutatorLinearMap_apply]
  simp only [map_sub]
  rw [hIdemApply]
  abel

/-- A self-adjoint idempotent projection is norm nonexpansive. -/
theorem realHilbertIdempotentSymmetricProjection_norm_le
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (P : E →L[ℝ] E)
    (hIdem : P.comp P = P)
    (hSymm : ∀ x y : E, inner ℝ (P x) y = inner ℝ x (P y))
    (x : E) :
    ‖P x‖ ≤ ‖x‖ := by
  have hResidual :=
    realHilbertProjection_residual_norm_sq P hIdem hSymm x
  have hSq :
      ‖P x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    nlinarith [sq_nonneg ‖x - P x‖]
  nlinarith [norm_nonneg (P x), norm_nonneg x]

/-- The complementary residual of a self-adjoint idempotent projection is
also norm nonexpansive. -/
theorem realHilbertIdempotentSymmetricProjection_residual_norm_le
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (P : E →L[ℝ] E)
    (hIdem : P.comp P = P)
    (hSymm : ∀ x y : E, inner ℝ (P x) y = inner ℝ x (P y))
    (x : E) :
    ‖x - P x‖ ≤ ‖x‖ := by
  have hResidual :=
    realHilbertProjection_residual_norm_sq P hIdem hSymm x
  have hSq :
      ‖x - P x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    nlinarith [sq_nonneg ‖P x‖]
  nlinarith [norm_nonneg (x - P x), norm_nonneg x]

/-- The feedback part of one source step cannot increase the current target
residual norm. -/
theorem realHilbertProjectionSweep_targetResidual_feedback_norm_le
    {E C : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (P : C → E →L[ℝ] E)
    (target source : C)
    (hIdem : ∀ c : C, (P c).comp (P c) = P c)
    (hSymm : ∀ (c : C) (x y : E),
      inner ℝ (P c x) y = inner ℝ x (P c y))
    (x : E) :
    ‖P source (x - P target x) -
        P target (P source (x - P target x))‖ ≤
      ‖x - P target x‖ := by
  let r := x - P target x
  have hSource :
      ‖P source r‖ ≤ ‖r‖ :=
    realHilbertIdempotentSymmetricProjection_norm_le
      (P source) (hIdem source) (hSymm source) r
  have hTarget :
      ‖P source r - P target (P source r)‖ ≤ ‖P source r‖ :=
    realHilbertIdempotentSymmetricProjection_residual_norm_le
      (P target) (hIdem target) (hSymm target) (P source r)
  exact hTarget.trans hSource

/-- One-step target-residual amplitude recurrence: commutator forcing plus
nonexpansive transport of the already-existing target residual. -/
theorem realHilbertProjectionSweep_targetResidual_apply_norm_le_commutatorCoefficient_mul_projectedNorm_add_residual
    {E C : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (P : C → E →L[ℝ] E)
    (target source : C)
    (hIdem : ∀ c : C, (P c).comp (P c) = P c)
    (hSymm : ∀ (c : C) (x y : E),
      inner ℝ (P c x) y = inner ℝ x (P c y))
    (x : E) :
    ‖P source x - P target (P source x)‖ ≤
      realHilbertProjectionSweepTargetSourceCommutatorCoefficient
          P target source *
          ‖P target x‖ +
        ‖x - P target x‖ := by
  rw [
    realHilbertProjectionSweep_targetResidual_apply_eq_neg_commutator_add_feedback
      P target source (hIdem target) x]
  calc
    ‖-realHilbertProjectionSweepTargetSourceCommutatorLinearMap
          P target source (P target x) +
        (P source (x - P target x) -
          P target (P source (x - P target x)))‖ ≤
      ‖realHilbertProjectionSweepTargetSourceCommutatorLinearMap
          P target source (P target x)‖ +
        ‖P source (x - P target x) -
          P target (P source (x - P target x))‖ := by
      simpa using
        (norm_add_le
          (-realHilbertProjectionSweepTargetSourceCommutatorLinearMap
            P target source (P target x))
          (P source (x - P target x) -
            P target (P source (x - P target x))))
    _ ≤
      realHilbertProjectionSweepTargetSourceCommutatorCoefficient
          P target source *
          ‖P target x‖ +
        ‖x - P target x‖ := by
      exact add_le_add
        (ContinuousLinearMap.le_opNorm
          (realHilbertProjectionSweepTargetSourceCommutatorLinearMap
            P target source)
          (P target x))
        (realHilbertProjectionSweep_targetResidual_feedback_norm_le
          P target source hIdem hSymm x)

/-- Genuine fixed-color physical one-step target-residual recurrence. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLink_targetResidual_apply_norm_le_commutatorCoefficient_mul_norm_add_residual
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
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN beta hbeta color source x -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN beta hbeta color target
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
            H N hN beta hbeta color source x)‖ ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTargetSourceCommutatorCoefficient
          H N hN beta hbeta color target source *
          ‖x‖ +
        ‖x -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
            H N hN beta hbeta color target x‖ := by
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
      H N hN beta hbeta color
  have hIdem : ∀ e, (P e).comp (P e) = P e := by
    intro e
    simpa [
      P,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_idempotent
        H N hN beta hbeta e.1
  have hSymm :
      ∀ (e : PeriodicHypercubicEvenFixedSpatialColorLink H color)
        (u v :
          PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
            H N hN beta hbeta),
        inner ℝ (P e u) v = inner ℝ u (P e v) := by
    intro e u v
    simpa [
      P,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_symmetric
        H N hN beta hbeta e.1 u v
  have hStep :=
    realHilbertProjectionSweep_targetResidual_apply_norm_le_commutatorCoefficient_mul_projectedNorm_add_residual
      P target source hIdem hSymm x
  have hProj :
      ‖P target x‖ ≤ ‖x‖ := by
    exact
      realHilbertIdempotentSymmetricProjection_norm_le
        (P target) (hIdem target) (hSymm target) x
  have hCoeff :
      0 ≤
        realHilbertProjectionSweepTargetSourceCommutatorCoefficient
          P target source :=
    realHilbertProjectionSweepTargetSourceCommutatorCoefficient_nonneg
      P target source
  calc
    ‖P source x - P target (P source x)‖ ≤
      realHilbertProjectionSweepTargetSourceCommutatorCoefficient
          P target source *
          ‖P target x‖ +
        ‖x - P target x‖ := hStep
    _ ≤
      realHilbertProjectionSweepTargetSourceCommutatorCoefficient
          P target source *
          ‖x‖ +
        ‖x - P target x‖ := by
      exact add_le_add_right
        (mul_le_mul_of_nonneg_left hProj hCoeff)
        _
    _ =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTargetSourceCommutatorCoefficient
          H N hN beta hbeta color target source *
          ‖x‖ +
        ‖x -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
            H N hN beta hbeta color target x‖ := by
      rfl

/-- At beta zero the one-step target residual is nonincreasing, because the
commutator forcing coefficient is exactly zero. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLink_targetResidual_apply_norm_le_residual_zero
    (H N : ℕ)
    (hN : 0 < N)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (target source :
      PeriodicHypercubicEvenFixedSpatialColorLink H color)
    (x :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN 0 (by norm_num)) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN 0 (by norm_num) color source x -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN 0 (by norm_num) color target
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
            H N hN 0 (by norm_num) color source x)‖ ≤
      ‖x -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
          H N hN 0 (by norm_num) color target x‖ := by
  have h :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLink_targetResidual_apply_norm_le_commutatorCoefficient_mul_norm_add_residual
      H N hN 0 (by norm_num) color target source x
  simpa using h

end

end MGAP4D.MathlibAnalytic
