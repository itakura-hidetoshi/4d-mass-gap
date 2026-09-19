import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceRemotePhysicalInfluenceResidual
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
import MGAP4D.MathlibAnalytic.FinitePositiveWeightReciprocalInfluenceKernelResponse
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance fixedTargetPhysicalLeftInfluenceEnvelopeSpatialLinkFintype
    (H : Nat) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance fixedTargetPhysicalLeftInfluenceEnvelopeSpecialUnitaryMeasurableSpace
    (N : Nat) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) Complex) :=
  specialUnitaryGroupMeasurableSpace N

/-- A fixed-target physical left-left influence envelope for the exact
kernel-section one-link law.

For an off-diagonal physical target/source pair, the C5 exceptional region is
controlled by the volume-independent background-update Harnack coefficient,
while the C5-remote region keeps the target-specific actual cross-ratio
residual.  Unlike the older coarse distinct-fiber carrier, this definition does
not replace every off-diagonal pair by one constant coefficient.

The distinguished target of the kernel-section law remains explicit. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel
    (H N : Nat)
    (hN : 0 < N)
    (beta : Real)
    (hbeta : 0 <= beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedTarget : PeriodicHypercubicEvenSpatialSliceLink H) :
    FiniteNonnegativeInfluenceKernelData
      (PeriodicHypercubicEvenSpatialSliceLink H) := by
  classical
  exact
    { influence := fun target source =>
        if target = source then 0
        else if target ∈
            periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers
              H source distinguishedTarget then
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta
        else
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemotePhysicalInfluenceResidual
            H N hN beta hbeta A source distinguishedTarget target
      influence_nonneg := by
        intro target source
        by_cases hEq : target = source
        · simp [hEq]
        · simp only [hEq, if_false]
          by_cases hExceptional :
              target ∈
                periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers
                  H source distinguishedTarget
          · rw [if_pos hExceptional]
            exact
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence_nonneg
                beta hbeta
          · rw [if_neg hExceptional]
            exact
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemotePhysicalInfluenceResidual_nonneg
                H N hN beta hbeta A source distinguishedTarget target
      influence_diagonal_zero := by
        intro source
        simp }

/-- On a non-diagonal C5-exceptional pair, the fixed-target envelope is exactly
the local Harnack coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel_eq_harnack_of_exceptional
    (H N : Nat)
    (hN : 0 < N)
    (beta : Real)
    (hbeta : 0 <= beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedTarget target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (hExceptional :
      target ∈
        periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers
          H source distinguishedTarget) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel
        H N hN beta hbeta A distinguishedTarget).influence target source =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
        beta := by
  simp [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel,
    hne, hExceptional]

/-- On a C5-remote pair, the fixed-target envelope is exactly the actual
target-specific remote physical residual. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel_eq_remoteResidual_of_remote
    (H N : Nat)
    (hN : 0 < N)
    (beta : Real)
    (hbeta : 0 <= beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedTarget target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hRemote :
      target ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
          H source distinguishedTarget) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel
        H N hN beta hbeta A distinguishedTarget).influence target source =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemotePhysicalInfluenceResidual
        H N hN beta hbeta A source distinguishedTarget target := by
  classical
  have hNotExceptional :
      target ∉
        periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers
          H source distinguishedTarget := by
    simpa [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers] using
      hRemote
  rcases
    periodicHypercubicEvenSpatialSlice_not_mem_C5ExceptionalBackgroundFibers
      H source distinguishedTarget target hNotExceptional with
    ⟨hSourceTarget, _hTargetDistinguished, _hNoShare⟩
  simp [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel,
    Ne.symm hSourceTarget, hNotExceptional]

/-- Every off-diagonal background-value update of the exact fixed-target
kernel-section one-link law is dominated by the fixed-target sparse/remote
physical envelope.

This theorem is the law-level bridge needed after the coarse-carrier
spatial-flatness obstruction: local exceptional pairs use the literal Harnack
bound, while genuinely remote pairs retain the actual cross-ratio residual.
No source-aligned identification is used. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_fixedTargetPhysicalLeft_boundedTest_difference_le_envelopeKernel
    (H N : Nat)
    (hN : 0 < N)
    (beta : Real)
    (hbeta : 0 <= beta)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedTarget distinguishedSource target source :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : target ≠ source)
    (k g2 u v : Matrix.specialUnitaryGroup (Fin N) Complex)
    (phi : Matrix.specialUnitaryGroup (Fin N) Complex -> Real)
    (hphi : StronglyMeasurable phi)
    (hphiBound : forall g, |phi g| <= 1) :
    |(∫ g, phi g
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B distinguishedTarget distinguishedSource target k g2
          (Function.update A source u)) -
      (∫ g, phi g
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B distinguishedTarget distinguishedSource target k g2
          (Function.update A source v))| <=
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel
        H N hN beta hbeta A distinguishedTarget).influence target source := by
  classical
  by_cases hExceptional :
      target ∈
        periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers
          H source distinguishedTarget
  · have hLocal :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_backgroundUpdate_boundedTest_difference_le_harnackInfluence
        H N hN beta hbeta B distinguishedTarget distinguishedSource target source
        hne k g2 u v A phi hphi hphiBound
    simpa [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel,
      hne, hExceptional] using hLocal
  · have hRemote :
        target ∈
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
            H source distinguishedTarget := by
      simpa [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers] using
        hExceptional
    have hRemoteBound :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_remote_boundedTest_difference_le_physicalResidual
        H N hN beta hbeta B A source distinguishedTarget distinguishedSource target
        hRemote k g2 u v phi hphi hphiBound
    simpa [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetPhysicalLeftInfluenceEnvelopeKernel,
      hne, hExceptional] using hRemoteBound

end

end MathlibAnalytic
end MGAP4D
