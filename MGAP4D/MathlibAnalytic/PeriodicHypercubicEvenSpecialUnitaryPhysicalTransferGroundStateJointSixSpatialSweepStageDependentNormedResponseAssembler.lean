import MGAP4D.MathlibAnalytic.FiniteDependentNormedTransposeResponseProfile
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialSweepStageTransposeSchurReceiver
import Mathlib.Tactic

/-!
# Source-dependent normed response assembler for the physical transpose receiver

Each source link may carry its own normed response space.  This is the natural
form when the source profile is realized as an L2 norm over a source-specific
conditional pair/background law.

A dependent normed response decomposition with the actual physical envelope K
therefore feeds directly into the transpose six-spatial Schur receiver without
identifying distinct source L2 carriers.
-/

namespace MGAP4D.MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance dependentNormedResponseAssemblerSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance dependentNormedResponseAssemblerSpatialLinkNonempty
    (H : ℕ) :
    Nonempty (PeriodicHypercubicEvenSpatialSliceLink H) :=
  ⟨(⟨(0 : PeriodicHypercubicEvenVertex H), by
      simp [periodicHypercubicEvenOnPrimaryReflectionPlane]⟩,
    ⟨(1 : PeriodicHypercubicAxis), by norm_num⟩)⟩

/-- Source-dependent normed response data imply the exact transpose one-sided
profile needed by the uniform physical Schur receiver. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStage_dependentNormedResponse_global_energy_coercive_uniform
    (N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 1 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (H : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta)
    (E : PeriodicHypercubicEvenSpatialSliceLink H → Type*)
    [∀ e, NormedAddCommGroup (E e)]
    (state localPart : ∀ e, E e)
    (response : ∀ source target, E source)
    (hDecomp : ∀ source,
      state source = localPart source + ∑ target, response source target)
    (hLocal : ∀ source,
      ‖localPart source‖ ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile
          H N hN beta hbeta f source)
    (hResponse : ∀ source target,
      ‖response source target‖ ≤
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
          H N hN beta hbeta A).influence target source *
          ‖state target‖) :
    (1 / 6 : ℝ) *
        ((1 -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient
            s beta) ^ 2 *
          ∑ e : PeriodicHypercubicEvenSpatialSliceLink H, ‖state e‖ ^ 2) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSixSpatialResidualEnergy
        H N hN beta hbeta f := by
  have hOneSided : ∀ source,
      ‖state source‖ ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile
            H N hN beta hbeta f source +
          ∑ target,
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
              H N hN beta hbeta A).influence target source *
              ‖state target‖ := by
    exact
      FiniteDependentNormedTransposeResponseProfile.norm_profile_transpose_oneSided
        E
        (fun target source =>
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
            H N hN beta hbeta A).influence target source)
        state localPart response
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile
          H N hN beta hbeta f)
        hDecomp hLocal hResponse
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfile_transposeOneSided_global_energy_coercive_uniform
      N hN s hs beta hbeta hcut H A f
      (fun e => ‖state e‖)
      (fun e => norm_nonneg _)
      hOneSided

end

end MGAP4D.MathlibAnalytic
