import MGAP4D.MathlibAnalytic.FiniteNormedResponseOneSidedProfile
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialSweepStageSchurReceiver
import Mathlib.Tactic

/-!
# Normed-response assembler for the physical six-spatial Schur receiver

Once the physical hybrid/trajectory layer produces, for each target link, a
normed vector decomposition

  state_t = local_t + sum_s response_{t,s}

with

  ||local_t|| <= ell_t
  ||response_{t,s}|| <= K(t,s) ||state_s||,

the scalar profile u_t := ||state_t|| satisfies the exact one-sided recurrence
required by the already-proved Schur receiver.

This file isolates that final algebraic assembly.  It uses no finite-cardinality
Cauchy--Schwarz estimate and therefore introduces no volume factor.
-/

namespace MGAP4D.MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance groundStateNormedResponseAssemblerSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance groundStateNormedResponseAssemblerSpatialLinkNonempty
    (H : ℕ) :
    Nonempty (PeriodicHypercubicEvenSpatialSliceLink H) :=
  ⟨(⟨(0 : PeriodicHypercubicEvenVertex H), by
      simp [periodicHypercubicEvenOnPrimaryReflectionPlane]⟩,
    ⟨(1 : PeriodicHypercubicAxis), by norm_num⟩)⟩

/-- Any normed physical response decomposition with local profile ell and
source response matrix K feeds directly into the volume-uniform six-spatial
Schur coercivity receiver. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStage_normedResponse_global_energy_coercive_uniform
    {E : Type*}
    [NormedAddCommGroup E]
    (N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 1 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (H : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta)
    (state local : PeriodicHypercubicEvenSpatialSliceLink H → E)
    (response :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → E)
    (hDecomp : ∀ target,
      state target = local target + ∑ source, response target source)
    (hLocal : ∀ target,
      ‖local target‖ ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile
          H N hN beta hbeta f target)
    (hResponse : ∀ target source,
      ‖response target source‖ ≤
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
          H N hN beta hbeta A).influence target source * ‖state source‖) :
    (1 / 6 : ℝ) *
        ((1 -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureUniformBidirectionalSchurCoefficient
            s beta) ^ 2 *
          ∑ e : PeriodicHypercubicEvenSpatialSliceLink H, ‖state e‖ ^ 2) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSixSpatialResidualEnergy
        H N hN beta hbeta f := by
  have hOneSided : ∀ target,
      ‖state target‖ ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile
            H N hN beta hbeta f target +
          ∑ source,
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
              H N hN beta hbeta A).influence target source *
              ‖state source‖ := by
    exact
      FiniteNormedResponseOneSidedProfile.norm_profile_oneSided
        (fun target source =>
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
            H N hN beta hbeta A).influence target source)
        state local response
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile
          H N hN beta hbeta f)
        hDecomp hLocal hResponse
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialSweepStageProfile_oneSided_global_energy_coercive_uniform
      N hN s hs beta hbeta hcut H A f
      (fun e => ‖state e‖)
      (fun e => norm_nonneg _)
      hOneSided

end

end MGAP4D.MathlibAnalytic
