import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairSweepStageResponseEnergy
import Mathlib.Tactic

/-!
# Charge the global response energy to the genuine six-spatial residual energy

PR #4847 provides a link-indexed family of actual bounded sweep-stage
representatives for which the vacuum-integrated response-amplitude energy is
bounded by

  rhoResp(s,beta) * ofReal(sum_e localProfile(e)^2).

The established six-spatial sweep identity gives

  (1/6) * sum_e localProfile(e)^2 <= E_6sp(f).

Therefore

  sum_e localProfile(e)^2 <= 6 * E_6sp(f),

and the complete response energy is charged to the genuine six-spatial
residual energy with only the fixed six-color factor.  No volume-dependent
factor is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

local instance sweepResponseResidualEnergySpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance sweepResponseResidualEnergySpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- For every bounded-core vector, choose the canonical sweep-stage
representatives so that the complete vacuum-integrated response-amplitude
energy is bounded by the genuine six-spatial residual energy. -/
theorem
    exists_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweep_linkIndexedRepresentatives_responseAmplitude_vacuum_lintegral_le_responseResidualCoefficient_mul_sixSpatialResidualEnergy_ofReal
    (N : ℕ) (hN : 0 < N)
    (s : ℝ) (hs : 8 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCutoff
          s hs)
    (H : ℕ)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta)
    (hf :
      f ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta) :
    ∃
      (F :
        PeriodicHypercubicEvenSpatialSliceLink H →
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
      (hF : ∀ e, StronglyMeasurable (F e))
      (bound : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
      (hbound : ∀ e z, ‖F e z‖ ≤ bound e),
      (∀ e,
        ∃ pre :
          List
            (PeriodicHypercubicEvenFixedSpatialColorLink H
              (periodicHypercubicEvenSpatialSliceLinkColor H e)),
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
              H N hN beta hbeta
              (F e) (hF e) (bound e) (hbound e) =
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
              H N hN beta hbeta
              (periodicHypercubicEvenSpatialSliceLinkColor H e) pre f) ∧
      (∫⁻ C,
        ENNReal.ofReal
          (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
            (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseAmplitudeMatrix
                H N hN beta hbeta C distinguishedSource
                (F target) (hF target) (bound target) (hbound target)
                source target) ^ 2)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabVacuumMeasure
          H N hN beta hbeta) ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualCoefficient
            s beta *
          ENNReal.ofReal
            (6 *
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSixSpatialResidualEnergy
                H N hN beta hbeta f) := by
  rcases
      exists_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweep_linkIndexedRepresentatives_responseAmplitude_vacuum_lintegral_le_responseResidualCoefficient_mul_localProfile_sq_sum_ofReal
        N hN s hs beta hbeta hcut H distinguishedSource f hf with
    ⟨F, hF, bound, hbound, hRep, hResponse⟩
  refine ⟨F, hF, bound, hbound, hRep, ?_⟩
  let S : ℝ :=
    ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile
        H N hN beta hbeta f e ^ 2
  let E : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSixSpatialResidualEnergy
      H N hN beta hbeta f
  have hProfile :
      (1 / 6 : ℝ) * S ≤ E := by
    simpa [S, E] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile_normalized_sq_sum_le_residualEnergy
        H N hN beta hbeta f
  have hSix : S ≤ 6 * E := by
    linarith
  have hENN :
      ENNReal.ofReal S ≤ ENNReal.ofReal (6 * E) :=
    ENNReal.ofReal_le_ofReal hSix
  exact hResponse.trans
    (mul_le_mul_right
      (by simpa [S, E] using hENN)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawFixedBackgroundResponseResidualCoefficient
        s beta))

end

end MGAP4D.MathlibAnalytic
