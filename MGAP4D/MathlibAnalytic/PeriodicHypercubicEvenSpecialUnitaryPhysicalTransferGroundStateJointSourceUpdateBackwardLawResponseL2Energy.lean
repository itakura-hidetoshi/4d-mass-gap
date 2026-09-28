import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceUpdateBackwardLawResponseTransposed
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourcePairCanonicalTargetLawResponseL2
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceUpdateBackwardDirectVarianceJointResidual
import Mathlib.Tactic

/-!
# Exact L2 energy of the backward source-law response

PR #4876 identifies one current-value backward source-law response pointwise
with the negative canonical target-law response after transposing the geometric
source/target roles.

The target heat-bath old/new joint law is already known to be exactly the
pushforward of two conditionally iid target-fiber samples.  The iid-pair law
is invariant under swapping those two samples.  Combining these exact law
identities with PR #4876 gives

  integral_(target heat-bath joint)
    ofReal(BackwardLawResponse^2)
  =
  ofReal ||transposed CanonicalTargetLawResponseL2||^2.

Thus the backward law-response term lands exactly on the existing
source-specific response L2 carrier, with geometric matrix orientation
K(source,target).  No response-symmetry assumption, comparison coefficient,
factor two, or finite-cardinality factor is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance backwardLawResponseL2EnergySpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance backwardLawResponseL2EnergySpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance backwardLawResponseL2EnergySpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance backwardLawResponseL2EnergySpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance backwardLawResponseL2EnergySpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance backwardLawResponseL2EnergySpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- On an iid target-fiber pair, the backward response of the corresponding
two complete configurations is the negative transposed canonical response
evaluated after swapping the two iid target values. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardLawResponse_currentValue_independentPairConfiguration_eq_neg_transposedResponseOnCarrier_swap_of_bounded
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : source ≠ target)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (Matrix.specialUnitaryGroup (Fin N) ℂ ×
          Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardLawResponse
        H N hN beta hbeta source F C C distinguishedSource
        (C distinguishedSource) (C source)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairConfigurationMap
          H N target z) =
      -periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseOnCarrier
        H N hN beta hbeta source target F C C distinguishedSource
        (C distinguishedSource) (C target) 0
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairBackgroundSwap
          H N z) := by
  let A :=
    Function.update z.1 target z.2.1
  have hPoint :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardLawResponse_currentValue_targetUpdate_eq_neg_transposedCanonicalTargetLawResponse_of_bounded
      H N hN beta hbeta C A distinguishedSource source target hne
      F hF bound hbound z.2.2
  simpa [
    A,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairConfigurationMap,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairBackgroundSwap,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseOnCarrier,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponse,
    hne] using hPoint

/-- Exact energy identity: the backward source-law response on the actual
target heat-bath joint carrier is the squared norm of the already-existing
transposed canonical response L2 vector. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardLawResponse_currentValue_heatBathJoint_lintegral_eq_transposedResponseL2_norm_sq_ofReal_of_bounded
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource source target :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : source ≠ target)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (∫⁻ CD,
      ENNReal.ofReal
        ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardLawResponse
          H N hN beta hbeta source F C C distinguishedSource
          (C distinguishedSource) (C source) CD) ^ 2)
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathJointMeasure
        H N hN beta hbeta C target distinguishedSource target
        (C distinguishedSource) (C target)) =
      ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
            H N hN beta hbeta C distinguishedSource target source
            (C distinguishedSource) (C target)
            F hF bound hbound C 0‖ ^ 2) := by
  let ν :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairBackgroundMeasure
      H N hN beta hbeta C target distinguishedSource target
      (C distinguishedSource) (C target)
  let J :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathJointMeasure
      H N hN beta hbeta C target distinguishedSource target
      (C distinguishedSource) (C target)
  let pairMap :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairConfigurationMap
      H N target
  let swapIn :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairBackgroundSwap
      H N
  let backward :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardLawResponse
      H N hN beta hbeta source F C C distinguishedSource
      (C distinguishedSource) (C source)
  let response :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseOnCarrier
      H N hN beta hbeta source target F C C distinguishedSource
      (C distinguishedSource) (C target) 0
  let L :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
      H N hN beta hbeta C distinguishedSource target source
      (C distinguishedSource) (C target)
      F hF bound hbound C 0
  have hMean :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectMean_stronglyMeasurable
      H N hN beta hbeta source F hF C C distinguishedSource
      (C distinguishedSource) (C source)
  have hLocal :
      StronglyMeasurable
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalLocalMean
          H N hN beta hbeta source F C C distinguishedSource
          (C distinguishedSource) (C source)) := by
    have hDiag :=
      hMean.comp_measurable (measurable_id.prodMk measurable_id)
    simpa [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectMean,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateDiagonalLocalMean] using hDiag
  have hBackward : StronglyMeasurable backward := by
    dsimp [backward]
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardLawResponse
    exact hMean.sub (hLocal.comp_measurable measurable_fst)
  let Phi :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ≥0∞ :=
    fun CD => ENNReal.ofReal ((backward CD) ^ 2)
  have hPhi : Measurable Phi := by
    exact ENNReal.continuous_ofReal.measurable.comp
      (hBackward.measurable.pow_const 2)
  have hPairMap : Measurable pairMap :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairConfigurationMap_measurable
      H N target
  have hJ :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairConfigurationMeasure
          H N hN beta hbeta C target distinguishedSource target
          (C distinguishedSource) (C target) =
        J := by
    simpa [J] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairConfigurationMeasure_eq_heatBathJointMeasure
        H N hN beta hbeta C target distinguishedSource target
        (C distinguishedSource) (C target)
  have hToPair :
      (∫⁻ CD, Phi CD ∂J) =
        ∫⁻ z, Phi (pairMap z) ∂ν := by
    rw [← hJ]
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairConfigurationMeasure
    simpa [ν, pairMap] using
      (MeasureTheory.lintegral_map hPhi hPairMap)
  have hPoint :
      ∀ z,
        Phi (pairMap z) =
          ENNReal.ofReal ((response (swapIn z)) ^ 2) := by
    intro z
    have hz :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardLawResponse_currentValue_independentPairConfiguration_eq_neg_transposedResponseOnCarrier_swap_of_bounded
        H N hN beta hbeta C distinguishedSource source target hne
        F hF bound hbound z
    dsimp [Phi, backward, pairMap, response, swapIn]
    rw [hz]
    ring_nf
  have hPairResponse :
      (∫⁻ z, Phi (pairMap z) ∂ν) =
        ∫⁻ z, ENNReal.ofReal ((response (swapIn z)) ^ 2) ∂ν := by
    apply lintegral_congr
    exact hPoint
  have hResponseStrong :
      StronglyMeasurable response := by
    simpa [response] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseOnCarrier_stronglyMeasurable
        H N hN beta hbeta C distinguishedSource target source
        (C distinguishedSource) (C target)
        F hF C 0
  let Psi :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (Matrix.specialUnitaryGroup (Fin N) ℂ ×
          Matrix.specialUnitaryGroup (Fin N) ℂ)) → ℝ≥0∞ :=
    fun z => ENNReal.ofReal ((response z) ^ 2)
  have hPsi : Measurable Psi := by
    exact ENNReal.continuous_ofReal.measurable.comp
      (hResponseStrong.measurable.pow_const 2)
  have hSwapMeas : Measurable swapIn := by
    simpa [swapIn] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairBackgroundSwap_measurable
        H N
  have hSwapLaw : Measure.map swapIn ν = ν := by
    simpa [
      ν,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairBackgroundMeasure] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairBackgroundMeasure_map_swap
        H N hN beta hbeta C target distinguishedSource target
        (C distinguishedSource) (C target)
  have hSwapIntegral :
      (∫⁻ z, ENNReal.ofReal ((response (swapIn z)) ^ 2) ∂ν) =
        ∫⁻ z, ENNReal.ofReal ((response z) ^ 2) ∂ν := by
    have hMap := MeasureTheory.lintegral_map hPsi hSwapMeas
    rw [hSwapLaw] at hMap
    simpa [Psi] using hMap.symm
  have hMem :
      MemLp response 2 ν := by
    simpa [
      response, ν,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairBackgroundMeasure] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseOnCarrier_memLp_two_of_bounded
        H N hN beta hbeta C distinguishedSource target source
        (C distinguishedSource) (C target)
        F hF bound hbound C 0
  have hSqInt : Integrable (fun z => (response z) ^ 2) ν := by
    simpa only [Pi.pow_apply] using hMem.integrable_sq
  have hOfReal :
      (∫⁻ z, ENNReal.ofReal ((response z) ^ 2) ∂ν) =
        ENNReal.ofReal (∫ z, (response z) ^ 2 ∂ν) :=
    (ofReal_integral_eq_lintegral_ofReal hSqInt
      (ae_of_all ν fun z => sq_nonneg (response z))).symm
  have hRep :
      (fun z => L z) =ᵐ[ν] response := by
    simpa [
      L, response, ν,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceIndependentPairBackgroundMeasure,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkIndependentPairBackgroundMeasure] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2_coeFn
        H N hN beta hbeta C distinguishedSource target source
        (C distinguishedSource) (C target)
        F hF bound hbound C 0
  have hNorm :
      ‖L‖ ^ 2 = ∫ z, (response z) ^ 2 ∂ν := by
    rw [realL2_norm_sq_eq_integral_norm_sq]
    apply integral_congr_ae
    filter_upwards [hRep] with z hz
    rw [hz]
    simp [Real.norm_eq_abs, sq_abs]
  calc
    (∫⁻ CD, ENNReal.ofReal ((backward CD) ^ 2) ∂J) =
        ∫⁻ CD, Phi CD ∂J := by rfl
    _ = ∫⁻ z, Phi (pairMap z) ∂ν := hToPair
    _ = ∫⁻ z, ENNReal.ofReal ((response (swapIn z)) ^ 2) ∂ν :=
      hPairResponse
    _ = ∫⁻ z, ENNReal.ofReal ((response z) ^ 2) ∂ν :=
      hSwapIntegral
    _ = ENNReal.ofReal (∫ z, (response z) ^ 2 ∂ν) := hOfReal
    _ = ENNReal.ofReal (‖L‖ ^ 2) := by rw [← hNorm]
    _ =
      ENNReal.ofReal
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourcePairCanonicalTargetLawResponseL2
            H N hN beta hbeta C distinguishedSource target source
            (C distinguishedSource) (C target)
            F hF bound hbound C 0‖ ^ 2) := by
      rfl

end

end MGAP4D.MathlibAnalytic
