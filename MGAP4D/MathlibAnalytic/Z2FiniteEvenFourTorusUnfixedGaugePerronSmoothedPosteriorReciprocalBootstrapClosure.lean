import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugePerronSmoothedPosteriorCanonicalNonstrictResponse
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugePerronSmoothedPosteriorRecursiveInfluenceRows
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The non-strict reciprocal response gives the exact smoothed-residual
four-point cross-ratio without assuming a strict posterior Dobrushin matrix. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidual_crossRatio_of_reciprocalKernel
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (A C : FiniteEvenFourTorusZ2SliceConfiguration H)
    (target source : FiniteEvenFourTorusSpatialLink H)
    (hNe : target ≠ source)
    (hAgree : FiniteProductAgreeOff A C source)
    (K :
      FiniteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalKernelCertificate
        H β energyIdentity energyNontrivial hβ hEnergy) :
    FinitePositiveWeightSingleSiteCrossRatioBound
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidual
        H β energyIdentity energyNontrivial hβ.le hEnergy.le)
      A C target
      (1 + finiteZ2CrossingLikelihoodRatio
        (z2WilsonTemporalCrossingRate
          β energyIdentity energyNontrivial) *
        K.responseError target source) := by
  apply
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidual_crossRatio_of_sourceTiltExpectation
      H β energyIdentity energyNontrivial hβ hEnergy
      A C target source hNe hAgree
  intro g h
  let rightWeight :=
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
      H β energyIdentity energyNontrivial hβ.le hEnergy.le
      (Function.update A target g)
  let sourceTilt :=
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidualSourceTilt
      H β energyIdentity energyNontrivial A source (C source)
  have hDiscrepancy :=
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidualSourceTiltExpectation_difference_abs_le_reciprocalKernel
      H β energyIdentity energyNontrivial hβ hEnergy
      A target source g h (C source) K
  have hDiscrepancyBound :
      |finitePositiveWeightGlobalExpectation
            (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
              H β energyIdentity energyNontrivial hβ.le hEnergy.le
              (Function.update A target h)) sourceTilt -
          finitePositiveWeightGlobalExpectation rightWeight sourceTilt| ≤
        K.responseError target source := by
    rw [←
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidualSourceTiltExpectation_eq_globalExpectation,
      ←
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidualSourceTiltExpectation_eq_globalExpectation]
    exact hDiscrepancy
  have hOneSided :=
    finitePositiveWeightGlobalExpectation_le_one_add_error_div_lower_mul
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
        H β energyIdentity energyNontrivial hβ.le hEnergy.le
        (Function.update A target h))
      rightWeight
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight_pos
        H β energyIdentity energyNontrivial hβ hEnergy
        (Function.update A target g))
      sourceTilt
      (finiteZ2CrossingLikelihoodRatio
        (z2WilsonTemporalCrossingRate
          β energyIdentity energyNontrivial))⁻¹
      (K.responseError target source)
      (inv_pos.mpr (finiteZ2CrossingLikelihoodRatio_pos
        (z2WilsonTemporalCrossingRate_pos hβ hEnergy).le
        (z2WilsonTemporalCrossingRate_lt_one hβ hEnergy)))
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTilt_ratio_inv_le
        H β energyIdentity energyNontrivial hβ hEnergy
        A source (C source))
      (K.responseError_nonneg target source)
      hDiscrepancyBound
  rw [
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidualSourceTiltExpectation_eq_globalExpectation,
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidualSourceTiltExpectation_eq_globalExpectation]
  simpa [rightWeight, sourceTilt, div_eq_mul_inv, mul_comm, mul_left_comm,
    mul_assoc] using hOneSided

/-- The reciprocal response compiles with the two exact local half-actions into
an explicit posterior cross-ratio radius. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight_crossRatio_of_reciprocalKernel
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (environment A C : FiniteEvenFourTorusZ2SliceConfiguration H)
    (target source : FiniteEvenFourTorusSpatialLink H)
    (hNe : target ≠ source)
    (hAgree : FiniteProductAgreeOff A C source)
    (K :
      FiniteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalKernelCertificate
        H β energyIdentity energyNontrivial hβ hEnergy) :
    FinitePositiveWeightSingleSiteCrossRatioBound
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
        H β energyIdentity energyNontrivial hβ.le hEnergy.le environment)
      A C target
      (Real.exp
        (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveCrossRatioRadius
          H β energyIdentity energyNontrivial target source
          (K.responseError target source))) := by
  have hResidualRaw :=
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidual_crossRatio_of_reciprocalKernel
      H β energyIdentity energyNontrivial hβ hEnergy
      A C target source hNe hAgree K
  have hResidual :
      FinitePositiveWeightSingleSiteCrossRatioBound
        (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidual
          H β energyIdentity energyNontrivial hβ.le hEnergy.le)
        A C target
        (Real.exp
          (Real.log
            (1 +
              finiteZ2CrossingLikelihoodRatio
                  (z2WilsonTemporalCrossingRate
                    β energyIdentity energyNontrivial) *
                K.responseError target source))) := by
    rw [←
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedRecursiveResidualCoefficient_eq_exp_log
        H β energyIdentity energyNontrivial hβ hEnergy
        (K.responseError target source)
        (K.responseError_nonneg target source)]
    exact hResidualRaw
  have hCombined :=
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight_crossRatio_of_residual
      H β energyIdentity energyNontrivial hβ hEnergy
      environment A C target source hNe hAgree
      (Real.exp
        (Real.log
          (1 +
            finiteZ2CrossingLikelihoodRatio
                (z2WilsonTemporalCrossingRate
                  β energyIdentity energyNontrivial) *
              K.responseError target source)))
      (le_of_lt (Real.exp_pos _)) hResidual
  let localRadius :=
    finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalCrossRatioRadius
      H β energyIdentity energyNontrivial target source
  let residualRadius :=
    Real.log
      (1 +
        finiteZ2CrossingLikelihoodRatio
            (z2WilsonTemporalCrossingRate
              β energyIdentity energyNontrivial) *
          K.responseError target source)
  have hExp :
      Real.exp
          (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveCrossRatioRadius
            H β energyIdentity energyNontrivial target source
            (K.responseError target source)) =
        Real.exp localRadius *
          (Real.exp localRadius * Real.exp residualRadius) := by
    unfold
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveCrossRatioRadius
    change Real.exp (2 * localRadius + residualRadius) = _
    rw [show 2 * localRadius + residualRadius =
      localRadius + (localRadius + residualRadius) by ring]
    simp only [Real.exp_add]
  rw [hExp]
  simpa [localRadius, residualRadius] using hCombined

/-- Reciprocal posterior radius with exact zero diagonal. -/
noncomputable def
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalInfluenceRadius
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (K :
      FiniteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalKernelCertificate
        H β energyIdentity energyNontrivial hβ hEnergy)
    (target source : FiniteEvenFourTorusSpatialLink H) : ℝ :=
  if target = source then 0 else
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveCrossRatioRadius
      H β energyIdentity energyNontrivial target source
      (K.responseError target source)

/-- Reciprocal posterior radius is nonnegative. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalInfluenceRadius_nonneg
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (K :
      FiniteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalKernelCertificate
        H β energyIdentity energyNontrivial hβ hEnergy)
    (target source : FiniteEvenFourTorusSpatialLink H) :
    0 ≤ finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalInfluenceRadius
      H β energyIdentity energyNontrivial hβ hEnergy K target source := by
  by_cases hEq : target = source
  · simp [
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalInfluenceRadius,
      hEq]
  · rw [
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalInfluenceRadius,
      if_neg hEq]
    exact
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveCrossRatioRadius_nonneg
        H β energyIdentity energyNontrivial hβ hEnergy
        target source (K.responseError target source)
        (K.responseError_nonneg target source)

/-- Cross-ratio entry data generated from the canonical non-strict reciprocal
response. -/
noncomputable def
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalInfluenceEntryData
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H)
    (K :
      FiniteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalKernelCertificate
        H β energyIdentity energyNontrivial hβ hEnergy) :
    FinitePositiveWeightCrossRatioInfluenceEntryData
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
        H β energyIdentity energyNontrivial hβ.le hEnergy.le environment) :=
  { radius :=
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalInfluenceRadius
        H β energyIdentity energyNontrivial hβ hEnergy K
    radius_nonneg :=
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalInfluenceRadius_nonneg
        H β energyIdentity energyNontrivial hβ hEnergy K
    crossRatioBound := by
      intro target source A B hNe hAgree
      rw [
        finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalInfluenceRadius,
        if_neg hNe]
      exact
        finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight_crossRatio_of_reciprocalKernel
          H β energyIdentity energyNontrivial hβ hEnergy
          environment A B target source hNe hAgree K }

/-- Actual full-`L¹` reciprocal posterior influence entry. -/
noncomputable def
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalInfluence
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H)
    (K :
      FiniteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalKernelCertificate
        H β energyIdentity energyNontrivial hβ hEnergy)
    (target source : FiniteEvenFourTorusSpatialLink H) : ℝ :=
  finitePositiveWeightCrossRatioEntryInfluence
    (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalInfluenceEntryData
      H β energyIdentity energyNontrivial hβ hEnergy environment K)
    target source

/-- The concrete posterior conditional change is bounded by the reciprocal
influence entry. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorConditionalL1_le_reciprocalInfluence
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (environment A B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (K :
      FiniteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalKernelCertificate
        H β energyIdentity energyNontrivial hβ hEnergy)
    (target source : FiniteEvenFourTorusSpatialLink H)
    (hAgree : FiniteProductAgreeOff A B source) :
    finitePositiveWeightSingleSiteConditionalL1
        (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
          H β energyIdentity energyNontrivial hβ.le hEnergy.le environment)
        A B target ≤
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalInfluence
        H β energyIdentity energyNontrivial hβ hEnergy
        environment K target source := by
  exact
    finitePositiveWeightSingleSiteConditionalL1_le_crossRatioEntryInfluence
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
        H β energyIdentity energyNontrivial hβ.le hEnergy.le environment)
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight_pos
        H β energyIdentity energyNontrivial hβ hEnergy environment)
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalInfluenceEntryData
        H β energyIdentity energyNontrivial hβ hEnergy environment K)
      target source A B hAgree

/-- Pointwise decomposition into the two local half-action influences and the
non-strict reciprocal response residual. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalInfluence_le_local_add_response
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H)
    (K :
      FiniteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalKernelCertificate
        H β energyIdentity energyNontrivial hβ hEnergy)
    (target source : FiniteEvenFourTorusSpatialLink H) :
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalInfluence
        H β energyIdentity energyNontrivial hβ hEnergy
        environment K target source ≤
      2 *
          finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluence
            H β energyIdentity energyNontrivial target source +
        (if target = source then 0 else
          finiteZ2CrossingLikelihoodRatio
              (z2WilsonTemporalCrossingRate
                β energyIdentity energyNontrivial) *
            K.responseError target source) := by
  by_cases hEq : target = source
  · subst source
    simp [
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalInfluence,
      finitePositiveWeightCrossRatioEntryInfluence_diagonal,
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluence]
  · let localRadius :=
      finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalCrossRatioRadius
        H β energyIdentity energyNontrivial target source
    let ratio :=
      finiteZ2CrossingLikelihoodRatio
        (z2WilsonTemporalCrossingRate
          β energyIdentity energyNontrivial)
    let error := K.responseError target source
    have hLocal : 0 ≤ localRadius :=
      finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalCrossRatioRadius_nonneg
        H β energyIdentity energyNontrivial hβ.le hEnergy.le target source
    have hRatio : 0 ≤ ratio :=
      le_of_lt
        (finiteZ2CrossingLikelihoodRatio_pos
          (z2WilsonTemporalCrossingRate_pos hβ hEnergy).le
          (z2WilsonTemporalCrossingRate_lt_one hβ hEnergy))
    have hError : 0 ≤ error := K.responseError_nonneg target source
    have hProduct : 0 ≤ ratio * error := mul_nonneg hRatio hError
    have hResidualRadius : 0 ≤ Real.log (1 + ratio * error) :=
      Real.log_nonneg (by nlinarith)
    unfold
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalInfluence
    rw [finitePositiveWeightCrossRatioEntryInfluence_eq_transform]
    simp only [hEq, if_false]
    have hRadiusProjection :
        (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalInfluenceEntryData
          H β energyIdentity energyNontrivial hβ hEnergy environment K).radius
            target source =
          finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalInfluenceRadius
            H β energyIdentity energyNontrivial hβ hEnergy K target source := rfl
    rw [hRadiusProjection]
    simp only [
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalInfluenceRadius,
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluence,
      hEq, if_false]
    unfold
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveCrossRatioRadius
    change
      finitePositiveWeightCrossRatioInfluenceTransform
          (2 * localRadius + Real.log (1 + ratio * error)) ≤
        2 * finitePositiveWeightCrossRatioInfluenceTransform localRadius +
          ratio * error
    calc
      finitePositiveWeightCrossRatioInfluenceTransform
          (2 * localRadius + Real.log (1 + ratio * error)) ≤
        finitePositiveWeightCrossRatioInfluenceTransform (2 * localRadius) +
          finitePositiveWeightCrossRatioInfluenceTransform
            (Real.log (1 + ratio * error)) :=
        finitePositiveWeightCrossRatioInfluenceTransform_add_le
          (2 * localRadius) (Real.log (1 + ratio * error))
          (mul_nonneg (by norm_num) hLocal) hResidualRadius
      _ ≤
        2 * finitePositiveWeightCrossRatioInfluenceTransform localRadius +
          finitePositiveWeightCrossRatioInfluenceTransform
            (Real.log (1 + ratio * error)) := by
        exact add_le_add
          (finitePositiveWeightCrossRatioInfluenceTransform_two_mul_le
            localRadius hLocal)
          (le_refl _)
      _ ≤
        2 * finitePositiveWeightCrossRatioInfluenceTransform localRadius +
          ratio * error := by
        exact add_le_add (le_refl _)
          (finitePositiveWeightCrossRatioInfluenceTransform_log_one_add_le
            (ratio * error) hProduct)

/-- Reciprocal candidate row sum for one fixed posterior. -/
noncomputable def
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalInfluenceRowSum
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H)
    (K :
      FiniteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalKernelCertificate
        H β energyIdentity energyNontrivial hβ hEnergy)
    (target : FiniteEvenFourTorusSpatialLink H) : ℝ :=
  ∑ source : FiniteEvenFourTorusSpatialLink H,
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalInfluence
      H β energyIdentity energyNontrivial hβ hEnergy
      environment K target source

/-- The complete reciprocal candidate row is bounded by the exact local row
plus the source-summed reciprocal response row. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalInfluenceRowSum_le_local_add_response
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H)
    (K :
      FiniteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalKernelCertificate
        H β energyIdentity energyNontrivial hβ hEnergy)
    (target : FiniteEvenFourTorusSpatialLink H) :
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalInfluenceRowSum
        H β energyIdentity energyNontrivial hβ hEnergy
        environment K target ≤
      2 *
          finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluenceRowSum
            H β energyIdentity energyNontrivial target +
        finiteZ2CrossingLikelihoodRatio
            (z2WilsonTemporalCrossingRate
              β energyIdentity energyNontrivial) *
          K.responseRowCoefficient := by
  let ratio :=
    finiteZ2CrossingLikelihoodRatio
      (z2WilsonTemporalCrossingRate
        β energyIdentity energyNontrivial)
  have hRatio : 0 ≤ ratio :=
    le_of_lt
      (finiteZ2CrossingLikelihoodRatio_pos
        (z2WilsonTemporalCrossingRate_pos hβ hEnergy).le
        (z2WilsonTemporalCrossingRate_lt_one hβ hEnergy))
  unfold
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalInfluenceRowSum
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluenceRowSum
  calc
    (∑ source : FiniteEvenFourTorusSpatialLink H,
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalInfluence
        H β energyIdentity energyNontrivial hβ hEnergy
        environment K target source) ≤
      ∑ source : FiniteEvenFourTorusSpatialLink H,
        (2 *
            finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluence
              H β energyIdentity energyNontrivial target source +
          (if target = source then 0 else
            ratio * K.responseError target source)) := by
      apply Finset.sum_le_sum
      intro source _hSource
      exact
        finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalInfluence_le_local_add_response
          H β energyIdentity energyNontrivial hβ hEnergy
          environment K target source
    _ ≤
      ∑ source : FiniteEvenFourTorusSpatialLink H,
        (2 *
            finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluence
              H β energyIdentity energyNontrivial target source +
          ratio * K.responseError target source) := by
      apply Finset.sum_le_sum
      intro source _hSource
      by_cases hEq : target = source
      · subst source
        have hResponse : 0 ≤ ratio * K.responseError target target :=
          mul_nonneg hRatio (K.responseError_nonneg target target)
        simpa using hResponse
      · simp [hEq]
    _ = 2 *
          (∑ source : FiniteEvenFourTorusSpatialLink H,
            finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluence
              H β energyIdentity energyNontrivial target source) +
        ratio *
          (∑ source : FiniteEvenFourTorusSpatialLink H,
            K.responseError target source) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 2 *
          (∑ source : FiniteEvenFourTorusSpatialLink H,
            finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluence
              H β energyIdentity energyNontrivial target source) +
        ratio * K.responseRowCoefficient :=
      add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left
          (K.responseErrorRowSum_le target) hRatio)

/-- Final non-circular closure certificate.  Its strict coefficient is built
from an exact finite local row and the reciprocal canonical-matrix response;
no strict fiber matrix appears among its inputs. -/
structure
    FiniteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalClosureCertificate
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) where
  reciprocal :
    FiniteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalKernelCertificate
      H β energyIdentity energyNontrivial hβ hEnergy
  localCoefficient : ℝ
  localCoefficient_nonneg : 0 ≤ localCoefficient
  localRowSum_le :
    ∀ target : FiniteEvenFourTorusSpatialLink H,
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluenceRowSum
          H β energyIdentity energyNontrivial target ≤ localCoefficient
  coefficient_lt_one :
    2 * localCoefficient +
      finiteZ2CrossingLikelihoodRatio
          (z2WilsonTemporalCrossingRate
            β energyIdentity energyNontrivial) *
        reciprocal.responseRowCoefficient < 1

/-- Explicit final reciprocal closure coefficient. -/
noncomputable def
    FiniteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalClosureCertificate.coefficient
    {H : ℕ}
    {β energyIdentity energyNontrivial : ℝ}
    {hβ : 0 < β}
    {hEnergy : energyIdentity < energyNontrivial}
    (C :
      FiniteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalClosureCertificate
        H β energyIdentity energyNontrivial hβ hEnergy) : ℝ :=
  2 * C.localCoefficient +
    finiteZ2CrossingLikelihoodRatio
        (z2WilsonTemporalCrossingRate
          β energyIdentity energyNontrivial) *
      C.reciprocal.responseRowCoefficient

/-- The final reciprocal closure coefficient is nonnegative. -/
theorem
    FiniteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalClosureCertificate.coefficient_nonneg
    {H : ℕ}
    {β energyIdentity energyNontrivial : ℝ}
    {hβ : 0 < β}
    {hEnergy : energyIdentity < energyNontrivial}
    (C :
      FiniteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalClosureCertificate
        H β energyIdentity energyNontrivial hβ hEnergy) :
    0 ≤ C.coefficient := by
  unfold
    FiniteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalClosureCertificate.coefficient
  exact add_nonneg
    (mul_nonneg (by norm_num) C.localCoefficient_nonneg)
    (mul_nonneg
      (le_of_lt
        (finiteZ2CrossingLikelihoodRatio_pos
          (z2WilsonTemporalCrossingRate_pos hβ hEnergy).le
          (z2WilsonTemporalCrossingRate_lt_one hβ hEnergy)))
      C.reciprocal.responseRowCoefficient_nonneg)

/-- Every reciprocal candidate row is bounded by the final strict coefficient. -/
theorem
    FiniteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalClosureCertificate.rowSum_le_coefficient
    {H : ℕ}
    {β energyIdentity energyNontrivial : ℝ}
    {hβ : 0 < β}
    {hEnergy : energyIdentity < energyNontrivial}
    (C :
      FiniteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalClosureCertificate
        H β energyIdentity energyNontrivial hβ hEnergy)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H)
    (target : FiniteEvenFourTorusSpatialLink H) :
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalInfluenceRowSum
        H β energyIdentity energyNontrivial hβ hEnergy
        environment C.reciprocal target ≤ C.coefficient := by
  have hRaw :=
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalInfluenceRowSum_le_local_add_response
      H β energyIdentity energyNontrivial hβ hEnergy
      environment C.reciprocal target
  have hRatio :
      0 ≤ finiteZ2CrossingLikelihoodRatio
        (z2WilsonTemporalCrossingRate
          β energyIdentity energyNontrivial) :=
    le_of_lt
      (finiteZ2CrossingLikelihoodRatio_pos
        (z2WilsonTemporalCrossingRate_pos hβ hEnergy).le
        (z2WilsonTemporalCrossingRate_lt_one hβ hEnergy))
  exact hRaw.trans
    (add_le_add
      (mul_le_mul_of_nonneg_left
        (C.localRowSum_le target) (by norm_num))
      (le_refl _))

/-- The non-circular reciprocal closure produces the actual strict Dobrushin
matrix consumed by the existing finite-weight spectral and gap theorems. -/
noncomputable def
    FiniteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalClosureCertificate.toDobrushinData
    {H : ℕ}
    {β energyIdentity energyNontrivial : ℝ}
    {hβ : 0 < β}
    {hEnergy : energyIdentity < energyNontrivial}
    (C :
      FiniteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalClosureCertificate
        H β energyIdentity energyNontrivial hβ hEnergy)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H) :
    FinitePositiveWeightDobrushinL1MatrixData
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
        H β energyIdentity energyNontrivial hβ.le hEnergy.le environment) :=
  (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalInfluenceEntryData
    H β energyIdentity energyNontrivial hβ hEnergy environment C.reciprocal).toDobrushinL1MatrixData
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight_pos
        H β energyIdentity energyNontrivial hβ hEnergy environment)
      C.coefficient C.coefficient_nonneg
      (by
        intro target
        simpa [
          finitePositiveWeightCrossRatioEntryRowSum,
          finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalInfluenceRowSum,
          finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorReciprocalInfluence] using
          C.rowSum_le_coefficient environment target)
      C.coefficient_lt_one

end

end MathlibAnalytic
end MGAP4D
