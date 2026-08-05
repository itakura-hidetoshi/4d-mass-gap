import MGAP4D.MathlibAnalytic.FinitePositiveWeightCrossRatioInfluenceTransform
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugePerronSmoothedPosteriorRecursiveInfluence
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The one-half-weight local influence row entering the recursive hidden
posterior.  The complete posterior contains two copies of this local radius. -/
noncomputable def
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluence
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (target source : FiniteEvenFourTorusSpatialLink H) : ℝ :=
  if target = source then 0 else
    finitePositiveWeightCrossRatioInfluenceTransform
      (finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalCrossRatioRadius
        H β energyIdentity energyNontrivial target source)

/-- Exact spatial-source support of one local hidden-posterior row. -/
noncomputable def
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalSourceNeighborhood
    (H : ℕ)
    (target : FiniteEvenFourTorusSpatialLink H) :
    Finset (FiniteEvenFourTorusSpatialLink H) := by
  classical
  exact Finset.univ.filter fun source =>
    Sum.inr source ∈
      finiteEvenFourTorusZ2LowerSpatialInteractionNeighborhood H target

@[simp] theorem
    finiteEvenFourTorusZ2_mem_perronSmoothedPosteriorLocalSourceNeighborhood
    (H : ℕ)
    (target source : FiniteEvenFourTorusSpatialLink H) :
    source ∈
        finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalSourceNeighborhood
          H target ↔
      Sum.inr source ∈
        finiteEvenFourTorusZ2LowerSpatialInteractionNeighborhood H target := by
  classical
  simp [
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalSourceNeighborhood]

/-- One local influence entry is nonnegative. -/
theorem
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluence_nonneg
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (target source : FiniteEvenFourTorusSpatialLink H) :
    0 ≤
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluence
        H β energyIdentity energyNontrivial target source := by
  by_cases hEq : target = source
  · simp [
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluence,
      hEq]
  · rw [
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluence,
      if_neg hEq]
    exact finitePositiveWeightCrossRatioInfluenceTransform_nonneg _
      (finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalCrossRatioRadius_nonneg
        H β energyIdentity energyNontrivial hβ hEnergy target source)

/-- The local influence row has exact finite incidence support. -/
theorem
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluence_eq_zero_of_not_mem
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (target source : FiniteEvenFourTorusSpatialLink H)
    (hSource :
      source ∉
        finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalSourceNeighborhood
          H target) :
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluence
        H β energyIdentity energyNontrivial target source = 0 := by
  have hAugmented :
      Sum.inr source ∉
        finiteEvenFourTorusZ2LowerSpatialInteractionNeighborhood H target := by
    simpa using hSource
  unfold
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluence
    finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalCrossRatioRadius
    finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalMixedActionRadius
    finiteEvenFourTorusZ2LowerSpatialUniformMixedActionRadius
  by_cases hEq : target = source
  · simp [hEq]
  · simp [hEq, hAugmented,
      finitePositiveWeightCrossRatioInfluenceTransform_zero]

/-- Candidate row sum of one local half-weight factor. -/
noncomputable def
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluenceRowSum
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (target : FiniteEvenFourTorusSpatialLink H) : ℝ :=
  ∑ source : FiniteEvenFourTorusSpatialLink H,
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluence
      H β energyIdentity energyNontrivial target source

/-- The one-factor local row is exactly supported on the finite shared-
plaquette source neighborhood. -/
theorem
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluenceRowSum_eq_support_sum
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (target : FiniteEvenFourTorusSpatialLink H) :
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluenceRowSum
        H β energyIdentity energyNontrivial target =
      ∑ source ∈
        finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalSourceNeighborhood
          H target,
        finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluence
          H β energyIdentity energyNontrivial target source := by
  classical
  unfold
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluenceRowSum
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro source _hSource hNotMem
  exact
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluence_eq_zero_of_not_mem
      H β energyIdentity energyNontrivial target source hNotMem

/-- Off-diagonal source-summed recursive response error. -/
noncomputable def
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveErrorRowSum
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (C :
      FiniteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveInfluenceCertificate
        H β energyIdentity energyNontrivial hβ hEnergy)
    (target : FiniteEvenFourTorusSpatialLink H) : ℝ :=
  ∑ source : FiniteEvenFourTorusSpatialLink H,
    if target = source then 0 else C.errorBound target source

/-- The recursive error row is nonnegative. -/
theorem
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveErrorRowSum_nonneg
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (C :
      FiniteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveInfluenceCertificate
        H β energyIdentity energyNontrivial hβ hEnergy)
    (target : FiniteEvenFourTorusSpatialLink H) :
    0 ≤
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveErrorRowSum
        H β energyIdentity energyNontrivial hβ hEnergy C target := by
  unfold
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveErrorRowSum
  exact Finset.sum_nonneg fun source _hSource => by
    split
    · exact le_rfl
    · exact C.errorBound_nonneg target source

/-- Pointwise decomposition of the actual recursive hidden-posterior influence
into two exact local half-weight entries and a linear recursive residual. -/
theorem
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveInfluence_le_local_add_residual
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H)
    (C :
      FiniteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveInfluenceCertificate
        H β energyIdentity energyNontrivial hβ hEnergy)
    (target source : FiniteEvenFourTorusSpatialLink H) :
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveInfluence
        H β energyIdentity energyNontrivial hβ hEnergy
        environment C target source ≤
      2 *
          finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluence
            H β energyIdentity energyNontrivial target source +
        (if target = source then 0 else
          finiteZ2CrossingLikelihoodRatio
              (z2WilsonTemporalCrossingRate
                β energyIdentity energyNontrivial) *
            C.errorBound target source) := by
  by_cases hEq : target = source
  · subst source
    simp [
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveInfluence,
      finitePositiveWeightCrossRatioEntryInfluence_diagonal,
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluence]
  · let localRadius :=
      finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalCrossRatioRadius
        H β energyIdentity energyNontrivial target source
    let ratio :=
      finiteZ2CrossingLikelihoodRatio
        (z2WilsonTemporalCrossingRate
          β energyIdentity energyNontrivial)
    let error := C.errorBound target source
    have hLocal : 0 ≤ localRadius := by
      exact
        finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalCrossRatioRadius_nonneg
          H β energyIdentity energyNontrivial hβ.le hEnergy.le target source
    have hRatio : 0 ≤ ratio := by
      exact le_of_lt
        (finiteZ2CrossingLikelihoodRatio_pos
          (z2WilsonTemporalCrossingRate_pos hβ hEnergy).le
          (z2WilsonTemporalCrossingRate_lt_one hβ hEnergy))
    have hError : 0 ≤ error := C.errorBound_nonneg target source
    have hProduct : 0 ≤ ratio * error := mul_nonneg hRatio hError
    have hResidualRadius : 0 ≤ Real.log (1 + ratio * error) := by
      exact Real.log_nonneg (by nlinarith)
    unfold
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveInfluence
    rw [finitePositiveWeightCrossRatioEntryInfluence_eq_transform]
    simp only [hEq, if_false]
    have hRadiusProjection :
        (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveInfluenceEntryData
          H β energyIdentity energyNontrivial hβ hEnergy environment C).radius
            target source =
          finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveInfluenceRadius
            H β energyIdentity energyNontrivial hβ hEnergy C target source := by
      rfl
    rw [hRadiusProjection]
    simp only [
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveInfluenceRadius,
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

/-- The complete actual recursive influence row is bounded by twice the exact
finite-incidence local row plus the crossing likelihood ratio times the
source-summed recursive error row. -/
theorem
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveInfluenceRowSum_le_local_add_error
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H)
    (C :
      FiniteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveInfluenceCertificate
        H β energyIdentity energyNontrivial hβ hEnergy)
    (target : FiniteEvenFourTorusSpatialLink H) :
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveInfluenceRowSum
        H β energyIdentity energyNontrivial hβ hEnergy
        environment C target ≤
      2 *
          finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluenceRowSum
            H β energyIdentity energyNontrivial target +
        finiteZ2CrossingLikelihoodRatio
            (z2WilsonTemporalCrossingRate
              β energyIdentity energyNontrivial) *
          finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveErrorRowSum
            H β energyIdentity energyNontrivial hβ hEnergy C target := by
  let ratio :=
    finiteZ2CrossingLikelihoodRatio
      (z2WilsonTemporalCrossingRate
        β energyIdentity energyNontrivial)
  unfold
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveInfluenceRowSum
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluenceRowSum
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveErrorRowSum
  calc
    (∑ source : FiniteEvenFourTorusSpatialLink H,
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveInfluence
        H β energyIdentity energyNontrivial hβ hEnergy
        environment C target source) ≤
      ∑ source : FiniteEvenFourTorusSpatialLink H,
        (2 *
            finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluence
              H β energyIdentity energyNontrivial target source +
          (if target = source then 0 else
            ratio * C.errorBound target source)) := by
      apply Finset.sum_le_sum
      intro source _hSource
      exact
        finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveInfluence_le_local_add_residual
          H β energyIdentity energyNontrivial hβ hEnergy
          environment C target source
    _ =
      2 *
          (∑ source : FiniteEvenFourTorusSpatialLink H,
            finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluence
              H β energyIdentity energyNontrivial target source) +
        ratio *
          (∑ source : FiniteEvenFourTorusSpatialLink H,
            if target = source then 0 else C.errorBound target source) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      congr 1
      calc
        (∑ source : FiniteEvenFourTorusSpatialLink H,
            if target = source then 0 else
              ratio * C.errorBound target source) =
          ∑ source : FiniteEvenFourTorusSpatialLink H,
            ratio *
              (if target = source then 0 else C.errorBound target source) := by
          apply Finset.sum_congr rfl
          intro source _hSource
          by_cases hEq : target = source
          · simp [hEq]
          · simp [hEq]
        _ = ratio *
            (∑ source : FiniteEvenFourTorusSpatialLink H,
              if target = source then 0 else C.errorBound target source) := by
          rw [Finset.mul_sum]

/-- A source-summed row certificate separates the exact local incidence row
from the genuinely recursive residual row.  It does not assume the desired
posterior Dobrushin matrix; it only packages quantitative bounds already
proved for a recursive influence certificate. -/
structure
    FiniteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveRowCertificate
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) where
  recursive :
    FiniteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveInfluenceCertificate
      H β energyIdentity energyNontrivial hβ hEnergy
  localCoefficient : ℝ
  errorCoefficient : ℝ
  localCoefficient_nonneg : 0 ≤ localCoefficient
  errorCoefficient_nonneg : 0 ≤ errorCoefficient
  localRowSum_le :
    ∀ target : FiniteEvenFourTorusSpatialLink H,
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluenceRowSum
          H β energyIdentity energyNontrivial target ≤ localCoefficient
  errorRowSum_le :
    ∀ target : FiniteEvenFourTorusSpatialLink H,
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveErrorRowSum
          H β energyIdentity energyNontrivial hβ hEnergy recursive target ≤
        errorCoefficient

/-- Explicit coefficient generated by local incidence and source-summed
recursive residual control. -/
noncomputable def
    FiniteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveRowCertificate.coefficient
    {H : ℕ}
    {β energyIdentity energyNontrivial : ℝ}
    {hβ : 0 < β}
    {hEnergy : energyIdentity < energyNontrivial}
    (R :
      FiniteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveRowCertificate
        H β energyIdentity energyNontrivial hβ hEnergy) : ℝ :=
  2 * R.localCoefficient +
    finiteZ2CrossingLikelihoodRatio
        (z2WilsonTemporalCrossingRate
          β energyIdentity energyNontrivial) *
      R.errorCoefficient

/-- The explicit recursive row coefficient is nonnegative. -/
theorem
    FiniteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveRowCertificate.coefficient_nonneg
    {H : ℕ}
    {β energyIdentity energyNontrivial : ℝ}
    {hβ : 0 < β}
    {hEnergy : energyIdentity < energyNontrivial}
    (R :
      FiniteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveRowCertificate
        H β energyIdentity energyNontrivial hβ hEnergy) :
    0 ≤ R.coefficient := by
  unfold
    FiniteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveRowCertificate.coefficient
  exact add_nonneg
    (mul_nonneg (by norm_num) R.localCoefficient_nonneg)
    (mul_nonneg
      (le_of_lt
        (finiteZ2CrossingLikelihoodRatio_pos
          (z2WilsonTemporalCrossingRate_pos hβ hEnergy).le
          (z2WilsonTemporalCrossingRate_lt_one hβ hEnergy)))
      R.errorCoefficient_nonneg)

/-- A source-summed recursive row certificate gives the uniform actual
posterior row bound. -/
theorem
    FiniteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveRowCertificate.rowSum_le_coefficient
    {H : ℕ}
    {β energyIdentity energyNontrivial : ℝ}
    {hβ : 0 < β}
    {hEnergy : energyIdentity < energyNontrivial}
    (R :
      FiniteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveRowCertificate
        H β energyIdentity energyNontrivial hβ hEnergy)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H)
    (target : FiniteEvenFourTorusSpatialLink H) :
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveInfluenceRowSum
        H β energyIdentity energyNontrivial hβ hEnergy
        environment R.recursive target ≤ R.coefficient := by
  have hRatio :
      0 ≤ finiteZ2CrossingLikelihoodRatio
        (z2WilsonTemporalCrossingRate
          β energyIdentity energyNontrivial) :=
    le_of_lt
      (finiteZ2CrossingLikelihoodRatio_pos
        (z2WilsonTemporalCrossingRate_pos hβ hEnergy).le
        (z2WilsonTemporalCrossingRate_lt_one hβ hEnergy))
  calc
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveInfluenceRowSum
        H β energyIdentity energyNontrivial hβ hEnergy
        environment R.recursive target ≤
      2 *
          finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluenceRowSum
            H β energyIdentity energyNontrivial target +
        finiteZ2CrossingLikelihoodRatio
            (z2WilsonTemporalCrossingRate
              β energyIdentity energyNontrivial) *
          finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveErrorRowSum
            H β energyIdentity energyNontrivial hβ hEnergy R.recursive target :=
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveInfluenceRowSum_le_local_add_error
        H β energyIdentity energyNontrivial hβ hEnergy
        environment R.recursive target
    _ ≤ 2 * R.localCoefficient +
        finiteZ2CrossingLikelihoodRatio
            (z2WilsonTemporalCrossingRate
              β energyIdentity energyNontrivial) * R.errorCoefficient :=
      add_le_add
        (mul_le_mul_of_nonneg_left
          (R.localRowSum_le target) (by norm_num))
        (mul_le_mul_of_nonneg_left
          (R.errorRowSum_le target) hRatio)
    _ = R.coefficient := rfl

/-- Once the explicit source-summed coefficient is strictly below one, the
actual fixed-environment hidden posterior obtains its Dobrushin matrix. -/
noncomputable def
    FiniteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveRowCertificate.toDobrushinData
    {H : ℕ}
    {β energyIdentity energyNontrivial : ℝ}
    {hβ : 0 < β}
    {hEnergy : energyIdentity < energyNontrivial}
    (R :
      FiniteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveRowCertificate
        H β energyIdentity energyNontrivial hβ hEnergy)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H)
    (hCoefficientLtOne : R.coefficient < 1) :
    FinitePositiveWeightDobrushinL1MatrixData
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
        H β energyIdentity energyNontrivial hβ.le hEnergy.le environment) :=
  finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveDobrushinData
    H β energyIdentity energyNontrivial hβ hEnergy
    environment R.recursive R.coefficient R.coefficient_nonneg
    (R.rowSum_le_coefficient environment) hCoefficientLtOne

end

end MathlibAnalytic
end MGAP4D
