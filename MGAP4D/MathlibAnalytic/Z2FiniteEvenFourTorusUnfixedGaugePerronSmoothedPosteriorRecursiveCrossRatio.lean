import MGAP4D.MathlibAnalytic.FinitePositiveWeightCoordinatewiseFactorCrossRatio
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugePerronSmoothedResidualRecursiveResponse
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The coordinatewise normalized temporal-crossing factor in one fixed
hidden posterior. -/
def finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorCrossingFactor
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (environment hidden : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  finiteEvenFourTorusZ2NormalizedTemporalCrossingKernel
    H β energyIdentity energyNontrivial hidden environment

/-- The posterior crossing factor is exactly a product of independent hidden
one-coordinate factors. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorCrossingFactor_eq_coordinatewiseFactor
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorCrossingFactor
        H β energyIdentity energyNontrivial environment =
      finiteProductCoordinatewiseFactor
        (fun coordinate : FiniteEvenFourTorusSpatialLink H =>
          fun g : Z2Gauge =>
            finiteZ2NormalizedLocalKernel
              (z2WilsonTemporalCrossingRate
                β energyIdentity energyNontrivial)
              (boolEquivZ2Gauge.symm g)
              (boolEquivZ2Gauge.symm (environment coordinate))) := by
  funext hidden
  unfold
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorCrossingFactor
    finiteEvenFourTorusZ2NormalizedTemporalCrossingKernel
    finiteProductCoordinatewiseFactor
  rw [finiteZ2GaugeNormalizedProductKernel_apply]

/-- The complete normalized crossing factor cancels exactly from every hidden
four-point cross ratio. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorCrossingFactor_crossRatio_one
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (environment A C : FiniteEvenFourTorusZ2SliceConfiguration H)
    (target : FiniteEvenFourTorusSpatialLink H) :
    FinitePositiveWeightSingleSiteCrossRatioBound
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorCrossingFactor
        H β energyIdentity energyNontrivial environment)
      A C target 1 := by
  rw [
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorCrossingFactor_eq_coordinatewiseFactor]
  exact
    finiteProductCoordinatewiseFactor_singleSiteCrossRatio_one
      (fun coordinate : FiniteEvenFourTorusSpatialLink H =>
        fun g : Z2Gauge =>
          finiteZ2NormalizedLocalKernel
            (z2WilsonTemporalCrossingRate
              β energyIdentity energyNontrivial)
            (boolEquivZ2Gauge.symm g)
            (boolEquivZ2Gauge.symm (environment coordinate)))
      A C target

/-- At strict coupling every fixed posterior crossing factor is strictly
positive. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorCrossingFactor_pos
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (environment hidden : FiniteEvenFourTorusZ2SliceConfiguration H) :
    0 < finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorCrossingFactor
      H β energyIdentity energyNontrivial environment hidden := by
  unfold
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorCrossingFactor
    finiteEvenFourTorusZ2NormalizedTemporalCrossingKernel
  exact finiteZ2GaugeNormalizedProductKernel_pos
    (z2WilsonTemporalCrossingRate_pos hβ hEnergy).le
    (z2WilsonTemporalCrossingRate_lt_one hβ hEnergy)
    (FiniteEvenFourTorusSpatialLink H) hidden environment

/-- The spatial half-weight is the unscaled exponential of the extracted slice
half-action. -/
theorem finiteEvenFourTorusZ2SpatialHalfWeight_eq_perronSliceExponential
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ) :
    finiteEvenFourTorusZ2SpatialHalfWeight
        H β energyIdentity energyNontrivial =
      fun A : FiniteEvenFourTorusZ2SliceConfiguration H =>
        Real.exp
          (-β *
            finiteEvenFourTorusZ2UnfixedGaugePerronSliceSpatialHalfAction
              H energyIdentity energyNontrivial A) := by
  funext A
  unfold finiteEvenFourTorusZ2SpatialHalfWeight
    finiteEvenFourTorusZ2UnfixedGaugePerronSliceSpatialHalfAction
  congr 1
  ring

/-- The additional spatial half-weight contributes the same exact
shared-plaquette row as the extracted Perron local factor. -/
theorem finiteEvenFourTorusZ2SpatialHalfWeight_crossRatio
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A C : FiniteEvenFourTorusZ2SliceConfiguration H)
    (target source : FiniteEvenFourTorusSpatialLink H)
    (hNe : target ≠ source)
    (hAgree : FiniteProductAgreeOff A C source) :
    FinitePositiveWeightSingleSiteCrossRatioBound
      (finiteEvenFourTorusZ2SpatialHalfWeight
        H β energyIdentity energyNontrivial)
      A C target
      (Real.exp
        (finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalCrossRatioRadius
          H β energyIdentity energyNontrivial target source)) := by
  rw [finiteEvenFourTorusZ2SpatialHalfWeight_eq_perronSliceExponential]
  simpa [
    finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalCrossRatioRadius] using
    finitePositiveExponentialWeightSingleSiteCrossRatioBound_of_mixedAction
      (finiteEvenFourTorusZ2UnfixedGaugePerronSliceSpatialHalfAction
        H energyIdentity energyNontrivial)
      β hβ A C target
      (finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalMixedActionRadius
        H energyIdentity energyNontrivial target source)
      (finiteEvenFourTorusZ2UnfixedGaugePerronSliceSpatialHalfAction_uniform_mixedAction
        H energyIdentity energyNontrivial hEnergy A C target source hNe hAgree)

/-- Exact pointwise factorization of a fixed hidden posterior into the
coordinatewise crossing factor, the additional spatial half-weight, the
extracted local Perron factor, and the recursively smoothed residual. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight_eq_factorizedProduct
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
        H β energyIdentity energyNontrivial hβ hEnergy environment =
      finitePositiveWeightProduct
        (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorCrossingFactor
          H β energyIdentity energyNontrivial environment)
        (finitePositiveWeightProduct
          (finiteEvenFourTorusZ2SpatialHalfWeight
            H β energyIdentity energyNontrivial)
          (finitePositiveWeightProduct
            (finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalFactor
              H β energyIdentity energyNontrivial hβ hEnergy)
            (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidual
              H β energyIdentity energyNontrivial hβ hEnergy))) := by
  funext hidden
  unfold finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorCrossingFactor
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedHiddenWeight
    finitePositiveWeightProduct
  rw [
    finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_eq_localFactor_mul_smoothedResidual]

/-- A residual four-point coefficient combines with the two exact local
half-weight rows; the coordinatewise crossing kernel contributes exactly one. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight_crossRatio_of_residual
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (environment A C : FiniteEvenFourTorusZ2SliceConfiguration H)
    (target source : FiniteEvenFourTorusSpatialLink H)
    (hNe : target ≠ source)
    (hAgree : FiniteProductAgreeOff A C source)
    (residualRatio : ℝ)
    (hResidualRatio : 0 ≤ residualRatio)
    (hResidual :
      FinitePositiveWeightSingleSiteCrossRatioBound
        (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidual
          H β energyIdentity energyNontrivial hβ.le hEnergy.le)
        A C target residualRatio) :
    FinitePositiveWeightSingleSiteCrossRatioBound
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
        H β energyIdentity energyNontrivial hβ.le hEnergy.le environment)
      A C target
      (Real.exp
          (finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalCrossRatioRadius
            H β energyIdentity energyNontrivial target source) *
        (Real.exp
            (finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalCrossRatioRadius
              H β energyIdentity energyNontrivial target source) *
          residualRatio)) := by
  rw [
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight_eq_factorizedProduct]
  let localRadius :=
    finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalCrossRatioRadius
      H β energyIdentity energyNontrivial target source
  let localFactor :=
    finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalFactor
      H β energyIdentity energyNontrivial hβ.le hEnergy.le
  let residual :=
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidual
      H β energyIdentity energyNontrivial hβ.le hEnergy.le
  have hCrossing :
      FinitePositiveWeightSingleSiteCrossRatioBound
        (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorCrossingFactor
          H β energyIdentity energyNontrivial environment)
        A C target 1 :=
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorCrossingFactor_crossRatio_one
      H β energyIdentity energyNontrivial environment A C target
  have hSpatial :
      FinitePositiveWeightSingleSiteCrossRatioBound
        (finiteEvenFourTorusZ2SpatialHalfWeight
          H β energyIdentity energyNontrivial)
        A C target (Real.exp localRadius) := by
    simpa [localRadius] using
      finiteEvenFourTorusZ2SpatialHalfWeight_crossRatio
        H β energyIdentity energyNontrivial hβ.le hEnergy.le
        A C target source hNe hAgree
  have hLocal :
      FinitePositiveWeightSingleSiteCrossRatioBound
        localFactor A C target (Real.exp localRadius) := by
    simpa [localFactor, localRadius] using
      finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalFactor_crossRatio
        H β energyIdentity energyNontrivial hβ.le hEnergy.le
        A C target source hNe hAgree
  have hLocalNonneg : ∀ X, 0 ≤ localFactor X := by
    intro X
    exact le_of_lt
      (finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalFactor_pos
        H β energyIdentity energyNontrivial hβ.le hEnergy.le X)
  have hResidualNonneg : ∀ X, 0 ≤ residual X := by
    intro X
    exact le_of_lt
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidual_pos
        H β energyIdentity energyNontrivial hβ.le hEnergy.le X)
  have hLocalResidualNonneg :
      ∀ X, 0 ≤ finitePositiveWeightProduct localFactor residual X := by
    intro X
    change 0 ≤ localFactor X * residual X
    exact mul_nonneg (hLocalNonneg X) (hResidualNonneg X)
  have hHiddenNonneg :
      ∀ X, 0 ≤
        finitePositiveWeightProduct
          (finiteEvenFourTorusZ2SpatialHalfWeight
            H β energyIdentity energyNontrivial)
          (finitePositiveWeightProduct localFactor residual) X := by
    intro X
    change 0 ≤
      finiteEvenFourTorusZ2SpatialHalfWeight
          H β energyIdentity energyNontrivial X *
        (localFactor X * residual X)
    exact mul_nonneg
      (le_of_lt
        (finiteEvenFourTorusZ2SpatialHalfWeight_pos
          H β energyIdentity energyNontrivial X))
      (mul_nonneg (hLocalNonneg X) (hResidualNonneg X))
  have hLocalResidual :
      FinitePositiveWeightSingleSiteCrossRatioBound
        (finitePositiveWeightProduct localFactor residual)
        A C target (Real.exp localRadius * residualRatio) := by
    exact finitePositiveWeightProduct_singleSiteCrossRatioBound
      localFactor residual hLocalNonneg hResidualNonneg
      A C target (Real.exp localRadius) residualRatio
      (le_of_lt (Real.exp_pos _)) hResidualRatio hLocal hResidual
  have hHidden :
      FinitePositiveWeightSingleSiteCrossRatioBound
        (finitePositiveWeightProduct
          (finiteEvenFourTorusZ2SpatialHalfWeight
            H β energyIdentity energyNontrivial)
          (finitePositiveWeightProduct localFactor residual))
        A C target
        (Real.exp localRadius * (Real.exp localRadius * residualRatio)) := by
    exact finitePositiveWeightProduct_singleSiteCrossRatioBound
      (finiteEvenFourTorusZ2SpatialHalfWeight
        H β energyIdentity energyNontrivial)
      (finitePositiveWeightProduct localFactor residual)
      (fun X => le_of_lt
        (finiteEvenFourTorusZ2SpatialHalfWeight_pos
          H β energyIdentity energyNontrivial X))
      hLocalResidualNonneg
      A C target (Real.exp localRadius)
      (Real.exp localRadius * residualRatio)
      (le_of_lt (Real.exp_pos _))
      (mul_nonneg (le_of_lt (Real.exp_pos _)) hResidualRatio)
      hSpatial hLocalResidual
  have hAll :=
    finitePositiveWeightProduct_singleSiteCrossRatioBound
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorCrossingFactor
        H β energyIdentity energyNontrivial environment)
      (finitePositiveWeightProduct
        (finiteEvenFourTorusZ2SpatialHalfWeight
          H β energyIdentity energyNontrivial)
        (finitePositiveWeightProduct localFactor residual))
      (fun X => le_of_lt
        (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorCrossingFactor_pos
          H β energyIdentity energyNontrivial hβ hEnergy environment X))
      hHiddenNonneg
      A C target 1
      (Real.exp localRadius * (Real.exp localRadius * residualRatio))
      (by norm_num)
      (mul_nonneg (le_of_lt (Real.exp_pos _))
        (mul_nonneg (le_of_lt (Real.exp_pos _)) hResidualRatio))
      hCrossing hHidden
  simpa [localFactor, residual, localRadius] using hAll

/-- The exact logarithmic hidden-posterior radius obtained from one recursive
residual response coefficient. -/
def finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveCrossRatioRadius
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (target source : FiniteEvenFourTorusSpatialLink H)
    (errorBound : ℝ) : ℝ :=
  2 *
      finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalCrossRatioRadius
        H β energyIdentity energyNontrivial target source +
    Real.log
      (1 +
        finiteZ2CrossingLikelihoodRatio
            (z2WilsonTemporalCrossingRate
              β energyIdentity energyNontrivial) *
          errorBound)

/-- The recursive posterior radius is nonnegative whenever the response error
is nonnegative. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveCrossRatioRadius_nonneg
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (target source : FiniteEvenFourTorusSpatialLink H)
    (errorBound : ℝ)
    (hErrorNonneg : 0 ≤ errorBound) :
    0 ≤
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveCrossRatioRadius
        H β energyIdentity energyNontrivial target source errorBound := by
  have hLocal :
      0 ≤ finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalCrossRatioRadius
        H β energyIdentity energyNontrivial target source :=
    finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalCrossRatioRadius_nonneg
      H β energyIdentity energyNontrivial hβ.le hEnergy.le target source
  have hR :
      0 ≤ finiteZ2CrossingLikelihoodRatio
        (z2WilsonTemporalCrossingRate
          β energyIdentity energyNontrivial) :=
    le_of_lt
      (finiteZ2CrossingLikelihoodRatio_pos
        (z2WilsonTemporalCrossingRate_pos hβ hEnergy).le
        (z2WilsonTemporalCrossingRate_lt_one hβ hEnergy))
  have hOne :
      1 ≤ 1 +
        finiteZ2CrossingLikelihoodRatio
            (z2WilsonTemporalCrossingRate
              β energyIdentity energyNontrivial) * errorBound := by
    nlinarith [mul_nonneg hR hErrorNonneg]
  unfold
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveCrossRatioRadius
  exact add_nonneg (mul_nonneg (by norm_num) hLocal) (Real.log_nonneg hOne)

/-- The exact recursive residual coefficient is the exponential of its
logarithmic radius. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedRecursiveResidualCoefficient_eq_exp_log
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (errorBound : ℝ)
    (hErrorNonneg : 0 ≤ errorBound) :
    1 +
        finiteZ2CrossingLikelihoodRatio
            (z2WilsonTemporalCrossingRate
              β energyIdentity energyNontrivial) * errorBound =
      Real.exp
        (Real.log
          (1 +
            finiteZ2CrossingLikelihoodRatio
                (z2WilsonTemporalCrossingRate
                  β energyIdentity energyNontrivial) * errorBound)) := by
  have hR :
      0 ≤ finiteZ2CrossingLikelihoodRatio
        (z2WilsonTemporalCrossingRate
          β energyIdentity energyNontrivial) :=
    le_of_lt
      (finiteZ2CrossingLikelihoodRatio_pos
        (z2WilsonTemporalCrossingRate_pos hβ hEnergy).le
        (z2WilsonTemporalCrossingRate_lt_one hβ hEnergy))
  have hPos :
      0 < 1 +
        finiteZ2CrossingLikelihoodRatio
            (z2WilsonTemporalCrossingRate
              β energyIdentity energyNontrivial) * errorBound := by
    nlinarith [mul_nonneg hR hErrorNonneg]
  exact (Real.exp_log hPos).symm

/-- The actual recursive residual response compiles into an explicit
off-diagonal hidden-posterior exponential cross-ratio radius. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight_crossRatio_of_recursiveResponse
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (environment A C : FiniteEvenFourTorusZ2SliceConfiguration H)
    (target source : FiniteEvenFourTorusSpatialLink H)
    (hNe : target ≠ source)
    (hAgree : FiniteProductAgreeOff A C source)
    (n : ℕ)
    (errorBound : ℝ)
    (hErrorNonneg : 0 ≤ errorBound)
    (D : ∀ g : Z2Gauge,
      FinitePositiveWeightDobrushinL1MatrixData
        (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
          H β energyIdentity energyNontrivial hβ.le hEnergy.le
          (Function.update A target g)))
    (hError :
      ∀ g h : Z2Gauge,
        finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedRecursiveResponseError
          H β energyIdentity energyNontrivial hβ hEnergy
          A target source g h (C source) (D g) n ≤ errorBound) :
    FinitePositiveWeightSingleSiteCrossRatioBound
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
        H β energyIdentity energyNontrivial hβ.le hEnergy.le environment)
      A C target
      (Real.exp
        (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveCrossRatioRadius
          H β energyIdentity energyNontrivial target source errorBound)) := by
  have hResidualRaw :=
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidual_crossRatio_of_recursiveResponse
      H β energyIdentity energyNontrivial hβ hEnergy
      A C target source hNe hAgree n errorBound hErrorNonneg D hError
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
                    β energyIdentity energyNontrivial) * errorBound))) := by
    rw [←
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedRecursiveResidualCoefficient_eq_exp_log
        H β energyIdentity energyNontrivial hβ hEnergy errorBound hErrorNonneg]
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
                  β energyIdentity energyNontrivial) * errorBound)))
      (le_of_lt (Real.exp_pos _)) hResidual
  let localRadius :=
    finiteEvenFourTorusZ2UnfixedGaugePerronSandwichLocalCrossRatioRadius
      H β energyIdentity energyNontrivial target source
  let residualRadius :=
    Real.log
      (1 +
        finiteZ2CrossingLikelihoodRatio
            (z2WilsonTemporalCrossingRate
              β energyIdentity energyNontrivial) * errorBound)
  have hExp :
      Real.exp
          (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveCrossRatioRadius
            H β energyIdentity energyNontrivial target source errorBound) =
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

end

end MathlibAnalytic
end MGAP4D
