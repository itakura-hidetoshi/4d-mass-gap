import MGAP4D.MathlibAnalytic.FiniteZ2GaugeProductKernelBoundaryTilt
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugePerronSmoothedResidualFactorization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Positive hidden-slice input weight smoothed by the normalized temporal
crossing kernel in the Perron sandwich equation. -/
def finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedHiddenWeight
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (hidden : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  finiteEvenFourTorusZ2SpatialHalfWeight
      H β energyIdentity energyNontrivial hidden *
    finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
      H β energyIdentity energyNontrivial hβ hEnergy hidden

/-- The hidden Perron sandwich input weight is strictly positive. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedHiddenWeight_pos
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (hidden : FiniteEvenFourTorusZ2SliceConfiguration H) :
    0 < finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedHiddenWeight
      H β energyIdentity energyNontrivial hβ hEnergy hidden := by
  exact mul_pos
    (finiteEvenFourTorusZ2SpatialHalfWeight_pos
      H β energyIdentity energyNontrivial hidden)
    (finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_pos
      H β energyIdentity energyNontrivial hβ hEnergy hidden)

/-- The smoothed Perron residual is exactly the generic finite positive kernel
normalizer for the normalized product crossing kernel and the hidden sandwich
weight. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidual_eq_kernelNormalizer
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidual
        H β energyIdentity energyNontrivial hβ hEnergy environment =
      finitePositiveKernelNormalizer
        (finiteEvenFourTorusZ2NormalizedTemporalCrossingKernel
          H β energyIdentity energyNontrivial)
        (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedHiddenWeight
          H β energyIdentity energyNontrivial hβ hEnergy)
        environment := by
  unfold finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidual
    finitePositiveKernelNormalizer
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedHiddenWeight
  rw [finiteKernelOperator_apply]
  apply Finset.sum_congr rfl
  intro hidden _hHidden
  rw [finiteEvenFourTorusZ2SpatialHalfWeightMultiplicationOperator_apply]

/-- Actual hidden one-link likelihood tilt produced by changing one observed
boundary link of the normalized temporal crossing product kernel. -/
def finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidualSourceTilt
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (base : FiniteEvenFourTorusZ2SliceConfiguration H)
    (source : FiniteEvenFourTorusSpatialLink H)
    (replacement : Z2Gauge)
    (hidden : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  finiteZ2GaugeNormalizedProductKernelBoundaryTilt
    (z2WilsonTemporalCrossingRate
      β energyIdentity energyNontrivial)
    base source replacement hidden

/-- The actual residual source tilt is strictly positive at strict coupling. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidualSourceTilt_pos
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (base : FiniteEvenFourTorusZ2SliceConfiguration H)
    (source : FiniteEvenFourTorusSpatialLink H)
    (replacement : Z2Gauge)
    (hidden : FiniteEvenFourTorusZ2SliceConfiguration H) :
    0 < finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidualSourceTilt
      H β energyIdentity energyNontrivial
      base source replacement hidden := by
  exact finiteZ2GaugeNormalizedProductKernelBoundaryTilt_pos
    (z2WilsonTemporalCrossingRate_pos hβ hEnergy).le
    (z2WilsonTemporalCrossingRate_lt_one hβ hEnergy)
    base source replacement hidden

/-- The actual residual source tilt depends only on the hidden source link. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidualSourceTilt_supportedOn_source
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (base : FiniteEvenFourTorusZ2SliceConfiguration H)
    (source : FiniteEvenFourTorusSpatialLink H)
    (replacement : Z2Gauge) :
    FiniteProductFunctionSupportedOn ({source} :
      Finset (FiniteEvenFourTorusSpatialLink H))
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidualSourceTilt
        H β energyIdentity energyNontrivial base source replacement) := by
  exact
    finiteZ2GaugeNormalizedProductKernelBoundaryTilt_supportedOn_source
      (z2WilsonTemporalCrossingRate
        β energyIdentity energyNontrivial)
      base source replacement

/-- Normalized hidden posterior expectation of the actual one-source crossing
tilt at a specified observed environment. -/
def finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidualSourceTiltExpectation
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (base environment : FiniteEvenFourTorusZ2SliceConfiguration H)
    (source : FiniteEvenFourTorusSpatialLink H)
    (replacement : Z2Gauge) : ℝ :=
  finitePositiveKernelTiltExpectation
    (finiteEvenFourTorusZ2NormalizedTemporalCrossingKernel
      H β energyIdentity energyNontrivial)
    (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedHiddenWeight
      H β energyIdentity energyNontrivial hβ hEnergy)
    environment
    (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidualSourceTilt
      H β energyIdentity energyNontrivial base source replacement)

/-- If two observed environments differ only at `source`, then after assigning
the same value at a distinct target they remain related by one common hidden
source-link tilt. -/
theorem finiteEvenFourTorusZ2NormalizedTemporalCrossingKernel_boundaryTiltRelation_update_target
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (A C : FiniteEvenFourTorusZ2SliceConfiguration H)
    (target source : FiniteEvenFourTorusSpatialLink H)
    (hNe : target ≠ source)
    (hAgree : FiniteProductAgreeOff A C source)
    (value : Z2Gauge) :
    FinitePositiveKernelBoundaryTiltRelation
      (finiteEvenFourTorusZ2NormalizedTemporalCrossingKernel
        H β energyIdentity energyNontrivial)
      (Function.update A target value)
      (Function.update C target value)
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidualSourceTilt
        H β energyIdentity energyNontrivial A source (C source)) := by
  have hAgreeUpdated :
      FiniteProductAgreeOff
        (Function.update A target value)
        (Function.update C target value)
        source := by
    intro coordinate hCoordinateSource
    by_cases hCoordinateTarget : coordinate = target
    · subst coordinate
      simp
    · simp [Function.update, hCoordinateTarget,
        hAgree coordinate hCoordinateSource]
  have hRelation :=
    finiteZ2GaugeNormalizedProductKernel_boundaryTiltRelation_of_agreeOff
      (z2WilsonTemporalCrossingRate_pos hβ hEnergy).le
      (z2WilsonTemporalCrossingRate_lt_one hβ hEnergy)
      (FiniteEvenFourTorusSpatialLink H)
      (Function.update A target value)
      (Function.update C target value)
      source hAgreeUpdated
  simpa [finiteEvenFourTorusZ2NormalizedTemporalCrossingKernel,
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidualSourceTilt,
    Function.update, hNe, Ne.symm hNe] using hRelation

/-- The actual smoothed-residual cross-ratio row is reduced exactly to a
comparison of one-source local-tilt expectations under two target-fiber hidden
posteriors.  This is the normalized rowwise comparison input for the next
Dobrushin/ground-state iteration. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidual_crossRatio_of_sourceTiltExpectation
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (A C : FiniteEvenFourTorusZ2SliceConfiguration H)
    (target source : FiniteEvenFourTorusSpatialLink H)
    (hNe : target ≠ source)
    (hAgree : FiniteProductAgreeOff A C source)
    (ratio : ℝ)
    (hExpectation :
      ∀ g h : Z2Gauge,
        finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidualSourceTiltExpectation
            H β energyIdentity energyNontrivial hβ.le hEnergy.le
            A (Function.update A target h) source (C source) ≤
          ratio *
            finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidualSourceTiltExpectation
              H β energyIdentity energyNontrivial hβ.le hEnergy.le
              A (Function.update A target g) source (C source)) :
    FinitePositiveWeightSingleSiteCrossRatioBound
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidual
        H β energyIdentity energyNontrivial hβ.le hEnergy.le)
      A C target ratio := by
  rw [show
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidual
        H β energyIdentity energyNontrivial hβ.le hEnergy.le =
      finitePositiveKernelNormalizer
        (finiteEvenFourTorusZ2NormalizedTemporalCrossingKernel
          H β energyIdentity energyNontrivial)
        (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedHiddenWeight
          H β energyIdentity energyNontrivial hβ.le hEnergy.le) by
      funext environment
      exact
        finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidual_eq_kernelNormalizer
          H β energyIdentity energyNontrivial hβ.le hEnergy.le environment]
  exact
    finitePositiveKernelNormalizer_crossRatio_of_tiltExpectation
      (finiteEvenFourTorusZ2NormalizedTemporalCrossingKernel
        H β energyIdentity energyNontrivial)
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedHiddenWeight
        H β energyIdentity energyNontrivial hβ.le hEnergy.le)
      (by
        intro hidden environment
        unfold finiteEvenFourTorusZ2NormalizedTemporalCrossingKernel
        exact finiteZ2GaugeNormalizedProductKernel_pos
          (z2WilsonTemporalCrossingRate_pos hβ hEnergy).le
          (z2WilsonTemporalCrossingRate_lt_one hβ hEnergy)
          (FiniteEvenFourTorusSpatialLink H) hidden environment)
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedHiddenWeight_pos
        H β energyIdentity energyNontrivial hβ.le hEnergy.le)
      A C target
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidualSourceTilt
        H β energyIdentity energyNontrivial A source (C source))
      ratio
      (fun value =>
        finiteEvenFourTorusZ2NormalizedTemporalCrossingKernel_boundaryTiltRelation_update_target
          H β energyIdentity energyNontrivial hβ hEnergy
          A C target source hNe hAgree value)
      (by
        intro g h
        simpa [
          finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedResidualSourceTiltExpectation]
          using hExpectation g h)

end

end MathlibAnalytic
end MGAP4D
