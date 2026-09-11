import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPerronPosteriorNonstrictKernelResponse
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Finite-step target-fiber response error for an arbitrary declared
observable variation profile.  Random scan is used only as the exact
stationary Gibbs comparison operator; this quantity is not a geometric
one-slab transfer rate. -/
noncomputable def finiteEvenFourTorusZ2PerronPosteriorObservableKernelResponseError
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (kernel :
      FiniteNonnegativeInfluenceKernelData
        (FiniteEvenFourTorusSpatialLink H))
    (iterations : ℕ)
    (target : FiniteEvenFourTorusSpatialLink H)
    (variation : FiniteEvenFourTorusSpatialLink H → ℝ) : ℝ :=
  finiteInfluenceKernelPartialSource
      kernel
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTiltSourceEnvelope
        H β energyIdentity energyNontrivial target)
      variation
      iterations +
    2 * finiteProductVariationTotal
      (finiteInfluenceKernelRandomScanVariationIterate
        kernel variation iterations)

/-- The arbitrary-observable response error is nonnegative for a nonnegative
variation profile. -/
theorem finiteEvenFourTorusZ2PerronPosteriorObservableKernelResponseError_nonneg
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (kernel :
      FiniteNonnegativeInfluenceKernelData
        (FiniteEvenFourTorusSpatialLink H))
    (iterations : ℕ)
    (target : FiniteEvenFourTorusSpatialLink H)
    (variation : FiniteEvenFourTorusSpatialLink H → ℝ)
    (hVariation : ∀ e, 0 ≤ variation e) :
    0 ≤ finiteEvenFourTorusZ2PerronPosteriorObservableKernelResponseError
      H β energyIdentity energyNontrivial
      kernel iterations target variation := by
  unfold finiteEvenFourTorusZ2PerronPosteriorObservableKernelResponseError
  have hEnvelope :
      ∀ e : FiniteEvenFourTorusSpatialLink H,
        0 ≤ finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTiltSourceEnvelope
          H β energyIdentity energyNontrivial target e :=
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTiltSourceEnvelope_nonneg
      H β energyIdentity energyNontrivial hβ hEnergy target
  have hPartial :
      0 ≤ finiteInfluenceKernelPartialSource
        kernel
        (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTiltSourceEnvelope
          H β energyIdentity energyNontrivial target)
        variation iterations := by
    induction iterations with
    | zero => exact le_rfl
    | succ n ih =>
        rw [finiteInfluenceKernelPartialSource_succ]
        exact add_nonneg ih
          (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
            (Finset.sum_nonneg fun e _he =>
              mul_nonneg (hEnvelope e)
                (finiteInfluenceKernelRandomScanVariationIterate_nonneg
                  kernel variation hVariation n e)))
  exact add_nonneg hPartial
    (mul_nonneg (by norm_num)
      (Finset.sum_nonneg fun e _he =>
        finiteInfluenceKernelRandomScanVariationIterate_nonneg
          kernel variation hVariation iterations e))

/-- A one-coordinate boundary change controls the normalized expectation of
any observable by the finite kernel propagation of its declared variation
profile. -/
theorem
    finiteEvenFourTorusZ2PerronPosteriorGlobalExpectation_update_difference_abs_le_observableKernelResponse
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H)
    (target : FiniteEvenFourTorusSpatialLink H)
    (g h : Z2Gauge)
    (kernel :
      FiniteNonnegativeInfluenceKernelData
        (FiniteEvenFourTorusSpatialLink H))
    (iterations : ℕ)
    (hDomination :
      FiniteEvenFourTorusZ2PerronPosteriorCanonicalDominatedBy
        H β energyIdentity energyNontrivial hβ hEnergy kernel)
    (f : FiniteEvenFourTorusZ2SliceConfiguration H → ℝ)
    (P : FiniteProductVariationBound f) :
    |finitePositiveWeightGlobalExpectation
          (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
            H β energyIdentity energyNontrivial hβ.le hEnergy.le
            (Function.update environment target h)) f -
        finitePositiveWeightGlobalExpectation
          (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
            H β energyIdentity energyNontrivial hβ.le hEnergy.le
            (Function.update environment target g)) f| ≤
      finiteEvenFourTorusZ2PerronPosteriorObservableKernelResponseError
        H β energyIdentity energyNontrivial
        kernel iterations target P.variation := by
  let comparison :=
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetFiberNonstrictComparisonData
      H β energyIdentity energyNontrivial hβ hEnergy
      environment target g h
  have hKernelDomination :
      FinitePositiveWeightNonstrictInfluenceDominatedBy
        comparison.rightInfluence kernel.influence := by
    intro responseTarget responseSource
    simpa [comparison,
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetFiberNonstrictComparisonData,
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorCanonicalNonstrictData]
      using hDomination
        environment target g responseTarget responseSource
  have hEnvelopeNonneg :
      ∀ e : FiniteEvenFourTorusSpatialLink H,
        0 ≤ finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTiltSourceEnvelope
          H β energyIdentity energyNontrivial target e :=
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTiltSourceEnvelope_nonneg
      H β energyIdentity energyNontrivial hβ hEnergy target
  have hEnvelope :
      ∀ e : FiniteEvenFourTorusSpatialLink H,
        comparison.sourceBound e ≤
          finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTiltSourceEnvelope
            H β energyIdentity energyNontrivial target e := by
    intro e
    exact le_rfl
  have hPartial :=
    comparison.partialStationarySource_le_kernel
      P kernel hKernelDomination
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTiltSourceEnvelope
        H β energyIdentity energyNontrivial target)
      hEnvelopeNonneg hEnvelope iterations
  have hTerminal :
      finiteProductVariationTotal
          (comparison.rightRandomScanIterateVariationBound
            P iterations).variation ≤
        finiteProductVariationTotal
          (finiteInfluenceKernelRandomScanVariationIterate
            kernel P.variation iterations) := by
    unfold finiteProductVariationTotal
    apply Finset.sum_le_sum
    intro e _he
    rw [comparison.rightRandomScanIterateVariation_eq P iterations]
    exact
      finitePositiveWeightNonstrictRandomScanVariationIterate_le_kernel
        comparison.rightInfluence kernel hKernelDomination P.variation
        P.variation_nonneg iterations e
  have hFinite :=
    comparison.expectationDiscrepancy_le_partialSource_add_two_mul_terminalVariation
      P iterations
  have hBound :
      comparison.expectationDiscrepancy f ≤
        finiteEvenFourTorusZ2PerronPosteriorObservableKernelResponseError
          H β energyIdentity energyNontrivial
          kernel iterations target P.variation := by
    apply hFinite.trans
    unfold finiteEvenFourTorusZ2PerronPosteriorObservableKernelResponseError
    exact add_le_add hPartial
      (mul_le_mul_of_nonneg_left hTerminal (by norm_num))
  rw [
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight_update_target_eq_tilt
      H β energyIdentity energyNontrivial hβ hEnergy
      environment target g h]
  simpa [comparison,
    FinitePositiveWeightStationaryNonstrictComparisonData.expectationDiscrepancy]
    using hBound

end

end MathlibAnalytic
end MGAP4D
