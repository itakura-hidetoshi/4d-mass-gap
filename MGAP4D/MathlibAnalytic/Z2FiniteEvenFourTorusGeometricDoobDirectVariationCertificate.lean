import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusGeometricDoobDirectResponseMatrix
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPerronPosteriorComponentObservableResponse
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeDoobMixtureIndexUniformity
import MGAP4D.MathlibAnalytic.FiniteProductDoobParallelVariation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- When two boundary configurations differ at most at one link, the exact
same-index posterior component response is bounded by the one corresponding
observable-response entry. -/
theorem
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentExpectation_difference_abs_le_observableKernelResponse_of_agreeOff
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (left right : FiniteEvenFourTorusZ2SliceConfiguration H)
    (target : FiniteEvenFourTorusSpatialLink H)
    (hAgree : FiniteProductAgreeOff left right target)
    (f : FiniteEvenFourTorusZ2SliceConfiguration H → ℝ)
    (P : FiniteProductVariationBound f)
    (kernel :
      FiniteNonnegativeInfluenceKernelData
        (FiniteEvenFourTorusSpatialLink H))
    (iterations : ℕ)
    (hDomination :
      FiniteEvenFourTorusZ2PerronPosteriorCanonicalDominatedBy
        H β energyIdentity energyNontrivial hβ hEnergy kernel) :
    |(finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentProbabilityData
          C β hβ hβCutoff H right g).expectation f -
        (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentProbabilityData
          C β hβ hβCutoff H left g).expectation f| ≤
      finiteEvenFourTorusZ2PerronPosteriorObservableKernelResponseError
        H β energyIdentity energyNontrivial
        kernel iterations target P.variation := by
  by_cases hTarget : left target = right target
  · have hEq : left = right := by
      funext source
      by_cases hSource : source = target
      · simpa [hSource] using hTarget
      · exact hAgree source hSource
    subst right
    simp
    exact
      finiteEvenFourTorusZ2PerronPosteriorObservableKernelResponseError_nonneg
        H β energyIdentity energyNontrivial hβ hEnergy
        kernel iterations target P.variation P.variation_nonneg
  · have hDisagreement :
        finiteProductDisagreementFinset left right = {target} := by
      ext source
      by_cases hSource : source = target
      · subst source
        simp [finiteProductDisagreementFinset, hTarget]
      · have hSame := hAgree source hSource
        simp [finiteProductDisagreementFinset, hSource, hSame]
    have h :=
      finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentExpectation_difference_abs_le_disagreementResponseSum
        C β hβ hβCutoff H g left right f P kernel iterations hDomination
    rw [hDisagreement] at h
    simpa using h

/-- The exact geometric Perron--Doob observable action is the convex mixture
of the normalized same-index posterior component expectations. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobObservable_eq_componentExpectationSum
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H)
    (f : FiniteEvenFourTorusZ2SliceConfiguration H → ℝ) :
    (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
        H β energyIdentity energyNontrivial hβ.le hEnergy.le).doobObservableLinearMap
        f environment =
      ∑ g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
        (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexProbabilityData
          C β hβ hβCutoff H environment).probability g *
        (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentProbabilityData
          C β hβ hβCutoff H environment g).expectation f := by
  let D := finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
    H β energyIdentity energyNontrivial hβ.le hEnergy.le
  rw [D.doobObservableLinearMap_apply]
  calc
    (∑ hidden : FiniteEvenFourTorusZ2SliceConfiguration H,
        D.doobKernel hidden environment * f hidden) =
      ∑ hidden : FiniteEvenFourTorusZ2SliceConfiguration H,
        (∑ g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
          (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexProbabilityData
            C β hβ hβCutoff H environment).probability g *
          (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentProbabilityData
            C β hβ hβCutoff H environment g).probability hidden) *
          f hidden := by
      apply Finset.sum_congr rfl
      intro hidden _hhidden
      rw [show D.doobKernel hidden environment =
        finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobKernel
          H β energyIdentity energyNontrivial hβ.le hEnergy.le
          hidden environment by rfl]
      rw [finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobKernel_eq_residualGaugePerronSmoothedMixture
        C β hβ hβCutoff H environment hidden]
    _ = ∑ hidden : FiniteEvenFourTorusZ2SliceConfiguration H,
        ∑ g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
          (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexProbabilityData
            C β hβ hβCutoff H environment).probability g *
          (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentProbabilityData
            C β hβ hβCutoff H environment g).probability hidden *
          f hidden := by
      apply Finset.sum_congr rfl
      intro hidden _hhidden
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro g _hg
      ring
    _ = ∑ g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
        ∑ hidden : FiniteEvenFourTorusZ2SliceConfiguration H,
          (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexProbabilityData
            C β hβ hβCutoff H environment).probability g *
          (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentProbabilityData
            C β hβ hβCutoff H environment g).probability hidden *
          f hidden := by
      rw [Finset.sum_comm]
    _ = ∑ g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
        (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexProbabilityData
          C β hβ hβCutoff H environment).probability g *
        (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentProbabilityData
          C β hβ hβCutoff H environment g).expectation f := by
      apply Finset.sum_congr rfl
      intro g _hg
      unfold FiniteRealProbabilityData.expectation
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro hidden _hhidden
      ring

/-- Environment independence of the residual-gauge index law transports the
same-index component response directly to the exact geometric Doob row. -/
theorem
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobObservable_difference_abs_le_observableKernelResponse_of_agreeOff
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (left right : FiniteEvenFourTorusZ2SliceConfiguration H)
    (target : FiniteEvenFourTorusSpatialLink H)
    (hAgree : FiniteProductAgreeOff left right target)
    (f : FiniteEvenFourTorusZ2SliceConfiguration H → ℝ)
    (P : FiniteProductVariationBound f)
    (kernel :
      FiniteNonnegativeInfluenceKernelData
        (FiniteEvenFourTorusSpatialLink H))
    (iterations : ℕ)
    (hDomination :
      FiniteEvenFourTorusZ2PerronPosteriorCanonicalDominatedBy
        H β energyIdentity energyNontrivial hβ hEnergy kernel) :
    |(finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
          H β energyIdentity energyNontrivial hβ.le hEnergy.le).doobObservableLinearMap
          f right -
        (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
          H β energyIdentity energyNontrivial hβ.le hEnergy.le).doobObservableLinearMap
          f left| ≤
      finiteEvenFourTorusZ2PerronPosteriorObservableKernelResponseError
        H β energyIdentity energyNontrivial
        kernel iterations target P.variation := by
  rw [finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobObservable_eq_componentExpectationSum
      C β hβ hβCutoff H right f,
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobObservable_eq_componentExpectationSum
      C β hβ hβCutoff H left f]
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
        ((finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexProbabilityData
            C β hβ hβCutoff H right).probability g *
          (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentProbabilityData
            C β hβ hβCutoff H right g).expectation f -
        (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexProbabilityData
            C β hβ hβCutoff H left).probability g *
          (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentProbabilityData
            C β hβ hβCutoff H left g).expectation f)| ≤
      ∑ g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
        |(finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexProbabilityData
            C β hβ hβCutoff H right).probability g *
          (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentProbabilityData
            C β hβ hβCutoff H right g).expectation f -
        (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexProbabilityData
            C β hβ hβCutoff H left).probability g *
          (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentProbabilityData
            C β hβ hβCutoff H left g).expectation f| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
        (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexProbabilityData
            C β hβ hβCutoff H left).probability g *
          |(finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentProbabilityData
              C β hβ hβCutoff H right g).expectation f -
            (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentProbabilityData
              C β hβ hβCutoff H left g).expectation f| := by
      apply Finset.sum_congr rfl
      intro g _hg
      rw [← finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexProbability_environment_independent
        C β hβ hβCutoff H left right g]
      rw [← mul_sub, abs_mul,
        abs_of_nonneg
          ((finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexProbabilityData
            C β hβ hβCutoff H left).probability_nonneg g)]
    _ ≤ ∑ g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
        (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexProbabilityData
            C β hβ hβCutoff H left).probability g *
          finiteEvenFourTorusZ2PerronPosteriorObservableKernelResponseError
            H β energyIdentity energyNontrivial
            kernel iterations target P.variation := by
      apply Finset.sum_le_sum
      intro g _hg
      exact mul_le_mul_of_nonneg_left
        (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentExpectation_difference_abs_le_observableKernelResponse_of_agreeOff
          C β hβ hβCutoff H g left right target hAgree
          f P kernel iterations hDomination)
        ((finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexProbabilityData
          C β hβ hβCutoff H left).probability_nonneg g)
    _ = finiteEvenFourTorusZ2PerronPosteriorObservableKernelResponseError
          H β energyIdentity energyNontrivial
          kernel iterations target P.variation := by
      rw [← Finset.sum_mul]
      rw [(finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexProbabilityData
        C β hβ hβCutoff H left).probability_sum_eq_one]
      ring

/-- The concrete posterior observable response is exactly the action of the
strict coordinate-response matrix on the declared variation profile. -/
theorem finiteEvenFourTorusZ2PerronPosteriorObservableKernelResponseError_eq_directResponseMatrix
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy)
    (H : ℕ)
    (target : FiniteEvenFourTorusSpatialLink H)
    (variation : FiniteEvenFourTorusSpatialLink H → ℝ) :
    finiteEvenFourTorusZ2PerronPosteriorObservableKernelResponseError
        H β energyIdentity energyNontrivial
        (finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeKernel
          H β energyIdentity energyNontrivial hβ hEnergy)
        (finiteEvenFourTorusZ2GeometricDoobDirectResponseIterations
          energyIdentity energyNontrivial hEnergy β hβ hβCutoff H)
        target variation =
      ∑ source : FiniteEvenFourTorusSpatialLink H,
        finiteEvenFourTorusZ2GeometricDoobDirectResponseInfluence
          energyIdentity energyNontrivial hEnergy β hβ hβCutoff
          H target source * variation source := by
  unfold finiteEvenFourTorusZ2PerronPosteriorObservableKernelResponseError
    finiteEvenFourTorusZ2GeometricDoobDirectResponseInfluence
    finiteInfluenceKernelObservableResponseEntry
    finiteInfluenceKernelObservableResponse
  exact
    finiteInfluenceKernelObservableResponse_eq_matrix_mul
      (finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeKernel
        H β energyIdentity energyNontrivial hβ hEnergy)
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTiltSourceEnvelope
        H β energyIdentity energyNontrivial target)
      variation
      (finiteEvenFourTorusZ2GeometricDoobDirectResponseIterations
        energyIdentity energyNontrivial hEnergy β hβ hβCutoff H)

/-- The exact geometric Doob observable map has canonical coordinate variation
bounded by the strict direct response matrix. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobObservable_canonicalVariation_le_directResponseMatrix
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy)
    (H : ℕ)
    (f : FiniteEvenFourTorusZ2SliceConfiguration H → ℝ)
    (target : FiniteEvenFourTorusSpatialLink H) :
    finiteProductCanonicalVariation
        ((finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
          H β energyIdentity energyNontrivial hβ.le hEnergy.le).doobObservableLinearMap f)
        target ≤
      ∑ source : FiniteEvenFourTorusSpatialLink H,
        finiteEvenFourTorusZ2GeometricDoobDirectResponseInfluence
          energyIdentity energyNontrivial hEnergy β hβ hβCutoff
          H target source * finiteProductCanonicalVariation f source := by
  let C :=
    finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy
  have hβActual : β ≤ C.couplingCutoff :=
    hβCutoff.trans
      (finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff_le_actual
        energyIdentity energyNontrivial hEnergy)
  let P : FiniteProductVariationBound f :=
    { variation := fun source => finiteProductCanonicalVariation f source
      variation_nonneg := finiteProductCanonicalVariation_nonneg f
      variation_bound := by
        intro source left right hAgree
        exact finiteProduct_difference_abs_le_canonicalVariation
          f source left right hAgree }
  let Q : FiniteProductVariationBound
      ((finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
        H β energyIdentity energyNontrivial hβ.le hEnergy.le).doobObservableLinearMap f) :=
    { variation := fun responseTarget =>
        ∑ source : FiniteEvenFourTorusSpatialLink H,
          finiteEvenFourTorusZ2GeometricDoobDirectResponseInfluence
            energyIdentity energyNontrivial hEnergy β hβ hβCutoff
            H responseTarget source * finiteProductCanonicalVariation f source
      variation_nonneg := by
        intro responseTarget
        exact Finset.sum_nonneg fun source _hsource =>
          mul_nonneg
            (finiteEvenFourTorusZ2GeometricDoobDirectResponseInfluence_nonneg
              energyIdentity energyNontrivial hEnergy β hβ hβCutoff
              H responseTarget source)
            (finiteProductCanonicalVariation_nonneg f source)
      variation_bound := by
        intro responseTarget left right hAgree
        have hBound :=
          finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobObservable_difference_abs_le_observableKernelResponse_of_agreeOff
            C β hβ hβActual H left right responseTarget hAgree
            f P
            (finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeKernel
              H β energyIdentity energyNontrivial hβ hEnergy)
            (finiteEvenFourTorusZ2GeometricDoobDirectResponseIterations
              energyIdentity energyNontrivial hEnergy β hβ hβCutoff H)
            (finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeKernel_dominates
              H β energyIdentity energyNontrivial hβ hEnergy)
        rw [finiteEvenFourTorusZ2PerronPosteriorObservableKernelResponseError_eq_directResponseMatrix
          energyIdentity energyNontrivial hEnergy β hβ hβCutoff
          H responseTarget P.variation] at hBound
        simpa [P, abs_sub_comm] using hBound }
  exact finiteProductCanonicalVariation_le_variationBound Q target

/-- Proof-relevant strict variation matrix for the exact geometric Perron--Doob
observable map at one finite side. -/
noncomputable def finiteEvenFourTorusZ2GeometricDoobDirectVariationMatrixData
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy)
    (H : ℕ) :
    FiniteProductParallelVariationMatrixData
      (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
        H β energyIdentity energyNontrivial hβ.le hEnergy.le).doobObservableLinearMap where
  influence :=
    finiteEvenFourTorusZ2GeometricDoobDirectResponseInfluence
      energyIdentity energyNontrivial hEnergy β hβ hβCutoff H
  influence_nonneg :=
    finiteEvenFourTorusZ2GeometricDoobDirectResponseInfluence_nonneg
      energyIdentity energyNontrivial hEnergy β hβ hβCutoff H
  canonicalVariation_le :=
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobObservable_canonicalVariation_le_directResponseMatrix
      energyIdentity energyNontrivial hEnergy β hβ hβCutoff H
  coefficient := 1 / 2
  coefficient_nonneg := by norm_num
  columnSum_le_coefficient := by
    intro source
    exact le_of_lt
      (finiteEvenFourTorusZ2GeometricDoobDirectResponseInfluence_columnSum_lt_half
        energyIdentity energyNontrivial hEnergy β hβ hβCutoff H source)
  coefficient_lt_one := by norm_num

/-- Direct parallel variation certificate for the actual geometric Doob row. -/
noncomputable def finiteEvenFourTorusZ2GeometricDoobDirectParallelVariationCertificate
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy)
    (H : ℕ) :
    FiniteProductDoobParallelVariationCertificate
      (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
        H β energyIdentity energyNontrivial hβ.le hEnergy.le) where
  variationData :=
    finiteEvenFourTorusZ2GeometricDoobDirectVariationMatrixData
      energyIdentity energyNontrivial hEnergy β hβ hβCutoff H

end

end MathlibAnalytic
end MGAP4D
