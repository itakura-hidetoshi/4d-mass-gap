import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPerronPosteriorObservableKernelResponse
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusResidualGaugeHammingIsometry
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Normalized Perron-smoothed posterior expectation at one spatial
boundary environment. -/
noncomputable def finiteEvenFourTorusZ2PerronPosteriorGlobalExpectation
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H)
    (f : FiniteEvenFourTorusZ2SliceConfiguration H → ℝ) : ℝ :=
  finitePositiveWeightGlobalExpectation
    (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
      H β energyIdentity energyNontrivial hβ.le hEnergy.le environment)
    f

/-- Replacing a finite set of boundary coordinates changes an arbitrary
posterior observable expectation by at most the sum of the corresponding
one-coordinate kernel response errors. -/
theorem
    finiteEvenFourTorusZ2PerronPosteriorGlobalExpectation_replaceOn_difference_abs_le_sum
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (left right : FiniteEvenFourTorusZ2SliceConfiguration H)
    (f : FiniteEvenFourTorusZ2SliceConfiguration H → ℝ)
    (P : FiniteProductVariationBound f)
    (kernel :
      FiniteNonnegativeInfluenceKernelData
        (FiniteEvenFourTorusSpatialLink H))
    (iterations : ℕ)
    (hDomination :
      FiniteEvenFourTorusZ2PerronPosteriorCanonicalDominatedBy
        H β energyIdentity energyNontrivial hβ hEnergy kernel)
    (s : Finset (FiniteEvenFourTorusSpatialLink H)) :
    |finiteEvenFourTorusZ2PerronPosteriorGlobalExpectation
          H β energyIdentity energyNontrivial hβ hEnergy
          (finiteProductReplaceOn left right s) f -
        finiteEvenFourTorusZ2PerronPosteriorGlobalExpectation
          H β energyIdentity energyNontrivial hβ hEnergy left f| ≤
      ∑ target ∈ s,
        finiteEvenFourTorusZ2PerronPosteriorObservableKernelResponseError
          H β energyIdentity energyNontrivial
          kernel iterations target P.variation := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [finiteProductReplaceOn,
        finiteEvenFourTorusZ2PerronPosteriorGlobalExpectation]
  | @insert source s hSource ih =>
      let current : FiniteEvenFourTorusZ2SliceConfiguration H :=
        finiteProductReplaceOn left right s
      let next : FiniteEvenFourTorusZ2SliceConfiguration H :=
        finiteProductReplaceOn left right (insert source s)
      have hCurrentUpdate :
          Function.update current source (current source) = current := by
        exact Function.update_eq_self source current
      have hNextUpdate :
          Function.update current source (right source) = next := by
        funext coordinate
        by_cases hEq : coordinate = source
        · subst coordinate
          simp [current, next, finiteProductReplaceOn]
        · simp [current, next, finiteProductReplaceOn, hEq]
      have hOneRaw :=
        finiteEvenFourTorusZ2PerronPosteriorGlobalExpectation_update_difference_abs_le_observableKernelResponse
          H β energyIdentity energyNontrivial hβ hEnergy
          current source (current source) (right source)
          kernel iterations hDomination f P
      have hOne :
          |finiteEvenFourTorusZ2PerronPosteriorGlobalExpectation
                H β energyIdentity energyNontrivial hβ hEnergy next f -
              finiteEvenFourTorusZ2PerronPosteriorGlobalExpectation
                H β energyIdentity energyNontrivial hβ hEnergy current f| ≤
            finiteEvenFourTorusZ2PerronPosteriorObservableKernelResponseError
              H β energyIdentity energyNontrivial
              kernel iterations source P.variation := by
        simpa [finiteEvenFourTorusZ2PerronPosteriorGlobalExpectation,
          hCurrentUpdate, hNextUpdate] using hOneRaw
      calc
        |finiteEvenFourTorusZ2PerronPosteriorGlobalExpectation
              H β energyIdentity energyNontrivial hβ hEnergy next f -
            finiteEvenFourTorusZ2PerronPosteriorGlobalExpectation
              H β energyIdentity energyNontrivial hβ hEnergy left f| =
          |(finiteEvenFourTorusZ2PerronPosteriorGlobalExpectation
                H β energyIdentity energyNontrivial hβ hEnergy next f -
              finiteEvenFourTorusZ2PerronPosteriorGlobalExpectation
                H β energyIdentity energyNontrivial hβ hEnergy current f) +
            (finiteEvenFourTorusZ2PerronPosteriorGlobalExpectation
                H β energyIdentity energyNontrivial hβ hEnergy current f -
              finiteEvenFourTorusZ2PerronPosteriorGlobalExpectation
                H β energyIdentity energyNontrivial hβ hEnergy left f)| := by
            congr 1
            ring
        _ ≤
          |finiteEvenFourTorusZ2PerronPosteriorGlobalExpectation
                H β energyIdentity energyNontrivial hβ hEnergy next f -
              finiteEvenFourTorusZ2PerronPosteriorGlobalExpectation
                H β energyIdentity energyNontrivial hβ hEnergy current f| +
            |finiteEvenFourTorusZ2PerronPosteriorGlobalExpectation
                H β energyIdentity energyNontrivial hβ hEnergy current f -
              finiteEvenFourTorusZ2PerronPosteriorGlobalExpectation
                H β energyIdentity energyNontrivial hβ hEnergy left f| :=
          abs_add_le _ _
        _ ≤
          finiteEvenFourTorusZ2PerronPosteriorObservableKernelResponseError
              H β energyIdentity energyNontrivial
              kernel iterations source P.variation +
            ∑ target ∈ s,
              finiteEvenFourTorusZ2PerronPosteriorObservableKernelResponseError
                H β energyIdentity energyNontrivial
                kernel iterations target P.variation :=
          add_le_add hOne (by simpa [current] using ih)
        _ = ∑ target ∈ insert source s,
              finiteEvenFourTorusZ2PerronPosteriorObservableKernelResponseError
                H β energyIdentity energyNontrivial
                kernel iterations target P.variation := by
          rw [Finset.sum_insert hSource]

/-- Arbitrary boundary environments are compared by summing response errors
only over the coordinates on which they actually disagree. -/
theorem
    finiteEvenFourTorusZ2PerronPosteriorGlobalExpectation_difference_abs_le_disagreementResponseSum
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (left right : FiniteEvenFourTorusZ2SliceConfiguration H)
    (f : FiniteEvenFourTorusZ2SliceConfiguration H → ℝ)
    (P : FiniteProductVariationBound f)
    (kernel :
      FiniteNonnegativeInfluenceKernelData
        (FiniteEvenFourTorusSpatialLink H))
    (iterations : ℕ)
    (hDomination :
      FiniteEvenFourTorusZ2PerronPosteriorCanonicalDominatedBy
        H β energyIdentity energyNontrivial hβ hEnergy kernel) :
    |finiteEvenFourTorusZ2PerronPosteriorGlobalExpectation
          H β energyIdentity energyNontrivial hβ hEnergy right f -
        finiteEvenFourTorusZ2PerronPosteriorGlobalExpectation
          H β energyIdentity energyNontrivial hβ hEnergy left f| ≤
      ∑ target ∈ finiteProductDisagreementFinset left right,
        finiteEvenFourTorusZ2PerronPosteriorObservableKernelResponseError
          H β energyIdentity energyNontrivial
          kernel iterations target P.variation := by
  simpa [finiteProductReplaceOn_disagreementFinset left right] using
    finiteEvenFourTorusZ2PerronPosteriorGlobalExpectation_replaceOn_difference_abs_le_sum
      H β energyIdentity energyNontrivial hβ hEnergy
      left right f P kernel iterations hDomination
      (finiteProductDisagreementFinset left right)

/-- A uniform one-coordinate response envelope yields a Hamming-Lipschitz
posterior expectation bound. -/
theorem
    finiteEvenFourTorusZ2PerronPosteriorGlobalExpectation_difference_abs_le_response_mul_hamming
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (left right : FiniteEvenFourTorusZ2SliceConfiguration H)
    (f : FiniteEvenFourTorusZ2SliceConfiguration H → ℝ)
    (P : FiniteProductVariationBound f)
    (kernel :
      FiniteNonnegativeInfluenceKernelData
        (FiniteEvenFourTorusSpatialLink H))
    (iterations : ℕ)
    (hDomination :
      FiniteEvenFourTorusZ2PerronPosteriorCanonicalDominatedBy
        H β energyIdentity energyNontrivial hβ hEnergy kernel)
    (response : ℝ)
    (hResponse :
      ∀ target : FiniteEvenFourTorusSpatialLink H,
        finiteEvenFourTorusZ2PerronPosteriorObservableKernelResponseError
            H β energyIdentity energyNontrivial
            kernel iterations target P.variation ≤ response) :
    |finiteEvenFourTorusZ2PerronPosteriorGlobalExpectation
          H β energyIdentity energyNontrivial hβ hEnergy right f -
        finiteEvenFourTorusZ2PerronPosteriorGlobalExpectation
          H β energyIdentity energyNontrivial hβ hEnergy left f| ≤
      response * finiteProductHammingDistanceReal left right := by
  have hPath :=
    finiteEvenFourTorusZ2PerronPosteriorGlobalExpectation_difference_abs_le_disagreementResponseSum
      H β energyIdentity energyNontrivial hβ hEnergy
      left right f P kernel iterations hDomination
  calc
    |finiteEvenFourTorusZ2PerronPosteriorGlobalExpectation
          H β energyIdentity energyNontrivial hβ hEnergy right f -
        finiteEvenFourTorusZ2PerronPosteriorGlobalExpectation
          H β energyIdentity energyNontrivial hβ hEnergy left f| ≤
      ∑ target ∈ finiteProductDisagreementFinset left right,
        finiteEvenFourTorusZ2PerronPosteriorObservableKernelResponseError
          H β energyIdentity energyNontrivial
          kernel iterations target P.variation := hPath
    _ ≤ ∑ _target ∈ finiteProductDisagreementFinset left right,
        response := by
      apply Finset.sum_le_sum
      intro target _hTarget
      exact hResponse target
    _ = response * finiteProductHammingDistanceReal left right := by
      unfold finiteProductHammingDistanceReal
      simp [nsmul_eq_mul]
      ring

/-- The same residual gauge transformation preserves the disagreement path,
so the posterior expectation response is controlled by the original Hamming
geometry. -/
theorem
    finiteEvenFourTorusZ2PerronPosteriorGlobalExpectation_sameResidualGauge_difference_abs_le_response_mul_hamming
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (left right : FiniteEvenFourTorusZ2SliceConfiguration H)
    (f : FiniteEvenFourTorusZ2SliceConfiguration H → ℝ)
    (P : FiniteProductVariationBound f)
    (kernel :
      FiniteNonnegativeInfluenceKernelData
        (FiniteEvenFourTorusSpatialLink H))
    (iterations : ℕ)
    (hDomination :
      FiniteEvenFourTorusZ2PerronPosteriorCanonicalDominatedBy
        H β energyIdentity energyNontrivial hβ hEnergy kernel)
    (response : ℝ)
    (hResponse :
      ∀ target : FiniteEvenFourTorusSpatialLink H,
        finiteEvenFourTorusZ2PerronPosteriorObservableKernelResponseError
            H β energyIdentity energyNontrivial
            kernel iterations target P.variation ≤ response) :
    |finiteEvenFourTorusZ2PerronPosteriorGlobalExpectation
          H β energyIdentity energyNontrivial hβ hEnergy (g • right) f -
        finiteEvenFourTorusZ2PerronPosteriorGlobalExpectation
          H β energyIdentity energyNontrivial hβ hEnergy (g • left) f| ≤
      response * finiteProductHammingDistanceReal left right := by
  have hBound :=
    finiteEvenFourTorusZ2PerronPosteriorGlobalExpectation_difference_abs_le_response_mul_hamming
      H β energyIdentity energyNontrivial hβ hEnergy
      (g • left) (g • right) f P kernel iterations hDomination
      response hResponse
  rw [finiteProductHammingDistanceReal_residualGauge_smul H g left right]
    at hBound
  exact hBound

end

end MathlibAnalytic
end MGAP4D
