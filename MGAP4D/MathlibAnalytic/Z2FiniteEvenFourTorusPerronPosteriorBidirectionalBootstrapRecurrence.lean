import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPerronPosteriorBidirectionalKernelResponse
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPerronPosteriorCanonicalKernelBootstrapClosure
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

local instance finiteEvenFourTorusSpatialLinkNonemptyForBidirectionalBootstrap
    (H : ℕ) : Nonempty (FiniteEvenFourTorusSpatialLink H) :=
  ⟨(⟨0, by simp⟩, ⟨1, by norm_num⟩)⟩

/-- Exact maximum row coefficient at one canonical bootstrap stage. -/
noncomputable def finiteEvenFourTorusZ2PerronPosteriorBootstrapRowCoefficient
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (responseIterations stage : ℕ) : ℝ :=
  finiteInfluenceKernelMaximumRowSum
    (finiteEvenFourTorusZ2PerronPosteriorCanonicalKernelBootstrap
      H β energyIdentity energyNontrivial hβ hEnergy
      responseIterations stage)

/-- The exact bootstrap row coefficient is nonnegative. -/
theorem finiteEvenFourTorusZ2PerronPosteriorBootstrapRowCoefficient_nonneg
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (responseIterations stage : ℕ) :
    0 ≤ finiteEvenFourTorusZ2PerronPosteriorBootstrapRowCoefficient
      H β energyIdentity energyNontrivial hβ hEnergy
      responseIterations stage := by
  unfold finiteEvenFourTorusZ2PerronPosteriorBootstrapRowCoefficient
  exact finiteInfluenceKernelMaximumRowSum_nonneg _

/-- Every row at a canonical stage is bounded by its exact maximum. -/
theorem finiteEvenFourTorusZ2PerronPosteriorBootstrapRowSum_le
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (responseIterations stage : ℕ)
    (target : FiniteEvenFourTorusSpatialLink H) :
    finiteInfluenceKernelRowSum
        (finiteEvenFourTorusZ2PerronPosteriorCanonicalKernelBootstrap
          H β energyIdentity energyNontrivial hβ hEnergy
          responseIterations stage)
        target ≤
      finiteEvenFourTorusZ2PerronPosteriorBootstrapRowCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy
        responseIterations stage :=
  finiteInfluenceKernelRowSum_le_maximum _ target

/-- Scalar finite-response bootstrap map.  Unlike the strict resolvent
coefficient, this formula is valid for every nonnegative row or column
coefficient. -/
noncomputable def finiteEvenFourTorusZ2PerronPosteriorFiniteBootstrapMap
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (responseIterations : ℕ)
    (coefficient : ℝ) : ℝ :=
  2 * finiteEvenFourTorusZ2PerronPosteriorLocalCoefficient
      β energyIdentity energyNontrivial +
    finiteZ2CrossingLikelihoodRatio
        (z2WilsonTemporalCrossingRate
          β energyIdentity energyNontrivial) *
      finiteEvenFourTorusZ2PerronPosteriorKernelFiniteResponseCoefficient
        H β energyIdentity energyNontrivial
        responseIterations coefficient

/-- The finite bootstrap map is nonnegative on nonnegative coefficients. -/
theorem finiteEvenFourTorusZ2PerronPosteriorFiniteBootstrapMap_nonneg
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (responseIterations : ℕ)
    (coefficient : ℝ)
    (hCoefficient : 0 ≤ coefficient) :
    0 ≤ finiteEvenFourTorusZ2PerronPosteriorFiniteBootstrapMap
      H β energyIdentity energyNontrivial responseIterations coefficient := by
  have hRatio :
      0 ≤ finiteZ2CrossingLikelihoodRatio
        (z2WilsonTemporalCrossingRate
          β energyIdentity energyNontrivial) :=
    le_of_lt
      (finiteZ2CrossingLikelihoodRatio_pos
        (z2WilsonTemporalCrossingRate_pos hβ hEnergy).le
        (z2WilsonTemporalCrossingRate_lt_one hβ hEnergy))
  unfold finiteEvenFourTorusZ2PerronPosteriorFiniteBootstrapMap
  exact add_nonneg
    (mul_nonneg (by norm_num)
      (finiteEvenFourTorusZ2PerronPosteriorLocalCoefficient_nonneg
        β energyIdentity energyNontrivial hβ.le hEnergy.le))
    (mul_nonneg hRatio
      (finiteEvenFourTorusZ2PerronPosteriorKernelFiniteResponseCoefficient_nonneg
        H β energyIdentity energyNontrivial hβ hEnergy
        responseIterations coefficient hCoefficient))

/-- A column coefficient of the input kernel controls every row of one
bootstrap successor through the finite response map. -/
theorem finiteEvenFourTorusZ2PerronPosteriorKernelBootstrapNext_rowSum_le
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (kernel :
      FiniteNonnegativeInfluenceKernelData
        (FiniteEvenFourTorusSpatialLink H))
    (responseIterations : ℕ)
    (columnCoefficient : ℝ)
    (hColumnNonneg : 0 ≤ columnCoefficient)
    (hColumnSum :
      ∀ source : FiniteEvenFourTorusSpatialLink H,
        finiteInfluenceKernelColumnSum kernel source ≤ columnCoefficient)
    (target : FiniteEvenFourTorusSpatialLink H) :
    finiteInfluenceKernelRowSum
        (finiteEvenFourTorusZ2PerronPosteriorKernelBootstrapNext
          H β energyIdentity energyNontrivial hβ hEnergy
          kernel responseIterations)
        target ≤
      finiteEvenFourTorusZ2PerronPosteriorFiniteBootstrapMap
        H β energyIdentity energyNontrivial
        responseIterations columnCoefficient := by
  let ratio :=
    finiteZ2CrossingLikelihoodRatio
      (z2WilsonTemporalCrossingRate
        β energyIdentity energyNontrivial)
  have hRatio : 0 ≤ ratio :=
    le_of_lt
      (finiteZ2CrossingLikelihoodRatio_pos
        (z2WilsonTemporalCrossingRate_pos hβ hEnergy).le
        (z2WilsonTemporalCrossingRate_lt_one hβ hEnergy))
  have hPointwise :
      ∀ source : FiniteEvenFourTorusSpatialLink H,
        (finiteEvenFourTorusZ2PerronPosteriorKernelBootstrapNext
            H β energyIdentity energyNontrivial hβ hEnergy
            kernel responseIterations).influence target source ≤
          2 *
              finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluence
                H β energyIdentity energyNontrivial target source +
            ratio *
              finiteEvenFourTorusZ2PerronPosteriorKernelResponseError
                H β energyIdentity energyNontrivial
                kernel responseIterations target source := by
    intro source
    by_cases hEq : target = source
    · rw [hEq]
      simp [finiteEvenFourTorusZ2PerronPosteriorKernelBootstrapNext]
      exact add_nonneg
        (mul_nonneg (by norm_num)
          (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluence_nonneg
            H β energyIdentity energyNontrivial hβ.le hEnergy.le source source))
        (mul_nonneg hRatio
          (finiteEvenFourTorusZ2PerronPosteriorKernelResponseError_nonneg
            H β energyIdentity energyNontrivial hβ hEnergy
            kernel responseIterations source source))
    · simp [finiteEvenFourTorusZ2PerronPosteriorKernelBootstrapNext,
        ratio, hEq]
  have hLocal :=
    finiteEvenFourTorusZ2PerronPosteriorLocalRowSum_le_coefficient
      H β energyIdentity energyNontrivial hβ.le hEnergy.le target
  have hResponse :=
    finiteEvenFourTorusZ2PerronPosteriorKernelResponseErrorRowSum_le
      H β energyIdentity energyNontrivial hβ hEnergy
      kernel responseIterations columnCoefficient
      hColumnNonneg hColumnSum target
  unfold finiteInfluenceKernelRowSum
  calc
    (∑ source : FiniteEvenFourTorusSpatialLink H,
      (finiteEvenFourTorusZ2PerronPosteriorKernelBootstrapNext
        H β energyIdentity energyNontrivial hβ hEnergy
        kernel responseIterations).influence target source) ≤
      ∑ source : FiniteEvenFourTorusSpatialLink H,
        (2 *
            finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluence
              H β energyIdentity energyNontrivial target source +
          ratio *
            finiteEvenFourTorusZ2PerronPosteriorKernelResponseError
              H β energyIdentity energyNontrivial
              kernel responseIterations target source) := by
        apply Finset.sum_le_sum
        intro source _
        exact hPointwise source
    _ = 2 *
          finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluenceRowSum
            H β energyIdentity energyNontrivial target +
        ratio *
          (∑ source : FiniteEvenFourTorusSpatialLink H,
            finiteEvenFourTorusZ2PerronPosteriorKernelResponseError
              H β energyIdentity energyNontrivial
              kernel responseIterations target source) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        rfl
    _ ≤ 2 * finiteEvenFourTorusZ2PerronPosteriorLocalCoefficient
          β energyIdentity energyNontrivial +
        ratio *
          finiteEvenFourTorusZ2PerronPosteriorKernelFiniteResponseCoefficient
            H β energyIdentity energyNontrivial
            responseIterations columnCoefficient :=
      add_le_add
        (mul_le_mul_of_nonneg_left hLocal (by norm_num))
        (mul_le_mul_of_nonneg_left hResponse hRatio)
    _ = finiteEvenFourTorusZ2PerronPosteriorFiniteBootstrapMap
        H β energyIdentity energyNontrivial
        responseIterations columnCoefficient := rfl

/-- A row coefficient of the input kernel controls every column of one
bootstrap successor through the same finite response map. -/
theorem finiteEvenFourTorusZ2PerronPosteriorKernelBootstrapNext_columnSum_le
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (kernel :
      FiniteNonnegativeInfluenceKernelData
        (FiniteEvenFourTorusSpatialLink H))
    (responseIterations : ℕ)
    (rowCoefficient : ℝ)
    (hRowNonneg : 0 ≤ rowCoefficient)
    (hRowSum :
      ∀ target : FiniteEvenFourTorusSpatialLink H,
        finiteInfluenceKernelRowSum kernel target ≤ rowCoefficient)
    (source : FiniteEvenFourTorusSpatialLink H) :
    finiteInfluenceKernelColumnSum
        (finiteEvenFourTorusZ2PerronPosteriorKernelBootstrapNext
          H β energyIdentity energyNontrivial hβ hEnergy
          kernel responseIterations)
        source ≤
      finiteEvenFourTorusZ2PerronPosteriorFiniteBootstrapMap
        H β energyIdentity energyNontrivial
        responseIterations rowCoefficient := by
  let ratio :=
    finiteZ2CrossingLikelihoodRatio
      (z2WilsonTemporalCrossingRate
        β energyIdentity energyNontrivial)
  have hRatio : 0 ≤ ratio :=
    le_of_lt
      (finiteZ2CrossingLikelihoodRatio_pos
        (z2WilsonTemporalCrossingRate_pos hβ hEnergy).le
        (z2WilsonTemporalCrossingRate_lt_one hβ hEnergy))
  have hPointwise :
      ∀ target : FiniteEvenFourTorusSpatialLink H,
        (finiteEvenFourTorusZ2PerronPosteriorKernelBootstrapNext
            H β energyIdentity energyNontrivial hβ hEnergy
            kernel responseIterations).influence target source ≤
          2 *
              finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluence
                H β energyIdentity energyNontrivial target source +
            ratio *
              finiteEvenFourTorusZ2PerronPosteriorKernelResponseError
                H β energyIdentity energyNontrivial
                kernel responseIterations target source := by
    intro target
    by_cases hEq : target = source
    · subst target
      simp [finiteEvenFourTorusZ2PerronPosteriorKernelBootstrapNext]
      exact add_nonneg
        (mul_nonneg (by norm_num)
          (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluence_nonneg
            H β energyIdentity energyNontrivial hβ.le hEnergy.le source source))
        (mul_nonneg hRatio
          (finiteEvenFourTorusZ2PerronPosteriorKernelResponseError_nonneg
            H β energyIdentity energyNontrivial hβ hEnergy
            kernel responseIterations source source))
    · simp [finiteEvenFourTorusZ2PerronPosteriorKernelBootstrapNext,
        ratio, hEq]
  have hLocal :=
    finiteEvenFourTorusZ2PerronPosteriorLocalInfluenceColumnSum_le
      H β energyIdentity energyNontrivial hβ.le hEnergy.le source
  have hResponse :=
    finiteEvenFourTorusZ2PerronPosteriorKernelResponseErrorColumnSum_le
      H β energyIdentity energyNontrivial hβ hEnergy
      kernel responseIterations rowCoefficient
      hRowNonneg hRowSum source
  unfold finiteInfluenceKernelColumnSum
  calc
    (∑ target : FiniteEvenFourTorusSpatialLink H,
      (finiteEvenFourTorusZ2PerronPosteriorKernelBootstrapNext
        H β energyIdentity energyNontrivial hβ hEnergy
        kernel responseIterations).influence target source) ≤
      ∑ target : FiniteEvenFourTorusSpatialLink H,
        (2 *
            finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluence
              H β energyIdentity energyNontrivial target source +
          ratio *
            finiteEvenFourTorusZ2PerronPosteriorKernelResponseError
              H β energyIdentity energyNontrivial
              kernel responseIterations target source) := by
        apply Finset.sum_le_sum
        intro target _
        exact hPointwise target
    _ = 2 *
          (∑ target : FiniteEvenFourTorusSpatialLink H,
            finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorLocalInfluence
              H β energyIdentity energyNontrivial target source) +
        ratio *
          (∑ target : FiniteEvenFourTorusSpatialLink H,
            finiteEvenFourTorusZ2PerronPosteriorKernelResponseError
              H β energyIdentity energyNontrivial
              kernel responseIterations target source) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ 2 * finiteEvenFourTorusZ2PerronPosteriorLocalCoefficient
          β energyIdentity energyNontrivial +
        ratio *
          finiteEvenFourTorusZ2PerronPosteriorKernelFiniteResponseCoefficient
            H β energyIdentity energyNontrivial
            responseIterations rowCoefficient :=
      add_le_add
        (mul_le_mul_of_nonneg_left hLocal (by norm_num))
        (mul_le_mul_of_nonneg_left hResponse hRatio)
    _ = finiteEvenFourTorusZ2PerronPosteriorFiniteBootstrapMap
        H β energyIdentity energyNontrivial
        responseIterations rowCoefficient := rfl

/-- Canonical maximum-row recurrence: the next row coefficient is controlled
by the current maximum column coefficient. -/
theorem finiteEvenFourTorusZ2PerronPosteriorBootstrapRowCoefficient_succ_le
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (responseIterations stage : ℕ) :
    finiteEvenFourTorusZ2PerronPosteriorBootstrapRowCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy
        responseIterations (stage + 1) ≤
      finiteEvenFourTorusZ2PerronPosteriorFiniteBootstrapMap
        H β energyIdentity energyNontrivial responseIterations
        (finiteEvenFourTorusZ2PerronPosteriorBootstrapColumnCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy
          responseIterations stage) := by
  unfold finiteEvenFourTorusZ2PerronPosteriorBootstrapRowCoefficient
  rw [finiteEvenFourTorusZ2PerronPosteriorCanonicalKernelBootstrap_succ]
  apply finiteInfluenceKernelMaximumRowSum_le_of_forall
  intro target
  exact finiteEvenFourTorusZ2PerronPosteriorKernelBootstrapNext_rowSum_le
    H β energyIdentity energyNontrivial hβ hEnergy
    (finiteEvenFourTorusZ2PerronPosteriorCanonicalKernelBootstrap
      H β energyIdentity energyNontrivial hβ hEnergy
      responseIterations stage)
    responseIterations
    (finiteEvenFourTorusZ2PerronPosteriorBootstrapColumnCoefficient
      H β energyIdentity energyNontrivial hβ hEnergy
      responseIterations stage)
    (finiteEvenFourTorusZ2PerronPosteriorBootstrapColumnCoefficient_nonneg
      H β energyIdentity energyNontrivial hβ hEnergy
      responseIterations stage)
    (finiteEvenFourTorusZ2PerronPosteriorBootstrapColumnSum_le
      H β energyIdentity energyNontrivial hβ hEnergy
      responseIterations stage)
    target

/-- Canonical maximum-column recurrence: the next column coefficient is
controlled by the current maximum row coefficient. -/
theorem finiteEvenFourTorusZ2PerronPosteriorBootstrapColumnCoefficient_succ_le
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (responseIterations stage : ℕ) :
    finiteEvenFourTorusZ2PerronPosteriorBootstrapColumnCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy
        responseIterations (stage + 1) ≤
      finiteEvenFourTorusZ2PerronPosteriorFiniteBootstrapMap
        H β energyIdentity energyNontrivial responseIterations
        (finiteEvenFourTorusZ2PerronPosteriorBootstrapRowCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy
          responseIterations stage) := by
  unfold finiteEvenFourTorusZ2PerronPosteriorBootstrapColumnCoefficient
  rw [finiteEvenFourTorusZ2PerronPosteriorCanonicalKernelBootstrap_succ]
  apply finiteInfluenceKernelMaximumColumnSum_le_of_forall
  intro source
  exact finiteEvenFourTorusZ2PerronPosteriorKernelBootstrapNext_columnSum_le
    H β energyIdentity energyNontrivial hβ hEnergy
    (finiteEvenFourTorusZ2PerronPosteriorCanonicalKernelBootstrap
      H β energyIdentity energyNontrivial hβ hEnergy
      responseIterations stage)
    responseIterations
    (finiteEvenFourTorusZ2PerronPosteriorBootstrapRowCoefficient
      H β energyIdentity energyNontrivial hβ hEnergy
      responseIterations stage)
    (finiteEvenFourTorusZ2PerronPosteriorBootstrapRowCoefficient_nonneg
      H β energyIdentity energyNontrivial hβ hEnergy
      responseIterations stage)
    (finiteEvenFourTorusZ2PerronPosteriorBootstrapRowSum_le
      H β energyIdentity energyNontrivial hβ hEnergy
      responseIterations stage)
    source

/-- Proof-relevant one-step strictness certificate for the bidirectional
canonical recurrence. -/
structure Z2PerronPosteriorBidirectionalBootstrapStepCertificate
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) where
  responseIterations : ℕ
  stage : ℕ
  rowCoefficient_lt_one :
    finiteEvenFourTorusZ2PerronPosteriorBootstrapRowCoefficient
      H β energyIdentity energyNontrivial hβ hEnergy
      responseIterations stage < 1
  columnCoefficient_lt_one :
    finiteEvenFourTorusZ2PerronPosteriorBootstrapColumnCoefficient
      H β energyIdentity energyNontrivial hβ hEnergy
      responseIterations stage < 1
  nextRowBound_lt_one :
    finiteEvenFourTorusZ2PerronPosteriorFiniteBootstrapMap
      H β energyIdentity energyNontrivial responseIterations
      (finiteEvenFourTorusZ2PerronPosteriorBootstrapColumnCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy
        responseIterations stage) < 1
  nextColumnBound_lt_one :
    finiteEvenFourTorusZ2PerronPosteriorFiniteBootstrapMap
      H β energyIdentity energyNontrivial responseIterations
      (finiteEvenFourTorusZ2PerronPosteriorBootstrapRowCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy
        responseIterations stage) < 1

namespace Z2PerronPosteriorBidirectionalBootstrapStepCertificate

variable
    {H : ℕ}
    {β energyIdentity energyNontrivial : ℝ}
    {hβ : 0 < β}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorBidirectionalBootstrapStepCertificate
      H β energyIdentity energyNontrivial hβ hEnergy)

/-- The successor canonical row coefficient is strict. -/
theorem successorRowCoefficient_lt_one :
    finiteEvenFourTorusZ2PerronPosteriorBootstrapRowCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy
        C.responseIterations (C.stage + 1) < 1 :=
  lt_of_le_of_lt
    (finiteEvenFourTorusZ2PerronPosteriorBootstrapRowCoefficient_succ_le
      H β energyIdentity energyNontrivial hβ hEnergy
      C.responseIterations C.stage)
    C.nextRowBound_lt_one

/-- The successor canonical column coefficient is strict. -/
theorem successorColumnCoefficient_lt_one :
    finiteEvenFourTorusZ2PerronPosteriorBootstrapColumnCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy
        C.responseIterations (C.stage + 1) < 1 :=
  lt_of_le_of_lt
    (finiteEvenFourTorusZ2PerronPosteriorBootstrapColumnCoefficient_succ_le
      H β energyIdentity energyNontrivial hβ hEnergy
      C.responseIterations C.stage)
    C.nextColumnBound_lt_one

end Z2PerronPosteriorBidirectionalBootstrapStepCertificate

end

end MathlibAnalytic
end MGAP4D
