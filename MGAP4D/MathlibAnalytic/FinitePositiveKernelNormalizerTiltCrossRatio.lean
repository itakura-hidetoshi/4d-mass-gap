import MGAP4D.MathlibAnalytic.FinitePositiveWeightConditionalCrossRatioInfluence
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Total unnormalized mass obtained by summing a finite positive kernel
against a positive hidden-state weight. -/
def finitePositiveKernelNormalizer
    {Ω E : Type}
    [Fintype Ω]
    (kernel : Ω → E → ℝ)
    (weight : Ω → ℝ)
    (environment : E) : ℝ :=
  ∑ hidden : Ω, kernel hidden environment * weight hidden

/-- Normalized hidden-state posterior associated with one environment. -/
def finitePositiveKernelPosterior
    {Ω E : Type}
    [Fintype Ω]
    (kernel : Ω → E → ℝ)
    (weight : Ω → ℝ)
    (environment : E)
    (hidden : Ω) : ℝ :=
  kernel hidden environment * weight hidden /
    finitePositiveKernelNormalizer kernel weight environment

/-- Posterior expectation of a boundary Radon--Nikodym tilt. -/
def finitePositiveKernelTiltExpectation
    {Ω E : Type}
    [Fintype Ω]
    (kernel : Ω → E → ℝ)
    (weight : Ω → ℝ)
    (environment : E)
    (tilt : Ω → ℝ) : ℝ :=
  ∑ hidden : Ω,
    finitePositiveKernelPosterior kernel weight environment hidden *
      tilt hidden

/-- A boundary update is represented by a hidden-state multiplicative tilt
when the updated kernel column is the original column times `tilt`. -/
def FinitePositiveKernelBoundaryTiltRelation
    {Ω E : Type}
    (kernel : Ω → E → ℝ)
    (base updated : E)
    (tilt : Ω → ℝ) : Prop :=
  ∀ hidden : Ω,
    kernel hidden updated = tilt hidden * kernel hidden base

/-- Strict positivity of every kernel entry and every hidden weight gives a
strictly positive finite normalizer. -/
theorem finitePositiveKernelNormalizer_pos
    {Ω E : Type}
    [Fintype Ω]
    [Nonempty Ω]
    (kernel : Ω → E → ℝ)
    (weight : Ω → ℝ)
    (hKernel : ∀ hidden environment, 0 < kernel hidden environment)
    (hWeight : ∀ hidden, 0 < weight hidden)
    (environment : E) :
    0 < finitePositiveKernelNormalizer kernel weight environment := by
  classical
  unfold finitePositiveKernelNormalizer
  apply Finset.sum_pos
  · intro hidden _hHidden
    exact mul_pos (hKernel hidden environment) (hWeight hidden)
  · let hidden : Ω := Classical.choice inferInstance
    exact ⟨hidden, Finset.mem_univ hidden⟩

/-- Every finite positive kernel posterior atom is strictly positive. -/
theorem finitePositiveKernelPosterior_pos
    {Ω E : Type}
    [Fintype Ω]
    [Nonempty Ω]
    (kernel : Ω → E → ℝ)
    (weight : Ω → ℝ)
    (hKernel : ∀ hidden environment, 0 < kernel hidden environment)
    (hWeight : ∀ hidden, 0 < weight hidden)
    (environment : E)
    (hidden : Ω) :
    0 < finitePositiveKernelPosterior kernel weight environment hidden := by
  unfold finitePositiveKernelPosterior
  exact div_pos
    (mul_pos (hKernel hidden environment) (hWeight hidden))
    (finitePositiveKernelNormalizer_pos
      kernel weight hKernel hWeight environment)

/-- The finite positive kernel posterior has total mass one. -/
theorem finitePositiveKernelPosterior_sum_eq_one
    {Ω E : Type}
    [Fintype Ω]
    [Nonempty Ω]
    (kernel : Ω → E → ℝ)
    (weight : Ω → ℝ)
    (hKernel : ∀ hidden environment, 0 < kernel hidden environment)
    (hWeight : ∀ hidden, 0 < weight hidden)
    (environment : E) :
    (∑ hidden : Ω,
      finitePositiveKernelPosterior kernel weight environment hidden) = 1 := by
  unfold finitePositiveKernelPosterior
  rw [← Finset.sum_div]
  change
    finitePositiveKernelNormalizer kernel weight environment /
        finitePositiveKernelNormalizer kernel weight environment = 1
  exact div_self
    (ne_of_gt
      (finitePositiveKernelNormalizer_pos
        kernel weight hKernel hWeight environment))

/-- A multiplicative boundary tilt converts the updated normalizer exactly
into the original normalizer times the posterior tilt expectation. -/
theorem finitePositiveKernelNormalizer_eq_mul_tiltExpectation
    {Ω E : Type}
    [Fintype Ω]
    [Nonempty Ω]
    (kernel : Ω → E → ℝ)
    (weight : Ω → ℝ)
    (hKernel : ∀ hidden environment, 0 < kernel hidden environment)
    (hWeight : ∀ hidden, 0 < weight hidden)
    (base updated : E)
    (tilt : Ω → ℝ)
    (hRelation :
      FinitePositiveKernelBoundaryTiltRelation kernel base updated tilt) :
    finitePositiveKernelNormalizer kernel weight updated =
      finitePositiveKernelNormalizer kernel weight base *
        finitePositiveKernelTiltExpectation
          kernel weight base tilt := by
  classical
  let normalizer := finitePositiveKernelNormalizer kernel weight base
  have hNormalizerPos : 0 < normalizer := by
    exact finitePositiveKernelNormalizer_pos
      kernel weight hKernel hWeight base
  have hNormalizerNe : normalizer ≠ 0 := ne_of_gt hNormalizerPos
  change
    (∑ hidden : Ω, kernel hidden updated * weight hidden) =
      normalizer *
        (∑ hidden : Ω,
          (kernel hidden base * weight hidden / normalizer) * tilt hidden)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro hidden _hHidden
  rw [hRelation hidden]
  field_simp [hNormalizerNe]

/-- A rowwise comparison of posterior tilt expectations implies the exact
four-point cross-ratio bound for the corresponding kernel normalizer.  This
isolates the remaining analysis in a normalized expectation comparison. -/
theorem finitePositiveKernelNormalizer_crossRatio_of_tiltExpectation
    {Ω ι G : Type}
    [Fintype Ω]
    [Nonempty Ω]
    [DecidableEq ι]
    [Fintype G]
    (kernel : Ω → (ι → G) → ℝ)
    (weight : Ω → ℝ)
    (hKernel : ∀ hidden environment, 0 < kernel hidden environment)
    (hWeight : ∀ hidden, 0 < weight hidden)
    (A C : ι → G)
    (target : ι)
    (tilt : Ω → ℝ)
    (ratio : ℝ)
    (hRelation :
      ∀ value : G,
        FinitePositiveKernelBoundaryTiltRelation kernel
          (Function.update A target value)
          (Function.update C target value)
          tilt)
    (hExpectation :
      ∀ g h : G,
        finitePositiveKernelTiltExpectation kernel weight
            (Function.update A target h) tilt ≤
          ratio *
            finitePositiveKernelTiltExpectation kernel weight
              (Function.update A target g) tilt) :
    FinitePositiveWeightSingleSiteCrossRatioBound
      (finitePositiveKernelNormalizer kernel weight)
      A C target ratio := by
  intro g h
  have hUpdatedH :=
    finitePositiveKernelNormalizer_eq_mul_tiltExpectation
      kernel weight hKernel hWeight
      (Function.update A target h)
      (Function.update C target h)
      tilt (hRelation h)
  have hUpdatedG :=
    finitePositiveKernelNormalizer_eq_mul_tiltExpectation
      kernel weight hKernel hWeight
      (Function.update A target g)
      (Function.update C target g)
      tilt (hRelation g)
  rw [hUpdatedH, hUpdatedG]
  let normalizerG :=
    finitePositiveKernelNormalizer kernel weight
      (Function.update A target g)
  let normalizerH :=
    finitePositiveKernelNormalizer kernel weight
      (Function.update A target h)
  have hNormalizerG : 0 ≤ normalizerG :=
    le_of_lt
      (finitePositiveKernelNormalizer_pos
        kernel weight hKernel hWeight (Function.update A target g))
  have hNormalizerH : 0 ≤ normalizerH :=
    le_of_lt
      (finitePositiveKernelNormalizer_pos
        kernel weight hKernel hWeight (Function.update A target h))
  calc
    normalizerG *
        (normalizerH *
          finitePositiveKernelTiltExpectation kernel weight
            (Function.update A target h) tilt) =
      (normalizerG * normalizerH) *
        finitePositiveKernelTiltExpectation kernel weight
          (Function.update A target h) tilt := by ring
    _ ≤ (normalizerG * normalizerH) *
        (ratio *
          finitePositiveKernelTiltExpectation kernel weight
            (Function.update A target g) tilt) :=
      mul_le_mul_of_nonneg_left (hExpectation g h)
        (mul_nonneg hNormalizerG hNormalizerH)
    _ = ratio *
        ((normalizerG *
          finitePositiveKernelTiltExpectation kernel weight
            (Function.update A target g) tilt) * normalizerH) := by ring

end

end MathlibAnalytic
end MGAP4D
