import MGAP4D.MathlibAnalytic.FinitePositiveKernelNormalizerTiltCrossRatio
import MGAP4D.MathlibAnalytic.FinitePositiveWeightLocalTiltConditional
import MGAP4D.MathlibAnalytic.FinitePositiveWeightStationaryRandomScanComparison
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Unnormalized finite-product weight whose normalized global law is the
hidden-state posterior associated with one observed environment. -/
def finitePositiveKernelPosteriorWeight
    {ι G E : Type}
    (kernel : (ι → G) → E → ℝ)
    (hiddenWeight : (ι → G) → ℝ)
    (environment : E)
    (hidden : ι → G) : ℝ :=
  kernel hidden environment * hiddenWeight hidden

/-- Positivity of the kernel and hidden weight gives positivity of every
posterior-weight atom. -/
theorem finitePositiveKernelPosteriorWeight_pos
    {ι G E : Type}
    (kernel : (ι → G) → E → ℝ)
    (hiddenWeight : (ι → G) → ℝ)
    (hKernel : ∀ hidden environment, 0 < kernel hidden environment)
    (hHiddenWeight : ∀ hidden, 0 < hiddenWeight hidden)
    (environment : E)
    (hidden : ι → G) :
    0 < finitePositiveKernelPosteriorWeight
      kernel hiddenWeight environment hidden := by
  exact mul_pos (hKernel hidden environment) (hHiddenWeight hidden)

/-- The total mass of the posterior weight is exactly the positive-kernel
normalizer. -/
theorem finitePositiveKernelPosteriorWeight_totalMass_eq_normalizer
    {ι G E : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (kernel : (ι → G) → E → ℝ)
    (hiddenWeight : (ι → G) → ℝ)
    (environment : E) :
    finitePositiveWeightTotalMass
        (finitePositiveKernelPosteriorWeight
          kernel hiddenWeight environment) =
      finitePositiveKernelNormalizer kernel hiddenWeight environment := by
  rfl

/-- The normalized global law of the posterior weight agrees atomwise with
the finite positive kernel posterior. -/
theorem finitePositiveKernelPosteriorWeight_globalProbability_eq_posterior
    {ι G E : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (kernel : (ι → G) → E → ℝ)
    (hiddenWeight : (ι → G) → ℝ)
    (environment : E)
    (hidden : ι → G) :
    finitePositiveWeightGlobalProbability
        (finitePositiveKernelPosteriorWeight
          kernel hiddenWeight environment)
        hidden =
      finitePositiveKernelPosterior
        kernel hiddenWeight environment hidden := by
  rfl

/-- Posterior tilt expectation is exactly normalized positive-weight global
expectation for the corresponding posterior weight. -/
theorem finitePositiveKernelPosteriorWeight_globalExpectation_eq_tiltExpectation
    {ι G E : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (kernel : (ι → G) → E → ℝ)
    (hiddenWeight : (ι → G) → ℝ)
    (environment : E)
    (observable : (ι → G) → ℝ) :
    finitePositiveWeightGlobalExpectation
        (finitePositiveKernelPosteriorWeight
          kernel hiddenWeight environment)
        observable =
      finitePositiveKernelTiltExpectation
        kernel hiddenWeight environment observable := by
  rfl

/-- A multiplicative boundary Radon--Nikodym relation between two kernel
columns becomes the exact multiplicative-tilt relation between their
unnormalized posterior weights. -/
theorem finitePositiveKernelPosteriorWeight_eq_multiplicativeTilt
    {ι G E : Type}
    (kernel : (ι → G) → E → ℝ)
    (hiddenWeight : (ι → G) → ℝ)
    (base updated : E)
    (tilt : (ι → G) → ℝ)
    (hRelation :
      FinitePositiveKernelBoundaryTiltRelation
        kernel base updated tilt) :
    finitePositiveKernelPosteriorWeight
        kernel hiddenWeight updated =
      finitePositiveWeightMultiplicativeTilt
        (finitePositiveKernelPosteriorWeight
          kernel hiddenWeight base)
        tilt := by
  funext hidden
  unfold finitePositiveKernelPosteriorWeight
    finitePositiveWeightMultiplicativeTilt
  rw [hRelation hidden]
  ring

/-- A bounded local boundary tilt gives the corresponding finite-support
cross-weight single-site conditional source bound for the two hidden
posterior weights. -/
theorem finitePositiveKernelPosteriorWeight_singleSiteConditionalCrossL1_le_sourceBound
    {ι G E : Type} [DecidableEq ι] [Fintype G] [Nonempty G]
    (kernel : (ι → G) → E → ℝ) (hiddenWeight : (ι → G) → ℝ)
    (hKernel : ∀ hidden environment, 0 < kernel hidden environment)
    (hHiddenWeight : ∀ hidden, 0 < hiddenWeight hidden)
    (base updated : E) (tilt : (ι → G) → ℝ)
    (hRelation : FinitePositiveKernelBoundaryTiltRelation
      kernel base updated tilt)
    (htilt : ∀ hidden, 0 < tilt hidden)
    (support : Finset ι)
    (htiltSupport : FiniteProductFunctionSupportedOn support tilt)
    (lower upper : ℝ) (hLower : 0 < lower) (hUpper : 0 < upper)
    (hLowerUpper : lower ≤ upper)
    (htiltLower : ∀ hidden, lower ≤ tilt hidden)
    (htiltUpper : ∀ hidden, tilt hidden ≤ upper)
    (environment : ι → G) (target : ι) :
    finitePositiveWeightSingleSiteConditionalCrossL1
        (finitePositiveKernelPosteriorWeight
          kernel hiddenWeight updated)
        (finitePositiveKernelPosteriorWeight
          kernel hiddenWeight base)
        environment target ≤
      finitePositiveWeightLocalTiltConditionalSourceBound
        support lower upper target := by
  rw [finitePositiveKernelPosteriorWeight_eq_multiplicativeTilt
    kernel hiddenWeight base updated tilt hRelation]
  exact
    finitePositiveWeightMultiplicativeTilt_singleSiteConditionalCrossL1_le_sourceBound
      (finitePositiveKernelPosteriorWeight
        kernel hiddenWeight base)
      tilt
      (finitePositiveKernelPosteriorWeight_pos
        kernel hiddenWeight hKernel hHiddenWeight base)
      htilt support htiltSupport lower upper
      hLower hUpper hLowerUpper htiltLower htiltUpper
      environment target

end

end MathlibAnalytic
end MGAP4D
