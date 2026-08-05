import MGAP4D.MathlibAnalytic.FiniteRealProbabilityMixtureCoupling
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeDoobPosteriorPerronSmoothedMixtureProbability
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Canonical overlap coupling of the two latent residual-gauge index laws. -/
noncomputable def
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexCouplingData
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (left right : FiniteEvenFourTorusZ2SliceConfiguration H) :
    FiniteRealCouplingData
      (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexProbabilityData
        C β hβ hβCutoff H left)
      (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexProbabilityData
        C β hβ hβCutoff H right) :=
  (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexProbabilityData
    C β hβ hβCutoff H left).overlapCouplingData
    (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexProbabilityData
      C β hβ hβCutoff H right)

/-- Canonical overlap coupling of any left/right pair of normalized
Perron-smoothed posterior components. -/
noncomputable def
    finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentCouplingData
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (left right : FiniteEvenFourTorusZ2SliceConfiguration H)
    (g h : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H) :
    FiniteRealCouplingData
      (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentProbabilityData
        C β hβ hβCutoff H left g)
      (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentProbabilityData
        C β hβ hβCutoff H right h) :=
  (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentProbabilityData
    C β hβ hβCutoff H left g).overlapCouplingData
    (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentProbabilityData
      C β hβ hβCutoff H right h)

/-- Full-state joint law obtained by coupling the residual-gauge latent indices
and then coupling the selected Perron-smoothed posterior components. -/
def finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureCoupling
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (left right x y : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  finiteRealProbabilityMixtureCoupling
    (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexCouplingData
      C β hβ hβCutoff H left right)
    (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentCouplingData
      C β hβ hβCutoff H left right)
    x y

/-- The actual full-state Doob mixture coupling is nonnegative. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureCoupling_nonneg
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (left right x y : FiniteEvenFourTorusZ2SliceConfiguration H) :
    0 ≤ finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureCoupling
      C β hβ hβCutoff H left right x y := by
  exact finiteRealProbabilityMixtureCoupling_nonneg
    (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexCouplingData
      C β hβ hβCutoff H left right)
    (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentCouplingData
      C β hβ hβCutoff H left right)
    x y

/-- The left marginal is exactly the left geometric one-slab Doob row. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureCoupling_leftMarginal
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (left right x : FiniteEvenFourTorusZ2SliceConfiguration H) :
    ∑ y : FiniteEvenFourTorusZ2SliceConfiguration H,
      finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureCoupling
        C β hβ hβCutoff H left right x y =
      finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobKernel
        H β energyIdentity energyNontrivial hβ.le hEnergy.le x left := by
  calc
    (∑ y : FiniteEvenFourTorusZ2SliceConfiguration H,
      finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureCoupling
        C β hβ hβCutoff H left right x y) =
      (finiteRealProbabilityMixtureData
        (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexProbabilityData
          C β hβ hβCutoff H left)
        (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentProbabilityData
          C β hβ hβCutoff H left)).probability x := by
      exact finiteRealProbabilityMixtureCoupling_leftMarginal
        (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexCouplingData
          C β hβ hβCutoff H left right)
        (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentCouplingData
          C β hβ hβCutoff H left right)
        x
    _ = finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobKernel
        H β energyIdentity energyNontrivial hβ.le hEnergy.le x left := by
      symm
      simpa [finiteRealProbabilityMixtureData] using
        finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobKernel_eq_residualGaugePerronSmoothedMixture
          C β hβ hβCutoff H left x

/-- The right marginal is exactly the right geometric one-slab Doob row. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureCoupling_rightMarginal
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (left right y : FiniteEvenFourTorusZ2SliceConfiguration H) :
    ∑ x : FiniteEvenFourTorusZ2SliceConfiguration H,
      finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureCoupling
        C β hβ hβCutoff H left right x y =
      finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobKernel
        H β energyIdentity energyNontrivial hβ.le hEnergy.le y right := by
  calc
    (∑ x : FiniteEvenFourTorusZ2SliceConfiguration H,
      finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureCoupling
        C β hβ hβCutoff H left right x y) =
      (finiteRealProbabilityMixtureData
        (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexProbabilityData
          C β hβ hβCutoff H right)
        (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentProbabilityData
          C β hβ hβCutoff H right)).probability y := by
      exact finiteRealProbabilityMixtureCoupling_rightMarginal
        (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureIndexCouplingData
          C β hβ hβCutoff H left right)
        (finiteEvenFourTorusZ2ResidualGaugePerronSmoothedMixtureComponentCouplingData
          C β hβ hβCutoff H left right)
        y
    _ = finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobKernel
        H β energyIdentity energyNontrivial hβ.le hEnergy.le y right := by
      symm
      simpa [finiteRealProbabilityMixtureData] using
        finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobKernel_eq_residualGaugePerronSmoothedMixture
          C β hβ hβCutoff H right y

/-- Exact-marginal full-state coupling of two actual geometric one-slab Doob
rows through their residual-gauge Perron-smoothed mixture representations. -/
noncomputable def
    finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureCouplingData
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (left right : FiniteEvenFourTorusZ2SliceConfiguration H) :
    FiniteRealCouplingData
      (FiniteKernelGroundStateDoobData.doobRowProbabilityData
        (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
          H β energyIdentity energyNontrivial hβ.le hEnergy.le)
        left)
      (FiniteKernelGroundStateDoobData.doobRowProbabilityData
        (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
          H β energyIdentity energyNontrivial hβ.le hEnergy.le)
        right) :=
  { joint := finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureCoupling
      C β hβ hβCutoff H left right
    joint_nonneg :=
      finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureCoupling_nonneg
        C β hβ hβCutoff H left right
    left_marginal :=
      finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureCoupling_leftMarginal
        C β hβ hβCutoff H left right
    right_marginal :=
      finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobMixtureCoupling_rightMarginal
        C β hβ hβCutoff H left right }

end

end MathlibAnalytic
end MGAP4D
