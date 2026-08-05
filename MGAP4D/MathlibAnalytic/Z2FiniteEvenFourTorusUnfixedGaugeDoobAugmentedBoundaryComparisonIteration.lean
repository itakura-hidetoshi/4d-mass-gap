import MGAP4D.MathlibAnalytic.FinitePositiveWeightDobrushinComparisonIteration
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeDoobAugmentedLocalTiltConditionalSource
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The explicit three-coordinate boundary source vector is nonnegative in the
physical high-temperature parameter range. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryConditionalSourceBound_nonneg
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (source : FiniteEvenFourTorusSpatialLink H)
    (target : FiniteEvenFourTorusZ2AugmentedCoordinate H) :
    0 ≤
      finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryConditionalSourceBound
        H β energyIdentity energyNontrivial source target := by
  unfold
    finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryConditionalSourceBound
  by_cases htarget :
      target ∈ finiteEvenFourTorusZ2AugmentedBoundarySourceSupport H source
  · simp only [htarget, if_true]
    have hDelta : 0 ≤ energyNontrivial - energyIdentity :=
      sub_nonneg.mpr hEnergy
    have hExponent :
        -2 * β * (energyNontrivial - energyIdentity) ≤ 0 := by
      nlinarith
    have hExpLeOne :
        Real.exp (-2 * β * (energyNontrivial - energyIdentity)) ≤ 1 := by
      simpa only [Real.exp_zero] using Real.exp_monotone hExponent
    nlinarith
  · simp [htarget]

/-- Proof-relevant interface for the remaining probabilistic Dobrushin
comparison theorem for two actual reduced augmented posterior weights.

The structure deliberately requires the comparison inequality as data.  It
does not assert that such a certificate has already been constructed. -/
structure
    FiniteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryComparisonCertificate
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (source : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge)
    (B : FiniteEvenFourTorusZ2SliceConfiguration H) where
  dobrushinData :
    FinitePositiveWeightDobrushinL1MatrixData
      (finiteEvenFourTorusZ2UnfixedGaugeDoobEncodedReducedAugmentedWeight
        H β energyIdentity energyNontrivial hβ hEnergy
        (finiteZ2GaugeReplaceCoordinate B source g))
  discrepancy : FiniteEvenFourTorusZ2AugmentedCoordinate H → ℝ
  discrepancy_nonneg :
    ∀ target : FiniteEvenFourTorusZ2AugmentedCoordinate H,
      0 ≤ discrepancy target
  discrepancy_le_two :
    ∀ target : FiniteEvenFourTorusZ2AugmentedCoordinate H,
      discrepancy target ≤ 2
  comparison :
    ∀ target : FiniteEvenFourTorusZ2AugmentedCoordinate H,
      discrepancy target ≤
        finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryConditionalSourceBound
            H β energyIdentity energyNontrivial source target +
          finiteNonnegativeKernelApply dobrushinData.influence
            discrepancy target

namespace FiniteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryComparisonCertificate

/-- Every actual boundary comparison certificate unfolds into the finite
Dobrushin partial resolvent plus the exact iterated residual. -/
theorem discrepancy_le_partial_add_residual
    {H : ℕ}
    {β energyIdentity energyNontrivial : ℝ}
    {hβ : 0 ≤ β}
    {hEnergy : energyIdentity ≤ energyNontrivial}
    {source : FiniteEvenFourTorusSpatialLink H}
    {g : Z2Gauge}
    {B : FiniteEvenFourTorusZ2SliceConfiguration H}
    (C :
      FiniteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryComparisonCertificate
        H β energyIdentity energyNontrivial hβ hEnergy source g B)
    (n : ℕ)
    (target : FiniteEvenFourTorusZ2AugmentedCoordinate H) :
    C.discrepancy target ≤
      finiteNonnegativeKernelPartialResolvent
          C.dobrushinData.influence
          (finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryConditionalSourceBound
            H β energyIdentity energyNontrivial source)
          n target +
        finiteNonnegativeKernelPowerApply
          C.dobrushinData.influence C.discrepancy n target := by
  exact
    finitePositiveWeightDobrushinComparison_iterate
      C.dobrushinData
      (finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryConditionalSourceBound
        H β energyIdentity energyNontrivial source)
      C.discrepancy C.comparison n target

/-- The residual of an actual comparison certificate is bounded by twice the
geometric Dobrushin coefficient. -/
theorem discrepancy_le_partial_add_two_geometricResidual
    {H : ℕ}
    {β energyIdentity energyNontrivial : ℝ}
    {hβ : 0 ≤ β}
    {hEnergy : energyIdentity ≤ energyNontrivial}
    {source : FiniteEvenFourTorusSpatialLink H}
    {g : Z2Gauge}
    {B : FiniteEvenFourTorusZ2SliceConfiguration H}
    (C :
      FiniteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryComparisonCertificate
        H β energyIdentity energyNontrivial hβ hEnergy source g B)
    (n : ℕ)
    (target : FiniteEvenFourTorusZ2AugmentedCoordinate H) :
    C.discrepancy target ≤
      finiteNonnegativeKernelPartialResolvent
          C.dobrushinData.influence
          (finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryConditionalSourceBound
            H β energyIdentity energyNontrivial source)
          n target +
        C.dobrushinData.coefficient ^ n * 2 := by
  exact
    finitePositiveWeightDobrushinComparison_iterate_le_partial_add_geometricResidual
      C.dobrushinData
      (finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryConditionalSourceBound
        H β energyIdentity energyNontrivial source)
      C.discrepancy 2 (by norm_num) C.discrepancy_le_two C.comparison n target

/-- The actual finite partial resolvent generated by the three-coordinate
source is nonnegative. -/
theorem partialResolvent_nonneg
    {H : ℕ}
    {β energyIdentity energyNontrivial : ℝ}
    {hβ : 0 ≤ β}
    {hEnergy : energyIdentity ≤ energyNontrivial}
    {source : FiniteEvenFourTorusSpatialLink H}
    {g : Z2Gauge}
    {B : FiniteEvenFourTorusZ2SliceConfiguration H}
    (C :
      FiniteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryComparisonCertificate
        H β energyIdentity energyNontrivial hβ hEnergy source g B)
    (n : ℕ)
    (target : FiniteEvenFourTorusZ2AugmentedCoordinate H) :
    0 ≤
      finiteNonnegativeKernelPartialResolvent
        C.dobrushinData.influence
        (finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryConditionalSourceBound
          H β energyIdentity energyNontrivial source)
        n target := by
  exact
    finitePositiveWeightDobrushin_partialResolvent_nonneg
      C.dobrushinData
      (finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryConditionalSourceBound
        H β energyIdentity energyNontrivial source)
      (finiteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryConditionalSourceBound_nonneg
        H β energyIdentity energyNontrivial hβ hEnergy source)
      n target

/-- The internal coefficient supplied by an actual comparison certificate is
strictly below one. -/
theorem coefficient_lt_one
    {H : ℕ}
    {β energyIdentity energyNontrivial : ℝ}
    {hβ : 0 ≤ β}
    {hEnergy : energyIdentity ≤ energyNontrivial}
    {source : FiniteEvenFourTorusSpatialLink H}
    {g : Z2Gauge}
    {B : FiniteEvenFourTorusZ2SliceConfiguration H}
    (C :
      FiniteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryComparisonCertificate
        H β energyIdentity energyNontrivial hβ hEnergy source g B) :
    C.dobrushinData.coefficient < 1 :=
  C.dobrushinData.coefficient_lt_one

end FiniteEvenFourTorusZ2UnfixedGaugeDoobAugmentedBoundaryComparisonCertificate

end

end MathlibAnalytic
end MGAP4D
