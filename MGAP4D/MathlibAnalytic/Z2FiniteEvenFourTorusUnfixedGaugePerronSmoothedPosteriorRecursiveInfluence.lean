import MGAP4D.MathlibAnalytic.FinitePositiveWeightCrossRatioInfluenceEntries
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugePerronSmoothedPosteriorRecursiveCrossRatio
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Uniform recursive-response input needed to turn the compiled posterior
cross-ratio radius into actual conditional `L¹` influence entries.

The certificate is intentionally still recursive: every target fiber carries
a Dobrushin matrix for the posterior at that fiber.  No strict row-sum or
fixed-point conclusion is hidden in this structure. -/
structure
    FiniteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveInfluenceCertificate
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial) where
  iterations : ℕ
  errorBound :
    FiniteEvenFourTorusSpatialLink H →
      FiniteEvenFourTorusSpatialLink H → ℝ
  errorBound_nonneg :
    ∀ target source : FiniteEvenFourTorusSpatialLink H,
      0 ≤ errorBound target source
  fiberDobrushin :
    ∀ (A : FiniteEvenFourTorusZ2SliceConfiguration H)
      (target : FiniteEvenFourTorusSpatialLink H)
      (g : Z2Gauge),
      FinitePositiveWeightDobrushinL1MatrixData
        (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
          H β energyIdentity energyNontrivial hβ.le hEnergy.le
          (Function.update A target g))
  recursiveError_le :
    ∀ (target source : FiniteEvenFourTorusSpatialLink H)
      (A C : FiniteEvenFourTorusZ2SliceConfiguration H),
      target ≠ source →
      FiniteProductAgreeOff A C source →
      ∀ g h : Z2Gauge,
        finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedRecursiveResponseError
            H β energyIdentity energyNontrivial hβ hEnergy
            A target source g h (C source)
            (fiberDobrushin A target g) iterations ≤
          errorBound target source

/-- Recursive posterior radius with exact zero diagonal. -/
noncomputable def
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveInfluenceRadius
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (C :
      FiniteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveInfluenceCertificate
        H β energyIdentity energyNontrivial hβ hEnergy)
    (target source : FiniteEvenFourTorusSpatialLink H) : ℝ :=
  if target = source then 0 else
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveCrossRatioRadius
      H β energyIdentity energyNontrivial target source
      (C.errorBound target source)

/-- The recursive posterior influence radius is nonnegative. -/
theorem
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveInfluenceRadius_nonneg
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (C :
      FiniteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveInfluenceCertificate
        H β energyIdentity energyNontrivial hβ hEnergy)
    (target source : FiniteEvenFourTorusSpatialLink H) :
    0 ≤
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveInfluenceRadius
        H β energyIdentity energyNontrivial hβ hEnergy C target source := by
  by_cases hEq : target = source
  · simp [
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveInfluenceRadius,
      hEq]
  · rw [
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveInfluenceRadius,
      if_neg hEq]
    exact
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveCrossRatioRadius_nonneg
        H β energyIdentity energyNontrivial hβ hEnergy target source
        (C.errorBound target source) (C.errorBound_nonneg target source)

/-- A recursive response certificate produces entrywise cross-ratio data for
one fixed hidden posterior. -/
noncomputable def
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveInfluenceEntryData
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H)
    (C :
      FiniteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveInfluenceCertificate
        H β energyIdentity energyNontrivial hβ hEnergy) :
    FinitePositiveWeightCrossRatioInfluenceEntryData
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
        H β energyIdentity energyNontrivial hβ.le hEnergy.le environment) :=
  { radius :=
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveInfluenceRadius
        H β energyIdentity energyNontrivial hβ hEnergy C
    radius_nonneg :=
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveInfluenceRadius_nonneg
        H β energyIdentity energyNontrivial hβ hEnergy C
    crossRatioBound := by
      intro target source A B hNe hAgree
      rw [
        finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveInfluenceRadius,
        if_neg hNe]
      exact
        finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight_crossRatio_of_recursiveResponse
          H β energyIdentity energyNontrivial hβ hEnergy
          environment A B target source hNe hAgree
          C.iterations (C.errorBound target source)
          (C.errorBound_nonneg target source)
          (C.fiberDobrushin A target)
          (C.recursiveError_le target source A B hNe hAgree) }

/-- Full-`L¹` influence entry supplied by the recursive posterior certificate. -/
noncomputable def
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveInfluence
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H)
    (C :
      FiniteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveInfluenceCertificate
        H β energyIdentity energyNontrivial hβ hEnergy)
    (target source : FiniteEvenFourTorusSpatialLink H) : ℝ :=
  finitePositiveWeightCrossRatioEntryInfluence
    (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveInfluenceEntryData
      H β energyIdentity energyNontrivial hβ hEnergy environment C)
    target source

/-- The actual one-source hidden-posterior conditional change is bounded by
the explicit recursive influence entry. -/
theorem
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorConditionalL1_le_recursiveInfluence
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (environment A B : FiniteEvenFourTorusZ2SliceConfiguration H)
    (C :
      FiniteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveInfluenceCertificate
        H β energyIdentity energyNontrivial hβ hEnergy)
    (target source : FiniteEvenFourTorusSpatialLink H)
    (hAgree : FiniteProductAgreeOff A B source) :
    finitePositiveWeightSingleSiteConditionalL1
        (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
          H β energyIdentity energyNontrivial hβ.le hEnergy.le environment)
        A B target ≤
      finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveInfluence
        H β energyIdentity energyNontrivial hβ hEnergy
        environment C target source := by
  exact
    finitePositiveWeightSingleSiteConditionalL1_le_crossRatioEntryInfluence
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
        H β energyIdentity energyNontrivial hβ.le hEnergy.le environment)
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight_pos
        H β energyIdentity energyNontrivial hβ hEnergy environment)
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveInfluenceEntryData
        H β energyIdentity energyNontrivial hβ hEnergy environment C)
      target source A B hAgree

/-- Recursive candidate row sum for the fixed hidden posterior. -/
noncomputable def
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveInfluenceRowSum
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H)
    (C :
      FiniteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveInfluenceCertificate
        H β energyIdentity energyNontrivial hβ hEnergy)
    (target : FiniteEvenFourTorusSpatialLink H) : ℝ :=
  ∑ source : FiniteEvenFourTorusSpatialLink H,
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveInfluence
      H β energyIdentity energyNontrivial hβ hEnergy
      environment C target source

/-- Once a strict all-target row-sum certificate is proved, the recursive
entry data becomes the actual generic Dobrushin matrix. -/
noncomputable def
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveDobrushinData
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H)
    (C :
      FiniteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveInfluenceCertificate
        H β energyIdentity energyNontrivial hβ hEnergy)
    (coefficient : ℝ)
    (hCoefficientNonneg : 0 ≤ coefficient)
    (hRowSum :
      ∀ target : FiniteEvenFourTorusSpatialLink H,
        finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveInfluenceRowSum
            H β energyIdentity energyNontrivial hβ hEnergy
            environment C target ≤ coefficient)
    (hCoefficientLtOne : coefficient < 1) :
    FinitePositiveWeightDobrushinL1MatrixData
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
        H β energyIdentity energyNontrivial hβ.le hEnergy.le environment) :=
  (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveInfluenceEntryData
    H β energyIdentity energyNontrivial hβ hEnergy environment C).toDobrushinL1MatrixData
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight_pos
        H β energyIdentity energyNontrivial hβ hEnergy environment)
      coefficient hCoefficientNonneg
      (by
        intro target
        simpa [
          finitePositiveWeightCrossRatioEntryRowSum,
          finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveInfluenceRowSum,
          finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorRecursiveInfluence] using
          hRowSum target)
      hCoefficientLtOne

end

end MathlibAnalytic
end MGAP4D
