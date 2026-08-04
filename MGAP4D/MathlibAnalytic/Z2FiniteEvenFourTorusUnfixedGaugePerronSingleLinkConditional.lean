import MGAP4D.MathlibAnalytic.FinitePositiveWeightSingleSiteConditional
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeDoobPosteriorLocalControl
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The actual Perron density is pointwise strictly positive. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronDensity_pos
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H) :
    0 < finiteEvenFourTorusZ2UnfixedGaugePerronDensity
      H β energyIdentity energyNontrivial hβ hEnergy A := by
  unfold finiteEvenFourTorusZ2UnfixedGaugePerronDensity
  exact sq_pos_of_pos
    (finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_pos
      H β energyIdentity energyNontrivial hβ hEnergy A)

/-- Actual one-link conditional partition function for the Perron density. -/
def finiteEvenFourTorusZ2UnfixedGaugePerronSingleLinkPartition
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H) : ℝ :=
  finitePositiveWeightSingleSitePartition
    (finiteEvenFourTorusZ2UnfixedGaugePerronDensity
      H β energyIdentity energyNontrivial hβ hEnergy) A e

/-- Actual real one-link conditional probability for the Perron density. -/
def finiteEvenFourTorusZ2UnfixedGaugePerronSingleLinkProbability
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge) : ℝ :=
  finitePositiveWeightSingleSiteProbability
    (finiteEvenFourTorusZ2UnfixedGaugePerronDensity
      H β energyIdentity energyNontrivial hβ hEnergy) A e g

/-- The actual Perron one-link partition function is strictly positive. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronSingleLinkPartition_pos
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H) :
    0 < finiteEvenFourTorusZ2UnfixedGaugePerronSingleLinkPartition
      H β energyIdentity energyNontrivial hβ hEnergy A e := by
  exact finitePositiveWeightSingleSitePartition_pos
    (finiteEvenFourTorusZ2UnfixedGaugePerronDensity
      H β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2UnfixedGaugePerronDensity_pos
      H β energyIdentity energyNontrivial hβ hEnergy)
    A e

/-- Every actual Perron one-link conditional probability is strictly positive. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronSingleLinkProbability_pos
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge) :
    0 < finiteEvenFourTorusZ2UnfixedGaugePerronSingleLinkProbability
      H β energyIdentity energyNontrivial hβ hEnergy A e g := by
  exact finitePositiveWeightSingleSiteProbability_pos
    (finiteEvenFourTorusZ2UnfixedGaugePerronDensity
      H β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2UnfixedGaugePerronDensity_pos
      H β energyIdentity energyNontrivial hβ hEnergy)
    A e g

/-- The actual Perron one-link conditional probabilities have total mass one. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronSingleLinkProbability_sum_eq_one
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H) :
    ∑ g : Z2Gauge,
      finiteEvenFourTorusZ2UnfixedGaugePerronSingleLinkProbability
        H β energyIdentity energyNontrivial hβ hEnergy A e g = 1 := by
  exact finitePositiveWeightSingleSiteProbability_sum_eq_one
    (finiteEvenFourTorusZ2UnfixedGaugePerronDensity
      H β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2UnfixedGaugePerronDensity_pos
      H β energyIdentity energyNontrivial hβ hEnergy)
    A e

/-- The existing two-sided Perron-density ratio compares every pair of atoms
in one actual link fiber. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronDensity_fiber_le_sqRatio_mul
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H)
    (g h : Z2Gauge) :
    finiteEvenFourTorusZ2UnfixedGaugePerronDensity
        H β energyIdentity energyNontrivial hβ.le hEnergy.le
        (finiteZ2GaugeReplaceCoordinate A e g) ≤
      (z2UnfixedGaugePerronSingleLinkRatio
        β energyIdentity energyNontrivial) ^ 2 *
        finiteEvenFourTorusZ2UnfixedGaugePerronDensity
          H β energyIdentity energyNontrivial hβ.le hEnergy.le
          (finiteZ2GaugeReplaceCoordinate A e h) := by
  have hLocal :=
    finiteEvenFourTorusZ2UnfixedGaugePerronDensity_le_sqRatio_mul_replace
      H β energyIdentity energyNontrivial hβ hEnergy
      (finiteZ2GaugeReplaceCoordinate A e g) e h
  have hReplace :
      finiteZ2GaugeReplaceCoordinate
          (finiteZ2GaugeReplaceCoordinate A e g) e h =
        finiteZ2GaugeReplaceCoordinate A e h := by
    funext i
    by_cases hie : i = e
    · subst i
      simp
    · simp [finiteZ2GaugeReplaceCoordinate, hie]
  rw [hReplace] at hLocal
  exact hLocal

/-- The explicit squared ratio controls all normalized actual Perron one-link
conditional probabilities. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronSingleLinkProbability_le_ratio_sq_mul
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H)
    (g h : Z2Gauge) :
    finiteEvenFourTorusZ2UnfixedGaugePerronSingleLinkProbability
        H β energyIdentity energyNontrivial hβ.le hEnergy.le A e g ≤
      (z2UnfixedGaugePerronSingleLinkRatio
        β energyIdentity energyNontrivial) ^ 2 *
        finiteEvenFourTorusZ2UnfixedGaugePerronSingleLinkProbability
          H β energyIdentity energyNontrivial hβ.le hEnergy.le A e h := by
  exact finitePositiveWeightSingleSiteProbability_le_ratio_mul
    (finiteEvenFourTorusZ2UnfixedGaugePerronDensity
      H β energyIdentity energyNontrivial hβ.le hEnergy.le)
    (finiteEvenFourTorusZ2UnfixedGaugePerronDensity_pos
      H β energyIdentity energyNontrivial hβ.le hEnergy.le)
    A e
    ((z2UnfixedGaugePerronSingleLinkRatio
      β energyIdentity energyNontrivial) ^ 2)
    (finiteEvenFourTorusZ2UnfixedGaugePerronDensity_fiber_le_sqRatio_mul
      H β energyIdentity energyNontrivial hβ hEnergy A e)
    g h

/-- The finite gauge carrier has exactly two elements. -/
theorem z2Gauge_card_eq_two : Fintype.card Z2Gauge = 2 := by
  native_decide

/-- Every actual Perron one-link conditional atom has an explicit all-volume
positive lower bound. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronSingleLinkProbability_lower
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H)
    (g : Z2Gauge) :
    (2 * (z2UnfixedGaugePerronSingleLinkRatio
      β energyIdentity energyNontrivial) ^ 2)⁻¹ ≤
      finiteEvenFourTorusZ2UnfixedGaugePerronSingleLinkProbability
        H β energyIdentity energyNontrivial hβ.le hEnergy.le A e g := by
  let R := z2UnfixedGaugePerronSingleLinkRatio
    β energyIdentity energyNontrivial
  let prob :=
    finiteEvenFourTorusZ2UnfixedGaugePerronSingleLinkProbability
      H β energyIdentity energyNontrivial hβ.le hEnergy.le A e
  have hEach : ∀ h : Z2Gauge, prob h ≤ R ^ 2 * prob g := by
    intro h
    exact
      finiteEvenFourTorusZ2UnfixedGaugePerronSingleLinkProbability_le_ratio_sq_mul
        H β energyIdentity energyNontrivial hβ hEnergy A e h g
  have hSum :
      (∑ h : Z2Gauge, prob h) ≤
        ∑ _h : Z2Gauge, R ^ 2 * prob g := by
    exact Finset.sum_le_sum fun h _hh => hEach h
  have hMass : ∑ h : Z2Gauge, prob h = 1 := by
    simpa [prob] using
      finiteEvenFourTorusZ2UnfixedGaugePerronSingleLinkProbability_sum_eq_one
        H β energyIdentity energyNontrivial hβ.le hEnergy.le A e
  have hBound : 1 ≤ 2 * R ^ 2 * prob g := by
    rw [hMass] at hSum
    simpa [z2Gauge_card_eq_two, mul_assoc] using hSum
  have hR : 0 < R := z2UnfixedGaugePerronSingleLinkRatio_pos hβ hEnergy
  have hDen : 0 < 2 * R ^ 2 := by positivity
  have hLower : (2 * R ^ 2)⁻¹ ≤ prob g := by
    apply (mul_le_mul_left hDen).mp
    rw [mul_inv_cancel₀ (ne_of_gt hDen)]
    exact hBound
  simpa [R, prob] using hLower

/-- Actual conditional expectation for one-link Perron-density heat-bath
resampling. -/
def finiteEvenFourTorusZ2UnfixedGaugePerronSingleLinkExpectation
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2SliceConfiguration H → ℝ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H) : ℝ :=
  finitePositiveWeightSingleSiteExpectation
    (finiteEvenFourTorusZ2UnfixedGaugePerronDensity
      H β energyIdentity energyNontrivial hβ hEnergy) f A e

/-- Actual conditional variance for one-link Perron-density heat-bath
resampling. -/
def finiteEvenFourTorusZ2UnfixedGaugePerronSingleLinkVariance
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2SliceConfiguration H → ℝ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H) : ℝ :=
  finitePositiveWeightSingleSiteVariance
    (finiteEvenFourTorusZ2UnfixedGaugePerronDensity
      H β energyIdentity energyNontrivial hβ hEnergy) f A e

/-- Every actual Perron one-link conditional variance is nonnegative. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronSingleLinkVariance_nonneg
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2SliceConfiguration H → ℝ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H) :
    0 ≤ finiteEvenFourTorusZ2UnfixedGaugePerronSingleLinkVariance
      H β energyIdentity energyNontrivial hβ hEnergy f A e := by
  exact finitePositiveWeightSingleSiteVariance_nonneg
    (finiteEvenFourTorusZ2UnfixedGaugePerronDensity
      H β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2UnfixedGaugePerronDensity_pos
      H β energyIdentity energyNontrivial hβ hEnergy)
    f A e

end

end MathlibAnalytic
end MGAP4D
