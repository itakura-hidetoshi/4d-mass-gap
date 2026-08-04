import MGAP4D.MathlibAnalytic.FinitePositiveWeightSingleSiteConditional
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugePerronLocalRatio
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Unnormalized reversible density of the actual Perron Doob chain. -/
def finiteEvenFourTorusZ2UnfixedGaugePerronDensity
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  (finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
    H β energyIdentity energyNontrivial hβ hEnergy A) ^ 2

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

/-- Squaring the actual positive-ground one-link ratio gives the corresponding
all-volume ratio for the reversible Perron density. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronDensity_le_singleLinkRatio_sq_mul
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
  let R := z2UnfixedGaugePerronSingleLinkRatio
    β energyIdentity energyNontrivial
  let p := finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
    H β energyIdentity energyNontrivial hβ.le hEnergy.le
  let Ag := finiteZ2GaugeReplaceCoordinate A e g
  let Ah := finiteZ2GaugeReplaceCoordinate A e h
  have hp : p Ag ≤ R * p Ah := by
    simpa [p, R, Ag, Ah, finiteZ2GaugeReplaceCoordinate,
      Function.update_update] using
      finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_le_singleLinkRatio_mul_replace
        H β energyIdentity energyNontrivial hβ hEnergy Ag e h
  have hpg : 0 ≤ p Ag :=
    le_of_lt
      (finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_pos
        H β energyIdentity energyNontrivial hβ.le hEnergy.le Ag)
  have hph : 0 ≤ p Ah :=
    le_of_lt
      (finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround_pos
        H β energyIdentity energyNontrivial hβ.le hEnergy.le Ah)
  have hR : 0 ≤ R :=
    le_of_lt (z2UnfixedGaugePerronSingleLinkRatio_pos hβ hEnergy)
  have hfactor :
      0 ≤ (R * p Ah - p Ag) * (R * p Ah + p Ag) :=
    mul_nonneg (sub_nonneg.mpr hp)
      (add_nonneg (mul_nonneg hR hph) hpg)
  change p Ag ^ 2 ≤ R ^ 2 * p Ah ^ 2
  nlinarith

/-- The same explicit squared ratio controls all normalized actual Perron
one-link conditional probabilities. -/
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
    (finiteEvenFourTorusZ2UnfixedGaugePerronDensity_le_singleLinkRatio_sq_mul
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
    simpa [z2Gauge_card_eq_two] using hSum
  have hR : 0 < R := z2UnfixedGaugePerronSingleLinkRatio_pos hβ hEnergy
  have hDen : 0 < 2 * R ^ 2 := by positivity
  rw [inv_le_iff₀ hDen]
  simpa [mul_assoc] using hBound

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
