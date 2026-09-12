import MGAP4D.MathlibAnalytic.FinitePositiveWeightSingleSiteVarianceDirichlet
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugePerronSingleLinkConditional
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Actual one-link pair Dirichlet form for the reversible Perron density. -/
def finiteEvenFourTorusZ2UnfixedGaugePerronSingleLinkPairDirichlet
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2SliceConfiguration H → ℝ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H) : ℝ :=
  finitePositiveWeightSingleSitePairDirichlet
    (finiteEvenFourTorusZ2UnfixedGaugePerronDensity
      H β energyIdentity energyNontrivial hβ hEnergy) f A e

/-- The actual Perron one-link conditional variance is exactly its symmetric
pair Dirichlet form. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronSingleLinkVariance_eq_pairDirichlet
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2SliceConfiguration H → ℝ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H) :
    finiteEvenFourTorusZ2UnfixedGaugePerronSingleLinkVariance
        H β energyIdentity energyNontrivial hβ hEnergy f A e =
      finiteEvenFourTorusZ2UnfixedGaugePerronSingleLinkPairDirichlet
        H β energyIdentity energyNontrivial hβ hEnergy f A e := by
  exact finitePositiveWeightSingleSiteVariance_eq_pairDirichlet
    (finiteEvenFourTorusZ2UnfixedGaugePerronDensity
      H β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2UnfixedGaugePerronDensity_pos
      H β energyIdentity energyNontrivial hβ hEnergy)
    f A e

/-- The explicit Perron atom lower bound turns the actual one-link conditional
variance into a volume-independent coercive control of every two-value fiber
difference. -/
theorem finiteEvenFourTorusZ2UnfixedGaugePerronSingleLink_difference_coercive
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 < β)
    (hEnergy : energyIdentity < energyNontrivial)
    (f : FiniteEvenFourTorusZ2SliceConfiguration H → ℝ)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H)
    (e : FiniteEvenFourTorusSpatialLink H)
    (g h : Z2Gauge) :
    ((2 * (z2UnfixedGaugePerronSingleLinkRatio
      β energyIdentity energyNontrivial) ^ 2)⁻¹) ^ 2 *
        (f (finiteZ2GaugeReplaceCoordinate A e g) -
          f (finiteZ2GaugeReplaceCoordinate A e h)) ^ 2 ≤
      2 * finiteEvenFourTorusZ2UnfixedGaugePerronSingleLinkVariance
        H β energyIdentity energyNontrivial hβ.le hEnergy.le f A e := by
  let R := z2UnfixedGaugePerronSingleLinkRatio
    β energyIdentity energyNontrivial
  let m := (2 * R ^ 2)⁻¹
  let prob :=
    finiteEvenFourTorusZ2UnfixedGaugePerronSingleLinkProbability
      H β energyIdentity energyNontrivial hβ.le hEnergy.le A e
  have hR : 0 < R := z2UnfixedGaugePerronSingleLinkRatio_pos hβ hEnergy
  have hDen : 0 < 2 * R ^ 2 := by positivity
  have hm : 0 < m := inv_pos.mpr hDen
  have hpg : m ≤ prob g := by
    simpa [m, R, prob] using
      finiteEvenFourTorusZ2UnfixedGaugePerronSingleLinkProbability_lower
        H β energyIdentity energyNontrivial hβ hEnergy A e g
  have hph : m ≤ prob h := by
    simpa [m, R, prob] using
      finiteEvenFourTorusZ2UnfixedGaugePerronSingleLinkProbability_lower
        H β energyIdentity energyNontrivial hβ hEnergy A e h
  have hpg0 : 0 ≤ prob g :=
    le_of_lt
      (finiteEvenFourTorusZ2UnfixedGaugePerronSingleLinkProbability_pos
        H β energyIdentity energyNontrivial hβ.le hEnergy.le A e g)
  have hProbProduct : m ^ 2 ≤ prob g * prob h := by
    simpa [pow_two] using mul_le_mul hpg hph hm.le hpg0
  have hPair :
      prob g * prob h *
          (f (finiteZ2GaugeReplaceCoordinate A e g) -
            f (finiteZ2GaugeReplaceCoordinate A e h)) ^ 2 ≤
        2 * finiteEvenFourTorusZ2UnfixedGaugePerronSingleLinkVariance
          H β energyIdentity energyNontrivial hβ.le hEnergy.le f A e := by
    simpa [prob, finiteEvenFourTorusZ2UnfixedGaugePerronSingleLinkProbability,
      finiteEvenFourTorusZ2UnfixedGaugePerronSingleLinkVariance,
      finiteZ2GaugeReplaceCoordinate] using
      finitePositiveWeightSingleSite_pairContribution_le_two_mul_variance
        (finiteEvenFourTorusZ2UnfixedGaugePerronDensity
          H β energyIdentity energyNontrivial hβ.le hEnergy.le)
        (finiteEvenFourTorusZ2UnfixedGaugePerronDensity_pos
          H β energyIdentity energyNontrivial hβ.le hEnergy.le)
        f A e g h
  calc
    ((2 * (z2UnfixedGaugePerronSingleLinkRatio
      β energyIdentity energyNontrivial) ^ 2)⁻¹) ^ 2 *
        (f (finiteZ2GaugeReplaceCoordinate A e g) -
          f (finiteZ2GaugeReplaceCoordinate A e h)) ^ 2 =
      m ^ 2 *
        (f (finiteZ2GaugeReplaceCoordinate A e g) -
          f (finiteZ2GaugeReplaceCoordinate A e h)) ^ 2 := by
      rfl
    _ ≤ (prob g * prob h) *
        (f (finiteZ2GaugeReplaceCoordinate A e g) -
          f (finiteZ2GaugeReplaceCoordinate A e h)) ^ 2 :=
      mul_le_mul_of_nonneg_right hProbProduct (sq_nonneg _)
    _ ≤ 2 * finiteEvenFourTorusZ2UnfixedGaugePerronSingleLinkVariance
        H β energyIdentity energyNontrivial hβ.le hEnergy.le f A e := hPair

end

end MathlibAnalytic
end MGAP4D
