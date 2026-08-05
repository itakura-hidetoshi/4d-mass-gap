import MGAP4D.MathlibAnalytic.FiniteKernelGroundStateDoobPosteriorProbability
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusUnfixedGaugeGroundStateDoobTransform
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The unnormalized actual unfixed-gauge ground posterior conditioned on a
fixed upper slice. -/
def finiteEvenFourTorusZ2UnfixedGaugeGroundPosteriorWeight
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (environment hidden : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
    H β energyIdentity energyNontrivial hβ hEnergy).
      groundPosteriorWeight environment hidden

/-- Pointwise expansion of the actual ground posterior. -/
@[simp] theorem finiteEvenFourTorusZ2UnfixedGaugeGroundPosteriorWeight_eq
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (environment hidden : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeGroundPosteriorWeight
        H β energyIdentity energyNontrivial hβ hEnergy environment hidden =
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
          H β energyIdentity energyNontrivial hβ hEnergy hidden environment *
        finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
          H β energyIdentity energyNontrivial hβ hEnergy hidden := by
  rfl

/-- The normalized actual ground posterior probability law. -/
noncomputable def finiteEvenFourTorusZ2UnfixedGaugeGroundPosteriorProbabilityData
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H) :
    FiniteRealProbabilityData
      (FiniteEvenFourTorusZ2SliceConfiguration H) :=
  (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
    H β energyIdentity energyNontrivial hβ hEnergy).
      groundPosteriorProbabilityData environment

/-- Normalizing the actual unfixed-gauge ground posterior gives exactly the
geometric one-slab Perron Doob row. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeGroundPosteriorProbability_eq_doobKernel
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (environment hidden : FiniteEvenFourTorusZ2SliceConfiguration H) :
    (finiteEvenFourTorusZ2UnfixedGaugeGroundPosteriorProbabilityData
      H β energyIdentity energyNontrivial hβ hEnergy environment).
        probability hidden =
      finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobKernel
        H β energyIdentity energyNontrivial hβ hEnergy hidden environment := by
  exact
    (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
      H β energyIdentity energyNontrivial hβ hEnergy).
        groundPosteriorProbabilityData_probability_eq_doobKernel
          environment hidden

/-- Temporal-gauge raw ground posterior before residual-gauge averaging. -/
def finiteEvenFourTorusZ2TemporalGaugeGroundPosteriorWeight
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (environment hidden : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
      H β energyIdentity energyNontrivial hβ hEnergy).kernel
      hidden environment *
    finiteEvenFourTorusZ2UnfixedGaugeAmbientPositiveGround
      H β energyIdentity energyNontrivial hβ hEnergy hidden

/-- The actual unfixed-gauge ground posterior is exactly the normalized
residual-gauge average of temporal-gauge raw ground posteriors. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeGroundPosteriorWeight_eq_residualGaugeAverage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (environment hidden : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeGroundPosteriorWeight
        H β energyIdentity energyNontrivial hβ hEnergy environment hidden =
      (Fintype.card
        (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H) : ℝ)⁻¹ *
        ∑ g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H,
          finiteEvenFourTorusZ2TemporalGaugeGroundPosteriorWeight
            H β energyIdentity energyNontrivial hβ hEnergy
            (g • environment) hidden := by
  rw [finiteEvenFourTorusZ2UnfixedGaugeGroundPosteriorWeight_eq]
  rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_eq_rightAverage]
  unfold finiteGroupRightAveragedKernel
    finiteEvenFourTorusZ2TemporalGaugeGroundPosteriorWeight
  rw [← Finset.sum_mul]
  ring

/-- Canonical full-state overlap coupling between two actual geometric Doob
rows. -/
noncomputable def finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobRowCouplingData
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (left right : FiniteEvenFourTorusZ2SliceConfiguration H) :
    FiniteRealCouplingData
      ((finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
        H β energyIdentity energyNontrivial hβ hEnergy).
          doobRowProbabilityData left)
      ((finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
        H β energyIdentity energyNontrivial hβ hEnergy).
          doobRowProbabilityData right) :=
  (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
    H β energyIdentity energyNontrivial hβ hEnergy).
      doobRowOverlapCouplingData left right

/-- The left marginal of the actual geometric Doob-row coupling is exact. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobRowCoupling_leftMarginal
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (left right hidden : FiniteEvenFourTorusZ2SliceConfiguration H) :
    ∑ output : FiniteEvenFourTorusZ2SliceConfiguration H,
      (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobRowCouplingData
        H β energyIdentity energyNontrivial hβ hEnergy left right).
          joint hidden output =
      finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobKernel
        H β energyIdentity energyNontrivial hβ hEnergy hidden left := by
  exact
    (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
      H β energyIdentity energyNontrivial hβ hEnergy).
        doobRowOverlapCouplingData_leftMarginal left right hidden

/-- The right marginal of the actual geometric Doob-row coupling is exact. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobRowCoupling_rightMarginal
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (left right hidden : FiniteEvenFourTorusZ2SliceConfiguration H) :
    ∑ output : FiniteEvenFourTorusZ2SliceConfiguration H,
      (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobRowCouplingData
        H β energyIdentity energyNontrivial hβ hEnergy left right).
          joint output hidden =
      finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobKernel
        H β energyIdentity energyNontrivial hβ hEnergy hidden right := by
  exact
    (finiteEvenFourTorusZ2UnfixedGaugeGroundStateDoobData
      H β energyIdentity energyNontrivial hβ hEnergy).
        doobRowOverlapCouplingData_rightMarginal left right hidden

end

end MathlibAnalytic
end MGAP4D
