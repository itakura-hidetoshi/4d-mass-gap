import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeOneStepMultiplicityNormalizedConfigurationFiber
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeTwoStepTemporalGaugeOrbitFiberReduction
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The direct two-step fine raw-kernel weight is invariant under the finest
residual gauge group. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepFineKernelWeight_invariant_for_average
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))) :
    FiniteGroupCoefficientInvariant
      (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H)))
      (FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H)))
      (finiteEvenFourTorusZ2GaugeInvariantTwoStepFineKernelWeight
        H β energyIdentity energyNontrivial hβ hEnergy A) := by
  intro g B
  unfold finiteEvenFourTorusZ2GaugeInvariantTwoStepFineKernelWeight
  rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_left_invariant]
  rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale_smul]

/-- The direct coarsest comparison weight is coarse residual-gauge invariant. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight_invariant_for_average
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))) :
    FiniteGroupCoefficientInvariant
      (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
      (FiniteEvenFourTorusZ2SliceConfiguration H)
      (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight
        H β energyIdentity energyNontrivial hβ hEnergy A) := by
  intro g b
  unfold finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight
  rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_left_invariant]

/-- Direct finest-to-coarsest residual-gauge hom induced by the two canonical
coarse-graining steps. -/
noncomputable def finiteEvenFourTorusZ2ResidualSliceGaugeTwoStepCoarseHom
    (H : ℕ) :
    FiniteEvenFourTorusZ2ResidualSliceGaugeGroup
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H)) →*
      FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H :=
  (finiteEvenFourTorusZ2ResidualSliceGaugeCoarseHom H).comp
    (finiteEvenFourTorusZ2ResidualSliceGaugeCoarseHom
      (finiteEvenFourTorusDoubleRefinement H))

/-- The direct residual-gauge coarse hom is surjective. -/
theorem finiteEvenFourTorusZ2ResidualSliceGaugeTwoStepCoarseHom_surjective
    (H : ℕ) :
    Function.Surjective
      (finiteEvenFourTorusZ2ResidualSliceGaugeTwoStepCoarseHom H) :=
  (finiteEvenFourTorusZ2ResidualSliceGaugeCoarseHom_surjective H).comp
    (finiteEvenFourTorusZ2ResidualSliceGaugeCoarseHom_surjective
      (finiteEvenFourTorusDoubleRefinement H))

/-- Direct two-step configuration coarse map is equivariant for the composed
residual-gauge hom. -/
theorem finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseMap_smul
    (H : ℕ)
    (g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (B : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))) :
    finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom H (g • B) =
      finiteEvenFourTorusZ2ResidualSliceGaugeTwoStepCoarseHom H g •
        finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom H B := by
  unfold finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom
    finiteEvenFourTorusZ2ResidualSliceGaugeTwoStepCoarseHom
  rw [finiteEvenFourTorusZ2SliceConfigurationCoarseMap_smul]
  rw [finiteEvenFourTorusZ2SliceConfigurationCoarseMap_smul]

/-- Direct finest-to-coarsest kernel coefficient averaged uniformly over the
entire composed configuration fibre. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantTwoStepMultiplicityNormalizedFineConfigurationFiberKernelCoefficient
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  finiteSurjectiveGroupHomFiberAverage
    (finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom H)
    (finiteEvenFourTorusZ2GaugeInvariantTwoStepFineKernelWeight
      H β energyIdentity energyNontrivial hβ hEnergy A) b

/-- The direct normalized coefficient is coarse residual-gauge invariant. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepMultiplicityNormalizedFineConfigurationFiberKernelCoefficient_invariant
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))) :
    FiniteGroupCoefficientInvariant
      (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
      (FiniteEvenFourTorusZ2SliceConfiguration H)
      (finiteEvenFourTorusZ2GaugeInvariantTwoStepMultiplicityNormalizedFineConfigurationFiberKernelCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A) := by
  unfold finiteEvenFourTorusZ2GaugeInvariantTwoStepMultiplicityNormalizedFineConfigurationFiberKernelCoefficient
    finiteSurjectiveGroupHomFiberAverage
  intro g b
  rw [finiteFiberPushforwardCoefficient_invariant_of_equivariant_surjective
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (FiniteEvenFourTorusZ2SliceConfiguration H)
    (finiteEvenFourTorusZ2ResidualSliceGaugeTwoStepCoarseHom H)
    (finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom H)
    (finiteEvenFourTorusZ2ResidualSliceGaugeTwoStepCoarseHom_surjective H)
    (finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseMap_smul H)
    (finiteEvenFourTorusZ2GaugeInvariantTwoStepFineKernelWeight
      H β energyIdentity energyNontrivial hβ hEnergy A)
    (finiteEvenFourTorusZ2GaugeInvariantTwoStepFineKernelWeight_invariant_for_average
      H β energyIdentity energyNontrivial hβ hEnergy A) g b]

/-- Orbit aggregation of the direct normalized configuration-fibre coefficient
is the direct multiplicity-normalized Package-J Boltzmann coefficient. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepMultiplicityNormalizedFineConfigurationFiberAggregate_eq_boltzmann
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H) :
    finiteGroupOrbitAggregateCoefficient
        (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
        (FiniteEvenFourTorusZ2SliceConfiguration H)
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepMultiplicityNormalizedFineConfigurationFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A) q =
      finiteEvenFourTorusZ2GaugeInvariantTwoStepMultiplicityNormalizedBoltzmannFineOrbitFiberCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A q := by
  unfold finiteEvenFourTorusZ2GaugeInvariantTwoStepMultiplicityNormalizedFineConfigurationFiberKernelCoefficient
    finiteSurjectiveGroupHomFiberAverage
    finiteEvenFourTorusZ2GaugeInvariantTwoStepMultiplicityNormalizedBoltzmannFineOrbitFiberCoefficient
  rw [finiteGroupOrbitAggregateCoefficient_const_mul]
  rw [finiteGroupOrbitAggregate_fiberPushforward]
  change
    (Fintype.card (finiteEvenFourTorusZ2SliceConfigurationTwoStepCoarseHom H).ker : ℝ)⁻¹ *
        finiteEvenFourTorusZ2GaugeInvariantTwoStepFineOrbitFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q = _
  rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepFineOrbitFiberKernelCoefficient_eq_temporalGauge]
  rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepTemporalGaugeFineOrbitFiberKernelCoefficient_eq_boltzmann]

/-- Orbit aggregation of the direct coarse comparison weight equals the direct
Package-J coarse Boltzmann coefficient. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeightAggregate_eq_boltzmann
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H) :
    finiteGroupOrbitAggregateCoefficient
        (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
        (FiniteEvenFourTorusZ2SliceConfiguration H)
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight
          H β energyIdentity energyNontrivial hβ hEnergy A) q =
      finiteEvenFourTorusZ2GaugeInvariantTwoStepBoltzmannCoarseOrbitCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A q := by
  change
    finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseOrbitKernelCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A q = _
  rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseOrbitKernelCoefficient_eq_temporalGauge]
  rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepTemporalGaugeCoarseOrbitKernelCoefficient_eq_boltzmann]

/-- Configurationwise direct two-step corrected balance. -/
def FiniteEvenFourTorusZ2TwoStepMultiplicityNormalizedConfigurationFiberBalance
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) : Prop :=
  ∀ (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H),
    finiteEvenFourTorusZ2GaugeInvariantTwoStepMultiplicityNormalizedFineConfigurationFiberKernelCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A b =
      finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight
        H β energyIdentity energyNontrivial hβ hEnergy A b

/-- Direct two-step configurationwise corrected balance is equivalent to its
normalized Boltzmann orbit-fibre form. -/
theorem finiteEvenFourTorusZ2TwoStepMultiplicityNormalizedConfigurationFiberBalance_iff_boltzmannBalance
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2TwoStepMultiplicityNormalizedConfigurationFiberBalance
        H β energyIdentity energyNontrivial hβ hEnergy ↔
      FiniteEvenFourTorusZ2TwoStepMultiplicityNormalizedBoltzmannBalance
        H β energyIdentity energyNontrivial hβ hEnergy := by
  unfold FiniteEvenFourTorusZ2TwoStepMultiplicityNormalizedConfigurationFiberBalance
    FiniteEvenFourTorusZ2TwoStepMultiplicityNormalizedBoltzmannBalance
  constructor
  · intro h A q
    rw [← finiteEvenFourTorusZ2GaugeInvariantTwoStepMultiplicityNormalizedFineConfigurationFiberAggregate_eq_boltzmann,
      ← finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeightAggregate_eq_boltzmann]
    unfold finiteGroupOrbitAggregateCoefficient
    apply Finset.sum_congr rfl
    intro b _hb
    by_cases hbq : finiteGroupOrbitClass
        (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
        (FiniteEvenFourTorusZ2SliceConfiguration H) b = q
    · simp [hbq, h A b]
    · simp [hbq]
  · intro h A
    apply
      (finiteGroupOrbitAggregateCoefficient_eq_all_iff_of_invariant
        (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
        (FiniteEvenFourTorusZ2SliceConfiguration H)
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepMultiplicityNormalizedFineConfigurationFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A)
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight
          H β energyIdentity energyNontrivial hβ hEnergy A)
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepMultiplicityNormalizedFineConfigurationFiberKernelCoefficient_invariant
          H β energyIdentity energyNontrivial hβ hEnergy A)
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight_invariant_for_average
          H β energyIdentity energyNontrivial hβ hEnergy A)).1
    intro q
    rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepMultiplicityNormalizedFineConfigurationFiberAggregate_eq_boltzmann,
      finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeightAggregate_eq_boltzmann]
    exact h A q

/-- The direct corrected configuration-fibre balance holds exactly at `β = 0`. -/
theorem finiteEvenFourTorusZ2TwoStepMultiplicityNormalizedConfigurationFiberBalance_beta_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2TwoStepMultiplicityNormalizedConfigurationFiberBalance
      H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy :=
  (finiteEvenFourTorusZ2TwoStepMultiplicityNormalizedConfigurationFiberBalance_iff_boltzmannBalance
    H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy).2
    (finiteEvenFourTorusZ2TwoStepMultiplicityNormalizedBoltzmannBalance_beta_zero
      H energyIdentity energyNontrivial hEnergy)

end

end MathlibAnalytic
end MGAP4D
