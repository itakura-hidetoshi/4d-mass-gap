import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeOneStepConfigurationFiberKernelEvaluation
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeMultiplicityNormalizedBoltzmannBalance
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Actual one-step fine kernel coefficient averaged uniformly over one
configuration coarse-map fibre. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantOneStepMultiplicityNormalizedFineConfigurationFiberKernelCoefficient
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  finiteSurjectiveGroupHomFiberAverage
    (finiteEvenFourTorusZ2SliceConfigurationCoarseHom H)
    (finiteEvenFourTorusZ2GaugeInvariantOneStepFineKernelWeight
      H β energyIdentity energyNontrivial hβ hEnergy A) b

/-- The normalized coefficient is exactly kernel-cardinality inverse times the
raw configuration-fibre sum. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneStepMultiplicityNormalizedFineConfigurationFiberKernelCoefficient_eq_inv_mul_raw
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2GaugeInvariantOneStepMultiplicityNormalizedFineConfigurationFiberKernelCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A b =
      (Fintype.card (finiteEvenFourTorusZ2SliceConfigurationCoarseHom H).ker : ℝ)⁻¹ *
        finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A b := by
  rfl

/-- Multiplicity normalization preserves coarse residual-gauge invariance of
the fibre coefficient. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneStepMultiplicityNormalizedFineConfigurationFiberKernelCoefficient_invariant
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H)) :
    FiniteGroupCoefficientInvariant
      (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
      (FiniteEvenFourTorusZ2SliceConfiguration H)
      (finiteEvenFourTorusZ2GaugeInvariantOneStepMultiplicityNormalizedFineConfigurationFiberKernelCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A) := by
  intro g b
  rw [finiteEvenFourTorusZ2GaugeInvariantOneStepMultiplicityNormalizedFineConfigurationFiberKernelCoefficient_eq_inv_mul_raw,
    finiteEvenFourTorusZ2GaugeInvariantOneStepMultiplicityNormalizedFineConfigurationFiberKernelCoefficient_eq_inv_mul_raw]
  rw [finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficient_invariant
    H β energyIdentity energyNontrivial hβ hEnergy A g b]

/-- Orbit aggregation commutes with multiplication of a coefficient by a
constant scalar. -/
theorem finiteGroupOrbitAggregateCoefficient_const_mul
    (G α : Type)
    [Group G]
    [Fintype α]
    [MulAction G α]
    (c : ℝ)
    (a : α → ℝ)
    (q : FiniteGroupOrbitQuotient G α) :
    finiteGroupOrbitAggregateCoefficient G α (fun x => c * a x) q =
      c * finiteGroupOrbitAggregateCoefficient G α a q := by
  classical
  unfold finiteGroupOrbitAggregateCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _hx
  by_cases hxq : finiteGroupOrbitClass G α x = q
  · simp [hxq]
  · simp [hxq]

/-- Orbit aggregation of the normalized configuration-fibre coefficient is
exactly the multiplicity-normalized Package-J fine Boltzmann coefficient. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneStepMultiplicityNormalizedFineConfigurationFiberAggregate_eq_boltzmann
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H) :
    finiteGroupOrbitAggregateCoefficient
        (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
        (FiniteEvenFourTorusZ2SliceConfiguration H)
        (finiteEvenFourTorusZ2GaugeInvariantOneStepMultiplicityNormalizedFineConfigurationFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A) q =
      finiteEvenFourTorusZ2GaugeInvariantOneStepMultiplicityNormalizedBoltzmannFineOrbitFiberCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A q := by
  unfold finiteEvenFourTorusZ2GaugeInvariantOneStepMultiplicityNormalizedFineConfigurationFiberKernelCoefficient
    finiteSurjectiveGroupHomFiberAverage
    finiteEvenFourTorusZ2GaugeInvariantOneStepMultiplicityNormalizedBoltzmannFineOrbitFiberCoefficient
  rw [finiteGroupOrbitAggregateCoefficient_const_mul]
  apply congrArg (fun t : ℝ =>
    (Fintype.card (finiteEvenFourTorusZ2SliceConfigurationCoarseHom H).ker : ℝ)⁻¹ * t)
  change
    finiteGroupOrbitAggregateCoefficient
        (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
        (FiniteEvenFourTorusZ2SliceConfiguration H)
        (finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A) q =
      finiteEvenFourTorusZ2GaugeInvariantOneStepBoltzmannFineOrbitFiberCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A q
  rw [← finiteEvenFourTorusZ2GaugeInvariantOneStepFineOrbitFiberKernelCoefficient_eq_configurationFiberAggregate]
  rw [finiteEvenFourTorusZ2GaugeInvariantOneStepFineOrbitFiberKernelCoefficient_eq_temporalGauge]
  rw [finiteEvenFourTorusZ2GaugeInvariantOneStepTemporalGaugeFineOrbitFiberKernelCoefficient_eq_boltzmann]

/-- The coarse raw comparison coefficient has Package-J's coarse Boltzmann
orbit coefficient as its orbit aggregation. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeightAggregate_eq_boltzmann
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H) :
    finiteGroupOrbitAggregateCoefficient
        (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
        (FiniteEvenFourTorusZ2SliceConfiguration H)
        (finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight
          H β energyIdentity energyNontrivial hβ hEnergy A) q =
      finiteEvenFourTorusZ2GaugeInvariantOneStepBoltzmannCoarseOrbitCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A q := by
  change
    finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseOrbitKernelCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A q = _
  rw [finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseOrbitKernelCoefficient_eq_temporalGauge]
  rw [finiteEvenFourTorusZ2GaugeInvariantOneStepTemporalGaugeCoarseOrbitKernelCoefficient_eq_boltzmann]

/-- Exact configurationwise multiplicity-normalized one-step balance. -/
def FiniteEvenFourTorusZ2OneStepMultiplicityNormalizedConfigurationFiberBalance
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) : Prop :=
  ∀ (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H),
    finiteEvenFourTorusZ2GaugeInvariantOneStepMultiplicityNormalizedFineConfigurationFiberKernelCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A b =
      finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight
        H β energyIdentity energyNontrivial hβ hEnergy A b

/-- The configurationwise corrected balance is equivalent to the normalized
Boltzmann orbit-fibre balance. -/
theorem finiteEvenFourTorusZ2OneStepMultiplicityNormalizedConfigurationFiberBalance_iff_boltzmannBalance
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2OneStepMultiplicityNormalizedConfigurationFiberBalance
        H β energyIdentity energyNontrivial hβ hEnergy ↔
      FiniteEvenFourTorusZ2OneStepMultiplicityNormalizedBoltzmannBalance
        H β energyIdentity energyNontrivial hβ hEnergy := by
  unfold FiniteEvenFourTorusZ2OneStepMultiplicityNormalizedConfigurationFiberBalance
    FiniteEvenFourTorusZ2OneStepMultiplicityNormalizedBoltzmannBalance
  constructor
  · intro h A q
    rw [← finiteEvenFourTorusZ2GaugeInvariantOneStepMultiplicityNormalizedFineConfigurationFiberAggregate_eq_boltzmann,
      ← finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeightAggregate_eq_boltzmann]
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
        (finiteEvenFourTorusZ2GaugeInvariantOneStepMultiplicityNormalizedFineConfigurationFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A)
        (finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight
          H β energyIdentity energyNontrivial hβ hEnergy A)
        (finiteEvenFourTorusZ2GaugeInvariantOneStepMultiplicityNormalizedFineConfigurationFiberKernelCoefficient_invariant
          H β energyIdentity energyNontrivial hβ hEnergy A)
        (finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight_invariant
          H β energyIdentity energyNontrivial hβ hEnergy A)).1
    intro q
    rw [finiteEvenFourTorusZ2GaugeInvariantOneStepMultiplicityNormalizedFineConfigurationFiberAggregate_eq_boltzmann,
      finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeightAggregate_eq_boltzmann]
    exact h A q

/-- Therefore the corrected configuration-fibre balance holds exactly at
`β = 0`, even though the original raw balance fails there. -/
theorem finiteEvenFourTorusZ2OneStepMultiplicityNormalizedConfigurationFiberBalance_beta_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2OneStepMultiplicityNormalizedConfigurationFiberBalance
      H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy :=
  (finiteEvenFourTorusZ2OneStepMultiplicityNormalizedConfigurationFiberBalance_iff_boltzmannBalance
    H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy).2
    (finiteEvenFourTorusZ2OneStepMultiplicityNormalizedBoltzmannBalance_beta_zero
      H energyIdentity energyNontrivial hEnergy)

end

end MathlibAnalytic
end MGAP4D
