import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeNormalizedOrbitFiberCriterion
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeConfigurationFiberTemporalLinkBoltzmann
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Exact configuration-by-configuration balance for the actual op-norm-
normalized one-step transfer.  Fine and coarse normalization scalars remain
independent. -/
def FiniteEvenFourTorusZ2OneStepNormalizedConfigurationFiberBalance
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) : Prop :=
  ∀ (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H),
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
        (finiteEvenFourTorusDoubleRefinement H)
        β energyIdentity energyNontrivial hβ hEnergy *
      finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A b =
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
        H β energyIdentity energyNontrivial hβ hEnergy *
      finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight
        H β energyIdentity energyNontrivial hβ hEnergy A b

/-- The normalized orbit-fibre criterion is equivalent to pointwise equality
of the correspondingly normalized configuration-fibre coefficients. -/
theorem finiteEvenFourTorusZ2OneStepNormalizedOrbitFiberBalance_iff_configurationFiberBalance
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2OneStepNormalizedOrbitFiberBalance
        H β energyIdentity energyNontrivial hβ hEnergy ↔
      FiniteEvenFourTorusZ2OneStepNormalizedConfigurationFiberBalance
        H β energyIdentity energyNontrivial hβ hEnergy := by
  unfold FiniteEvenFourTorusZ2OneStepNormalizedOrbitFiberBalance
  unfold FiniteEvenFourTorusZ2OneStepNormalizedConfigurationFiberBalance
  constructor
  · intro h A
    let νf := finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
      (finiteEvenFourTorusDoubleRefinement H)
      β energyIdentity energyNontrivial hβ hEnergy
    let νc := finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
      H β energyIdentity energyNontrivial hβ hEnergy
    let cf :=
      finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A
    let cc :=
      finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight
        H β energyIdentity energyNontrivial hβ hEnergy A
    have hcf :
        FiniteGroupCoefficientInvariant
          (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
          (FiniteEvenFourTorusZ2SliceConfiguration H)
          (fun b => νf * cf b) := by
      intro g b
      dsimp [νf, cf]
      rw [finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficient_invariant
        H β energyIdentity energyNontrivial hβ hEnergy A g b]
    have hcc :
        FiniteGroupCoefficientInvariant
          (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
          (FiniteEvenFourTorusZ2SliceConfiguration H)
          (fun b => νc * cc b) := by
      intro g b
      dsimp [νc, cc]
      rw [finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight_invariant
        H β energyIdentity energyNontrivial hβ hEnergy A g b]
    apply
      (finiteGroupOrbitAggregateCoefficient_eq_all_iff_of_invariant
        (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
        (FiniteEvenFourTorusZ2SliceConfiguration H)
        (fun b => νf * cf b)
        (fun b => νc * cc b)
        hcf hcc).1
    intro q
    rw [finiteGroupOrbitAggregateCoefficient_smul,
      finiteGroupOrbitAggregateCoefficient_smul]
    dsimp [νf, νc, cf, cc]
    calc
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
            (finiteEvenFourTorusDoubleRefinement H)
            β energyIdentity energyNontrivial hβ hEnergy *
          finiteGroupOrbitAggregateCoefficient
            (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
            (FiniteEvenFourTorusZ2SliceConfiguration H)
            (finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficient
              H β energyIdentity energyNontrivial hβ hEnergy A) q =
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
            (finiteEvenFourTorusDoubleRefinement H)
            β energyIdentity energyNontrivial hβ hEnergy *
          finiteEvenFourTorusZ2GaugeInvariantOneStepFineOrbitFiberKernelCoefficient
            H β energyIdentity energyNontrivial hβ hEnergy A q := by
          rw [finiteEvenFourTorusZ2GaugeInvariantOneStepFineOrbitFiberKernelCoefficient_eq_configurationFiberAggregate]
      _ = finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
            H β energyIdentity energyNontrivial hβ hEnergy *
          finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseOrbitKernelCoefficient
            H β energyIdentity energyNontrivial hβ hEnergy A q := h A q
      _ = finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
            H β energyIdentity energyNontrivial hβ hEnergy *
          finiteGroupOrbitAggregateCoefficient
            (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
            (FiniteEvenFourTorusZ2SliceConfiguration H)
            (finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight
              H β energyIdentity energyNontrivial hβ hEnergy A) q := rfl
  · intro h A q
    let νf := finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
      (finiteEvenFourTorusDoubleRefinement H)
      β energyIdentity energyNontrivial hβ hEnergy
    let νc := finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
      H β energyIdentity energyNontrivial hβ hEnergy
    let cf :=
      finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A
    let cc :=
      finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight
        H β energyIdentity energyNontrivial hβ hEnergy A
    have hcf :
        FiniteGroupCoefficientInvariant
          (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
          (FiniteEvenFourTorusZ2SliceConfiguration H)
          (fun b => νf * cf b) := by
      intro g b
      dsimp [νf, cf]
      rw [finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficient_invariant
        H β energyIdentity energyNontrivial hβ hEnergy A g b]
    have hcc :
        FiniteGroupCoefficientInvariant
          (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
          (FiniteEvenFourTorusZ2SliceConfiguration H)
          (fun b => νc * cc b) := by
      intro g b
      dsimp [νc, cc]
      rw [finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight_invariant
        H β energyIdentity energyNontrivial hβ hEnergy A g b]
    have hAggregate :=
      (finiteGroupOrbitAggregateCoefficient_eq_all_iff_of_invariant
        (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
        (FiniteEvenFourTorusZ2SliceConfiguration H)
        (fun b => νf * cf b)
        (fun b => νc * cc b)
        hcf hcc).2 (h A)
    have hq := hAggregate q
    rw [finiteGroupOrbitAggregateCoefficient_smul,
      finiteGroupOrbitAggregateCoefficient_smul] at hq
    dsimp [νf, νc, cf, cc] at hq
    calc
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
            (finiteEvenFourTorusDoubleRefinement H)
            β energyIdentity energyNontrivial hβ hEnergy *
          finiteEvenFourTorusZ2GaugeInvariantOneStepFineOrbitFiberKernelCoefficient
            H β energyIdentity energyNontrivial hβ hEnergy A q =
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
            (finiteEvenFourTorusDoubleRefinement H)
            β energyIdentity energyNontrivial hβ hEnergy *
          finiteGroupOrbitAggregateCoefficient
            (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
            (FiniteEvenFourTorusZ2SliceConfiguration H)
            (finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficient
              H β energyIdentity energyNontrivial hβ hEnergy A) q := by
          rw [finiteEvenFourTorusZ2GaugeInvariantOneStepFineOrbitFiberKernelCoefficient_eq_configurationFiberAggregate]
      _ = finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
            H β energyIdentity energyNontrivial hβ hEnergy *
          finiteGroupOrbitAggregateCoefficient
            (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
            (FiniteEvenFourTorusZ2SliceConfiguration H)
            (finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight
              H β energyIdentity energyNontrivial hβ hEnergy A) q := hq
      _ = finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
            H β energyIdentity energyNontrivial hβ hEnergy *
          finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseOrbitKernelCoefficient
            H β energyIdentity energyNontrivial hβ hEnergy A q := rfl

/-- Exact configuration-fibre criterion for the actual normalized one-step
cross-volume residual at arbitrary nonnegative coupling. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidual_eq_zero_iff_normalizedConfigurationFiberBalance
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      FiniteEvenFourTorusZ2OneStepNormalizedConfigurationFiberBalance
        H β energyIdentity energyNontrivial hβ hEnergy := by
  rw [finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidual_eq_zero_iff_normalizedOrbitFiberBalance]
  exact finiteEvenFourTorusZ2OneStepNormalizedOrbitFiberBalance_iff_configurationFiberBalance
    H β energyIdentity energyNontrivial hβ hEnergy

/-- Explicit temporal-link Boltzmann form of the actual normalized one-step
configuration-fibre balance. -/
def FiniteEvenFourTorusZ2OneStepNormalizedTemporalLinkConfigurationFiberBalance
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) : Prop :=
  ∀ (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H),
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
        (finiteEvenFourTorusDoubleRefinement H)
        β energyIdentity energyNontrivial hβ hEnergy *
      (∑ B : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement H),
        if finiteEvenFourTorusZ2SliceConfigurationCoarseMap H B = b then
          ((Fintype.card
              (FiniteEvenFourTorusZ2TemporalLinkField
                (finiteEvenFourTorusDoubleRefinement H)) : ℝ)⁻¹ *
            ∑ U : FiniteEvenFourTorusZ2TemporalLinkField
                (finiteEvenFourTorusDoubleRefinement H),
              Real.exp (-β *
                finiteEvenFourTorusZ2TemporalGaugeOneSlabAction
                  (finiteEvenFourTorusDoubleRefinement H)
                  β energyIdentity energyNontrivial B (U • A))) *
            finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H B
        else 0) =
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
        H β energyIdentity energyNontrivial hβ hEnergy *
      (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H A *
        ((Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) : ℝ)⁻¹ *
          ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
            Real.exp (-β *
              finiteEvenFourTorusZ2TemporalGaugeOneSlabAction
                H β energyIdentity energyNontrivial b
                  (U • finiteEvenFourTorusZ2SliceConfigurationCoarseMap H A))))

/-- The normalized configuration-fibre equation is exactly its explicit finite
Boltzmann-sum expansion. -/
theorem finiteEvenFourTorusZ2OneStepNormalizedConfigurationFiberBalance_iff_temporalLinkBalance
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2OneStepNormalizedConfigurationFiberBalance
        H β energyIdentity energyNontrivial hβ hEnergy ↔
      FiniteEvenFourTorusZ2OneStepNormalizedTemporalLinkConfigurationFiberBalance
        H β energyIdentity energyNontrivial hβ hEnergy := by
  unfold FiniteEvenFourTorusZ2OneStepNormalizedConfigurationFiberBalance
  unfold FiniteEvenFourTorusZ2OneStepNormalizedTemporalLinkConfigurationFiberBalance
  constructor
  · intro h A b
    rw [← finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficient_eq_temporalLinkBoltzmannSum]
    rw [← finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight_eq_temporalLinkBoltzmannSum]
    exact h A b
  · intro h A b
    rw [finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficient_eq_temporalLinkBoltzmannSum]
    rw [finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight_eq_temporalLinkBoltzmannSum]
    exact h A b

/-- The actual normalized one-step residual vanishes exactly when the explicit
normalization-weighted temporal-link Boltzmann fibre balance holds. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidual_eq_zero_iff_normalizedTemporalLinkConfigurationFiberBalance
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      FiniteEvenFourTorusZ2OneStepNormalizedTemporalLinkConfigurationFiberBalance
        H β energyIdentity energyNontrivial hβ hEnergy := by
  rw [finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidual_eq_zero_iff_normalizedConfigurationFiberBalance]
  exact finiteEvenFourTorusZ2OneStepNormalizedConfigurationFiberBalance_iff_temporalLinkBalance
    H β energyIdentity energyNontrivial hβ hEnergy

/-- One explicit failure of the normalized configuration-fibre balance is a
certificate that the actual normalized one-step residual is nonzero. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidual_ne_zero_of_normalizedConfigurationFiberMismatch
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H)
    (hMismatch :
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
          (finiteEvenFourTorusDoubleRefinement H)
          β energyIdentity energyNontrivial hβ hEnergy *
        finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A b ≠
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
          H β energyIdentity energyNontrivial hβ hEnergy *
        finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight
          H β energyIdentity energyNontrivial hβ hEnergy A b) :
    finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy ≠ 0 := by
  intro hzero
  have hBalance :=
    (finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidual_eq_zero_iff_normalizedConfigurationFiberBalance
      H β energyIdentity energyNontrivial hβ hEnergy).1 hzero
  exact hMismatch (hBalance A b)

end

end MathlibAnalytic
end MGAP4D
