import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeTwoStepNormalizedOrbitFiberCriterion
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeNormalizedConfigurationFiberTemporalLinkBoltzmann
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeConfigurationFiberTemporalLinkBoltzmann
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Exact configuration-by-configuration balance for the actual op-norm-
normalized direct two-step transfer.  Finest and coarsest normalization
scalars remain independent. -/
def FiniteEvenFourTorusZ2TwoStepNormalizedConfigurationFiberBalance
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) : Prop :=
  ∀ (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H),
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H))
        β energyIdentity energyNontrivial hβ hEnergy *
      finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A b =
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
        H β energyIdentity energyNontrivial hβ hEnergy *
      finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight
        H β energyIdentity energyNontrivial hβ hEnergy A b

/-- The normalized direct two-step orbit-fibre criterion is equivalent to
pointwise equality of the correspondingly normalized configuration-fibre
coefficients. -/
theorem finiteEvenFourTorusZ2TwoStepNormalizedOrbitFiberBalance_iff_configurationFiberBalance
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2TwoStepNormalizedOrbitFiberBalance
        H β energyIdentity energyNontrivial hβ hEnergy ↔
      FiniteEvenFourTorusZ2TwoStepNormalizedConfigurationFiberBalance
        H β energyIdentity energyNontrivial hβ hEnergy := by
  unfold FiniteEvenFourTorusZ2TwoStepNormalizedOrbitFiberBalance
  unfold FiniteEvenFourTorusZ2TwoStepNormalizedConfigurationFiberBalance
  constructor
  · intro h A
    let νf := finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))
      β energyIdentity energyNontrivial hβ hEnergy
    let νc := finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
      H β energyIdentity energyNontrivial hβ hEnergy
    let cf :=
      finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A
    let cc :=
      finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight
        H β energyIdentity energyNontrivial hβ hEnergy A
    have hcf :
        FiniteGroupCoefficientInvariant
          (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
          (FiniteEvenFourTorusZ2SliceConfiguration H)
          (fun b => νf * cf b) := by
      intro g b
      dsimp [νf, cf]
      rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient_invariant
        H β energyIdentity energyNontrivial hβ hEnergy A g b]
    have hcc :
        FiniteGroupCoefficientInvariant
          (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
          (FiniteEvenFourTorusZ2SliceConfiguration H)
          (fun b => νc * cc b) := by
      intro g b
      dsimp [νc, cc]
      rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight_invariant
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
            (finiteEvenFourTorusDoubleRefinement
              (finiteEvenFourTorusDoubleRefinement H))
            β energyIdentity energyNontrivial hβ hEnergy *
          finiteGroupOrbitAggregateCoefficient
            (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
            (FiniteEvenFourTorusZ2SliceConfiguration H)
            (finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient
              H β energyIdentity energyNontrivial hβ hEnergy A) q =
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
            (finiteEvenFourTorusDoubleRefinement
              (finiteEvenFourTorusDoubleRefinement H))
            β energyIdentity energyNontrivial hβ hEnergy *
          finiteEvenFourTorusZ2GaugeInvariantTwoStepFineOrbitFiberKernelCoefficient
            H β energyIdentity energyNontrivial hβ hEnergy A q := by
          rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepFineOrbitFiberKernelCoefficient_eq_configurationFiberAggregate]
      _ = finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
            H β energyIdentity energyNontrivial hβ hEnergy *
          finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseOrbitKernelCoefficient
            H β energyIdentity energyNontrivial hβ hEnergy A q := h A q
      _ = finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
            H β energyIdentity energyNontrivial hβ hEnergy *
          finiteGroupOrbitAggregateCoefficient
            (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
            (FiniteEvenFourTorusZ2SliceConfiguration H)
            (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight
              H β energyIdentity energyNontrivial hβ hEnergy A) q := rfl
  · intro h A q
    let νf := finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))
      β energyIdentity energyNontrivial hβ hEnergy
    let νc := finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
      H β energyIdentity energyNontrivial hβ hEnergy
    let cf :=
      finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A
    let cc :=
      finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight
        H β energyIdentity energyNontrivial hβ hEnergy A
    have hcf :
        FiniteGroupCoefficientInvariant
          (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
          (FiniteEvenFourTorusZ2SliceConfiguration H)
          (fun b => νf * cf b) := by
      intro g b
      dsimp [νf, cf]
      rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient_invariant
        H β energyIdentity energyNontrivial hβ hEnergy A g b]
    have hcc :
        FiniteGroupCoefficientInvariant
          (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
          (FiniteEvenFourTorusZ2SliceConfiguration H)
          (fun b => νc * cc b) := by
      intro g b
      dsimp [νc, cc]
      rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight_invariant
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
            (finiteEvenFourTorusDoubleRefinement
              (finiteEvenFourTorusDoubleRefinement H))
            β energyIdentity energyNontrivial hβ hEnergy *
          finiteEvenFourTorusZ2GaugeInvariantTwoStepFineOrbitFiberKernelCoefficient
            H β energyIdentity energyNontrivial hβ hEnergy A q =
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
            (finiteEvenFourTorusDoubleRefinement
              (finiteEvenFourTorusDoubleRefinement H))
            β energyIdentity energyNontrivial hβ hEnergy *
          finiteGroupOrbitAggregateCoefficient
            (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
            (FiniteEvenFourTorusZ2SliceConfiguration H)
            (finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient
              H β energyIdentity energyNontrivial hβ hEnergy A) q := by
          rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepFineOrbitFiberKernelCoefficient_eq_configurationFiberAggregate]
      _ = finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
            H β energyIdentity energyNontrivial hβ hEnergy *
          finiteGroupOrbitAggregateCoefficient
            (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
            (FiniteEvenFourTorusZ2SliceConfiguration H)
            (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight
              H β energyIdentity energyNontrivial hβ hEnergy A) q := hq
      _ = finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
            H β energyIdentity energyNontrivial hβ hEnergy *
          finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseOrbitKernelCoefficient
            H β energyIdentity energyNontrivial hβ hEnergy A q := rfl

/-- Exact configuration-fibre criterion for the actual normalized direct two-
step cross-volume residual at arbitrary nonnegative coupling. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidual_eq_zero_iff_normalizedConfigurationFiberBalance
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      FiniteEvenFourTorusZ2TwoStepNormalizedConfigurationFiberBalance
        H β energyIdentity energyNontrivial hβ hEnergy := by
  rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidual_eq_zero_iff_normalizedOrbitFiberBalance]
  exact finiteEvenFourTorusZ2TwoStepNormalizedOrbitFiberBalance_iff_configurationFiberBalance
    H β energyIdentity energyNontrivial hβ hEnergy

/-- Explicit temporal-link Boltzmann form of the actual normalized direct two-
step configuration-fibre balance. -/
def FiniteEvenFourTorusZ2TwoStepNormalizedTemporalLinkConfigurationFiberBalance
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) : Prop :=
  ∀ (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H),
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H))
        β energyIdentity energyNontrivial hβ hEnergy *
      (∑ B : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H)),
        if finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
            (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
              (finiteEvenFourTorusDoubleRefinement H) B) = b then
          ((Fintype.card
              (FiniteEvenFourTorusZ2TemporalLinkField
                (finiteEvenFourTorusDoubleRefinement
                  (finiteEvenFourTorusDoubleRefinement H))) : ℝ)⁻¹ *
            ∑ U : FiniteEvenFourTorusZ2TemporalLinkField
                (finiteEvenFourTorusDoubleRefinement
                  (finiteEvenFourTorusDoubleRefinement H)),
              Real.exp (-β *
                finiteEvenFourTorusZ2TemporalGaugeOneSlabAction
                  (finiteEvenFourTorusDoubleRefinement
                    (finiteEvenFourTorusDoubleRefinement H))
                  β energyIdentity energyNontrivial B (U • A))) *
            finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale H B
        else 0) =
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
        H β energyIdentity energyNontrivial hβ hEnergy *
      (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale H A *
        ((Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) : ℝ)⁻¹ *
          ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
            Real.exp (-β *
              finiteEvenFourTorusZ2TemporalGaugeOneSlabAction
                H β energyIdentity energyNontrivial b
                  (U • finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
                    (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
                      (finiteEvenFourTorusDoubleRefinement H) A)))))

/-- The normalized direct two-step configuration-fibre equation is exactly its
explicit finite Boltzmann-sum expansion. -/
theorem finiteEvenFourTorusZ2TwoStepNormalizedConfigurationFiberBalance_iff_temporalLinkBalance
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2TwoStepNormalizedConfigurationFiberBalance
        H β energyIdentity energyNontrivial hβ hEnergy ↔
      FiniteEvenFourTorusZ2TwoStepNormalizedTemporalLinkConfigurationFiberBalance
        H β energyIdentity energyNontrivial hβ hEnergy := by
  unfold FiniteEvenFourTorusZ2TwoStepNormalizedConfigurationFiberBalance
  unfold FiniteEvenFourTorusZ2TwoStepNormalizedTemporalLinkConfigurationFiberBalance
  constructor
  · intro h A b
    rw [← finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient_eq_temporalLinkBoltzmannSum]
    rw [← finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight_eq_temporalLinkBoltzmannSum]
    exact h A b
  · intro h A b
    rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient_eq_temporalLinkBoltzmannSum]
    rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight_eq_temporalLinkBoltzmannSum]
    exact h A b

/-- The actual normalized direct two-step residual vanishes exactly when the
normalization-weighted temporal-link Boltzmann fibre balance holds. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidual_eq_zero_iff_normalizedTemporalLinkConfigurationFiberBalance
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      FiniteEvenFourTorusZ2TwoStepNormalizedTemporalLinkConfigurationFiberBalance
        H β energyIdentity energyNontrivial hβ hEnergy := by
  rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidual_eq_zero_iff_normalizedConfigurationFiberBalance]
  exact finiteEvenFourTorusZ2TwoStepNormalizedConfigurationFiberBalance_iff_temporalLinkBalance
    H β energyIdentity energyNontrivial hβ hEnergy

/-- One explicit failed normalized direct two-step configuration fibre is a
certificate that the actual normalized direct two-step residual is nonzero. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidual_ne_zero_of_normalizedConfigurationFiberMismatch
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H)
    (hMismatch :
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H))
          β energyIdentity energyNontrivial hβ hEnergy *
        finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A b ≠
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
          H β energyIdentity energyNontrivial hβ hEnergy *
        finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight
          H β energyIdentity energyNontrivial hβ hEnergy A b) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy ≠ 0 := by
  intro hzero
  have hBalance :=
    (finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidual_eq_zero_iff_normalizedConfigurationFiberBalance
      H β energyIdentity energyNontrivial hβ hEnergy).1 hzero
  exact hMismatch (hBalance A b)

/-- Audit-visible Package-N receipt: one-step and direct two-step actual
operator-norm-normalized compatibility are reduced to exact finite
configuration-fibre and temporal-link Boltzmann balances, with no positive-
coupling compatibility assumed. -/
structure Z2FiniteEvenFourTorusCrossVolumeNormalizedConfigurationFiberTemporalLinkPackage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) where
  oneStepConfigurationCriterion :
    finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      FiniteEvenFourTorusZ2OneStepNormalizedConfigurationFiberBalance
        H β energyIdentity energyNontrivial hβ hEnergy
  oneStepTemporalLinkCriterion :
    finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      FiniteEvenFourTorusZ2OneStepNormalizedTemporalLinkConfigurationFiberBalance
        H β energyIdentity energyNontrivial hβ hEnergy
  twoStepOrbitFiberCriterion :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      FiniteEvenFourTorusZ2TwoStepNormalizedOrbitFiberBalance
        H β energyIdentity energyNontrivial hβ hEnergy
  twoStepConfigurationCriterion :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      FiniteEvenFourTorusZ2TwoStepNormalizedConfigurationFiberBalance
        H β energyIdentity energyNontrivial hβ hEnergy
  twoStepTemporalLinkCriterion :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      FiniteEvenFourTorusZ2TwoStepNormalizedTemporalLinkConfigurationFiberBalance
        H β energyIdentity energyNontrivial hβ hEnergy

/-- Construct the complete Package-N normalized finite-fibre receipt. -/
noncomputable def z2FiniteEvenFourTorusCrossVolumeNormalizedConfigurationFiberTemporalLinkPackage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Z2FiniteEvenFourTorusCrossVolumeNormalizedConfigurationFiberTemporalLinkPackage
      H β energyIdentity energyNontrivial hβ hEnergy where
  oneStepConfigurationCriterion :=
    finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidual_eq_zero_iff_normalizedConfigurationFiberBalance
      H β energyIdentity energyNontrivial hβ hEnergy
  oneStepTemporalLinkCriterion :=
    finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidual_eq_zero_iff_normalizedTemporalLinkConfigurationFiberBalance
      H β energyIdentity energyNontrivial hβ hEnergy
  twoStepOrbitFiberCriterion :=
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidual_eq_zero_iff_normalizedOrbitFiberBalance
      H β energyIdentity energyNontrivial hβ hEnergy
  twoStepConfigurationCriterion :=
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidual_eq_zero_iff_normalizedConfigurationFiberBalance
      H β energyIdentity energyNontrivial hβ hEnergy
  twoStepTemporalLinkCriterion :=
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidual_eq_zero_iff_normalizedTemporalLinkConfigurationFiberBalance
      H β energyIdentity energyNontrivial hβ hEnergy

end

end MathlibAnalytic
end MGAP4D