import MGAP4D.MathlibAnalytic.NonzeroDerivativeSmallPositive
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeTwoStepProjectiveFirstVariation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A nonzero beta-zero first variation of one identity-anchored one-step
projective coefficient forces the actual operator-norm-normalized one-step
cross-volume residual to be nonzero throughout some positive beta interval. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidual_exists_smallPositive_interval_ne_zero_of_projectiveFirstVariation_ne_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H)
    (hFirstVariation :
      finiteEvenFourTorusZ2GaugeInvariantOneStepGlobalProjectiveConfigurationFiberObstructionFirstVariation
        H energyIdentity energyNontrivial A 1 b 1 ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (β : ℝ) (hβ : 0 < β), β < ε →
        finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidualLinearMap
          H β energyIdentity energyNontrivial (le_of_lt hβ) hEnergy ≠ 0 := by
  have hderiv :=
    finiteEvenFourTorusZ2GaugeInvariantOneStepGlobalProjectiveConfigurationFiberObstructionAnalytic_hasDerivAt_zero
      H energyIdentity energyNontrivial A 1 b 1
  have hzero :=
    finiteEvenFourTorusZ2GaugeInvariantOneStepGlobalProjectiveConfigurationFiberObstructionAnalytic_zero_identityAnchor
      H energyIdentity energyNontrivial hEnergy A b
  rcases
      HasDerivAt.exists_pos_forall_pos_lt_ne_zero_of_eq_zero_of_ne_zero
        hderiv hzero hFirstVariation with
    ⟨ε, hε, hAnalyticNonzero⟩
  refine ⟨ε, hε, ?_⟩
  intro β hβ hβε
  have hProjective := hAnalyticNonzero β hβ hβε
  rw [finiteEvenFourTorusZ2GaugeInvariantOneStepGlobalProjectiveConfigurationFiberObstructionAnalytic_eq_actual
    H β energyIdentity energyNontrivial (le_of_lt hβ) hEnergy A 1 b 1] at hProjective
  exact
    finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidual_ne_zero_of_globalProjectiveConfigurationFiberObstruction_ne_zero
      H β energyIdentity energyNontrivial (le_of_lt hβ) hEnergy A b hProjective

/-- Direct two-step analogue: one nonzero beta-zero projective first variation
forces the actual normalized finest-to-coarsest residual to be nonzero on a
whole sufficiently small positive beta interval. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidual_exists_smallPositive_interval_ne_zero_of_projectiveFirstVariation_ne_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H)
    (hFirstVariation :
      finiteEvenFourTorusZ2GaugeInvariantTwoStepGlobalProjectiveConfigurationFiberObstructionFirstVariation
        H energyIdentity energyNontrivial A 1 b 1 ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (β : ℝ) (hβ : 0 < β), β < ε →
        finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidualLinearMap
          H β energyIdentity energyNontrivial (le_of_lt hβ) hEnergy ≠ 0 := by
  have hderiv :=
    finiteEvenFourTorusZ2GaugeInvariantTwoStepGlobalProjectiveConfigurationFiberObstructionAnalytic_hasDerivAt_zero
      H energyIdentity energyNontrivial A 1 b 1
  have hzero :=
    finiteEvenFourTorusZ2GaugeInvariantTwoStepGlobalProjectiveConfigurationFiberObstructionAnalytic_zero_identityAnchor
      H energyIdentity energyNontrivial hEnergy A b
  rcases
      HasDerivAt.exists_pos_forall_pos_lt_ne_zero_of_eq_zero_of_ne_zero
        hderiv hzero hFirstVariation with
    ⟨ε, hε, hAnalyticNonzero⟩
  refine ⟨ε, hε, ?_⟩
  intro β hβ hβε
  have hProjective := hAnalyticNonzero β hβ hβε
  rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepGlobalProjectiveConfigurationFiberObstructionAnalytic_eq_actual
    H β energyIdentity energyNontrivial (le_of_lt hβ) hEnergy A 1 b 1] at hProjective
  exact
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidual_ne_zero_of_globalProjectiveConfigurationFiberObstruction_ne_zero
      H β energyIdentity energyNontrivial (le_of_lt hβ) hEnergy A b hProjective

/-- If exact normalized one-step compatibility occurs arbitrarily close to
zero from the positive-coupling side, then every fixed identity-anchored
projective first variation must vanish. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneStepProjectiveFirstVariation_eq_zero_of_residualZeros_accumulate_right
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H)
    (hAccum :
      ∀ ε : ℝ, 0 < ε →
        ∃ β : ℝ, ∃ hβ : 0 < β,
          β < ε ∧
            finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidualLinearMap
              H β energyIdentity energyNontrivial (le_of_lt hβ) hEnergy = 0) :
    finiteEvenFourTorusZ2GaugeInvariantOneStepGlobalProjectiveConfigurationFiberObstructionFirstVariation
      H energyIdentity energyNontrivial A 1 b 1 = 0 := by
  by_contra hFirstVariation
  rcases
      finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidual_exists_smallPositive_interval_ne_zero_of_projectiveFirstVariation_ne_zero
        H energyIdentity energyNontrivial hEnergy A b hFirstVariation with
    ⟨ε, hε, hResidualNonzero⟩
  rcases hAccum ε hε with ⟨β, hβ, hβε, hResidualZero⟩
  exact (hResidualNonzero β hβ hβε) hResidualZero

/-- If exact normalized direct two-step compatibility occurs arbitrarily close
to zero from the positive-coupling side, then every fixed identity-anchored
direct two-step projective first variation must vanish. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepProjectiveFirstVariation_eq_zero_of_residualZeros_accumulate_right
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H)
    (hAccum :
      ∀ ε : ℝ, 0 < ε →
        ∃ β : ℝ, ∃ hβ : 0 < β,
          β < ε ∧
            finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidualLinearMap
              H β energyIdentity energyNontrivial (le_of_lt hβ) hEnergy = 0) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepGlobalProjectiveConfigurationFiberObstructionFirstVariation
      H energyIdentity energyNontrivial A 1 b 1 = 0 := by
  by_contra hFirstVariation
  rcases
      finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidual_exists_smallPositive_interval_ne_zero_of_projectiveFirstVariation_ne_zero
        H energyIdentity energyNontrivial hEnergy A b hFirstVariation with
    ⟨ε, hε, hResidualNonzero⟩
  rcases hAccum ε hε with ⟨β, hβ, hβε, hResidualZero⟩
  exact (hResidualNonzero β hβ hβε) hResidualZero

/-- Audit-visible Package-Q receipt.  Positive-coupling normalized
nonintertwining is conditional only on an explicit nonzero finite Wilson
projective first variation; existence of such a witness is deliberately left
to the next package. -/
structure Z2FiniteEvenFourTorusCrossVolumeProjectiveSmallPositiveObstructionPackage
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) where
  oneStepSmallPositive :
    ∀ (A : FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement H))
      (b : FiniteEvenFourTorusZ2SliceConfiguration H),
      finiteEvenFourTorusZ2GaugeInvariantOneStepGlobalProjectiveConfigurationFiberObstructionFirstVariation
          H energyIdentity energyNontrivial A 1 b 1 ≠ 0 →
        ∃ ε : ℝ, 0 < ε ∧
          ∀ (β : ℝ) (hβ : 0 < β), β < ε →
            finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidualLinearMap
              H β energyIdentity energyNontrivial (le_of_lt hβ) hEnergy ≠ 0
  twoStepSmallPositive :
    ∀ (A : FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H)))
      (b : FiniteEvenFourTorusZ2SliceConfiguration H),
      finiteEvenFourTorusZ2GaugeInvariantTwoStepGlobalProjectiveConfigurationFiberObstructionFirstVariation
          H energyIdentity energyNontrivial A 1 b 1 ≠ 0 →
        ∃ ε : ℝ, 0 < ε ∧
          ∀ (β : ℝ) (hβ : 0 < β), β < ε →
            finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidualLinearMap
              H β energyIdentity energyNontrivial (le_of_lt hβ) hEnergy ≠ 0

/-- Construct the Package-Q conditional positive-coupling obstruction receipt. -/
noncomputable def z2FiniteEvenFourTorusCrossVolumeProjectiveSmallPositiveObstructionPackage
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Z2FiniteEvenFourTorusCrossVolumeProjectiveSmallPositiveObstructionPackage
      H energyIdentity energyNontrivial hEnergy where
  oneStepSmallPositive := fun A b hFirstVariation =>
    finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidual_exists_smallPositive_interval_ne_zero_of_projectiveFirstVariation_ne_zero
      H energyIdentity energyNontrivial hEnergy A b hFirstVariation
  twoStepSmallPositive := fun A b hFirstVariation =>
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidual_exists_smallPositive_interval_ne_zero_of_projectiveFirstVariation_ne_zero
      H energyIdentity energyNontrivial hEnergy A b hFirstVariation

end

end MathlibAnalytic
end MGAP4D