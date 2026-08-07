import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeNormalizedProjectiveFiberObstruction
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Global one-step projective obstruction, now allowing both the fine
evaluation configuration and the coarse fibre label to vary.  Thus the
operator-norm normalization ratio is eliminated from the complete finite
coefficient profile, not merely fibrewise at one fixed evaluation point. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantOneStepGlobalProjectiveConfigurationFiberObstruction
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A A₀ : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (b b₀ : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  finiteScalarWeightedProjectiveFiberObstruction
    (fun p :
        FiniteEvenFourTorusZ2SliceConfiguration
            (finiteEvenFourTorusDoubleRefinement H) ×
          FiniteEvenFourTorusZ2SliceConfiguration H =>
      finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy p.1 p.2)
    (fun p :
        FiniteEvenFourTorusZ2SliceConfiguration
            (finiteEvenFourTorusDoubleRefinement H) ×
          FiniteEvenFourTorusZ2SliceConfiguration H =>
      finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight
        H β energyIdentity energyNontrivial hβ hEnergy p.1 p.2)
    (A, b) (A₀, b₀)

/-- The entire one-step normalized configuration-fibre balance is equivalent
to one single normalized identity-anchor equation and normalization-free
projective equality of every `(evaluation configuration, coarse fibre)` pair
against that global anchor. -/
theorem finiteEvenFourTorusZ2OneStepNormalizedConfigurationFiberBalance_iff_globalIdentityAnchor_and_projective
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2OneStepNormalizedConfigurationFiberBalance
        H β energyIdentity energyNontrivial hβ hEnergy ↔
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
          (finiteEvenFourTorusDoubleRefinement H)
          β energyIdentity energyNontrivial hβ hEnergy *
        finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy 1 1 =
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
          H β energyIdentity energyNontrivial hβ hEnergy *
        finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight
          H β energyIdentity energyNontrivial hβ hEnergy 1 1 ∧
      ∀ (A : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement H))
        (b : FiniteEvenFourTorusZ2SliceConfiguration H),
        finiteEvenFourTorusZ2GaugeInvariantOneStepGlobalProjectiveConfigurationFiberObstruction
          H β energyIdentity energyNontrivial hβ hEnergy A 1 b 1 = 0 := by
  unfold FiniteEvenFourTorusZ2OneStepNormalizedConfigurationFiberBalance
  let α :=
    FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement H) ×
      FiniteEvenFourTorusZ2SliceConfiguration H
  let w : α → ℝ := fun p =>
    finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficient
      H β energyIdentity energyNontrivial hβ hEnergy p.1 p.2
  let v : α → ℝ := fun p =>
    finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight
      H β energyIdentity energyNontrivial hβ hEnergy p.1 p.2
  let af := finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
    (finiteEvenFourTorusDoubleRefinement H)
    β energyIdentity energyNontrivial hβ hEnergy
  let ac := finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
    H β energyIdentity energyNontrivial hβ hEnergy
  have hiff :=
    finiteScalarWeighted_scaled_eq_all_iff_anchor_and_projective
      af ac w v
      ((1 : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement H)),
        (1 : FiniteEvenFourTorusZ2SliceConfiguration H))
      (by
        dsimp [af]
        exact finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar_ne_zero
          (finiteEvenFourTorusDoubleRefinement H)
          β energyIdentity energyNontrivial hβ hEnergy)
      (by
        dsimp [v]
        exact ne_of_gt
          (finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight_pos
            H β energyIdentity energyNontrivial hβ hEnergy 1 1))
  constructor
  · intro h
    have hall : ∀ p : α, af * w p = ac * v p := by
      intro p
      exact h p.1 p.2
    have hp := hiff.1 hall
    constructor
    · simpa [af, ac, w, v, α] using hp.1
    · intro A b
      have hob := hp.2 (A, b)
      simpa [finiteEvenFourTorusZ2GaugeInvariantOneStepGlobalProjectiveConfigurationFiberObstruction,
        w, v, α] using hob
  · rintro ⟨hAnchor, hProjective⟩ A b
    have hp :
        af * w
            ((1 : FiniteEvenFourTorusZ2SliceConfiguration
              (finiteEvenFourTorusDoubleRefinement H)),
              (1 : FiniteEvenFourTorusZ2SliceConfiguration H)) =
          ac * v
            ((1 : FiniteEvenFourTorusZ2SliceConfiguration
              (finiteEvenFourTorusDoubleRefinement H)),
              (1 : FiniteEvenFourTorusZ2SliceConfiguration H)) ∧
        ∀ p : α,
          finiteScalarWeightedProjectiveFiberObstruction w v p
            ((1 : FiniteEvenFourTorusZ2SliceConfiguration
              (finiteEvenFourTorusDoubleRefinement H)),
              (1 : FiniteEvenFourTorusZ2SliceConfiguration H)) = 0 := by
      constructor
      · simpa [af, ac, w, v, α] using hAnchor
      · intro p
        have hob := hProjective p.1 p.2
        simpa [finiteEvenFourTorusZ2GaugeInvariantOneStepGlobalProjectiveConfigurationFiberObstruction,
          w, v, α] using hob
    have hall := hiff.2 hp
    exact hall (A, b)

/-- Exact one-step normalized residual criterion with only one normalization-
sensitive scalar equation left in the entire finite coefficient system. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidual_eq_zero_iff_globalIdentityAnchor_and_projective
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
          (finiteEvenFourTorusDoubleRefinement H)
          β energyIdentity energyNontrivial hβ hEnergy *
        finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy 1 1 =
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
          H β energyIdentity energyNontrivial hβ hEnergy *
        finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight
          H β energyIdentity energyNontrivial hβ hEnergy 1 1 ∧
      ∀ (A : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement H))
        (b : FiniteEvenFourTorusZ2SliceConfiguration H),
        finiteEvenFourTorusZ2GaugeInvariantOneStepGlobalProjectiveConfigurationFiberObstruction
          H β energyIdentity energyNontrivial hβ hEnergy A 1 b 1 = 0 := by
  rw [finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidual_eq_zero_iff_normalizedConfigurationFiberBalance]
  exact finiteEvenFourTorusZ2OneStepNormalizedConfigurationFiberBalance_iff_globalIdentityAnchor_and_projective
    H β energyIdentity energyNontrivial hβ hEnergy

/-- A single nonzero global one-step projective obstruction, even between
different fine evaluation configurations, certifies failure of actual
normalized one-step intertwining. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidual_ne_zero_of_globalProjectiveConfigurationFiberObstruction_ne_zero
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H)
    (hMismatch :
      finiteEvenFourTorusZ2GaugeInvariantOneStepGlobalProjectiveConfigurationFiberObstruction
        H β energyIdentity energyNontrivial hβ hEnergy A 1 b 1 ≠ 0) :
    finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy ≠ 0 := by
  intro hzero
  have hp :=
    (finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidual_eq_zero_iff_globalIdentityAnchor_and_projective
      H β energyIdentity energyNontrivial hβ hEnergy).1 hzero
  exact hMismatch (hp.2 A b)

/-- Global projective obstruction for direct two-step finest-to-coarsest
configuration-fibre profiles. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantTwoStepGlobalProjectiveConfigurationFiberObstruction
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A A₀ : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (b b₀ : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  finiteScalarWeightedProjectiveFiberObstruction
    (fun p :
        FiniteEvenFourTorusZ2SliceConfiguration
            (finiteEvenFourTorusDoubleRefinement
              (finiteEvenFourTorusDoubleRefinement H)) ×
          FiniteEvenFourTorusZ2SliceConfiguration H =>
      finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy p.1 p.2)
    (fun p :
        FiniteEvenFourTorusZ2SliceConfiguration
            (finiteEvenFourTorusDoubleRefinement
              (finiteEvenFourTorusDoubleRefinement H)) ×
          FiniteEvenFourTorusZ2SliceConfiguration H =>
      finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight
        H β energyIdentity energyNontrivial hβ hEnergy p.1 p.2)
    (A, b) (A₀, b₀)

/-- Direct two-step normalized compatibility is likewise reduced to one global
identity-anchor normalization equation plus normalization-free projective
shape equality over the complete finest/coarsest coefficient table. -/
theorem finiteEvenFourTorusZ2TwoStepNormalizedConfigurationFiberBalance_iff_globalIdentityAnchor_and_projective
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2TwoStepNormalizedConfigurationFiberBalance
        H β energyIdentity energyNontrivial hβ hEnergy ↔
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H))
          β energyIdentity energyNontrivial hβ hEnergy *
        finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy 1 1 =
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
          H β energyIdentity energyNontrivial hβ hEnergy *
        finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight
          H β energyIdentity energyNontrivial hβ hEnergy 1 1 ∧
      ∀ (A : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H)))
        (b : FiniteEvenFourTorusZ2SliceConfiguration H),
        finiteEvenFourTorusZ2GaugeInvariantTwoStepGlobalProjectiveConfigurationFiberObstruction
          H β energyIdentity energyNontrivial hβ hEnergy A 1 b 1 = 0 := by
  unfold FiniteEvenFourTorusZ2TwoStepNormalizedConfigurationFiberBalance
  let α :=
    FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H)) ×
      FiniteEvenFourTorusZ2SliceConfiguration H
  let w : α → ℝ := fun p =>
    finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient
      H β energyIdentity energyNontrivial hβ hEnergy p.1 p.2
  let v : α → ℝ := fun p =>
    finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight
      H β energyIdentity energyNontrivial hβ hEnergy p.1 p.2
  let af := finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
    (finiteEvenFourTorusDoubleRefinement
      (finiteEvenFourTorusDoubleRefinement H))
    β energyIdentity energyNontrivial hβ hEnergy
  let ac := finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
    H β energyIdentity energyNontrivial hβ hEnergy
  have hiff :=
    finiteScalarWeighted_scaled_eq_all_iff_anchor_and_projective
      af ac w v
      ((1 : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H))),
        (1 : FiniteEvenFourTorusZ2SliceConfiguration H))
      (by
        dsimp [af]
        exact finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar_ne_zero
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H))
          β energyIdentity energyNontrivial hβ hEnergy)
      (by
        dsimp [v]
        exact ne_of_gt
          (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight_pos
            H β energyIdentity energyNontrivial hβ hEnergy 1 1))
  constructor
  · intro h
    have hall : ∀ p : α, af * w p = ac * v p := by
      intro p
      exact h p.1 p.2
    have hp := hiff.1 hall
    constructor
    · simpa [af, ac, w, v, α] using hp.1
    · intro A b
      have hob := hp.2 (A, b)
      simpa [finiteEvenFourTorusZ2GaugeInvariantTwoStepGlobalProjectiveConfigurationFiberObstruction,
        w, v, α] using hob
  · rintro ⟨hAnchor, hProjective⟩ A b
    have hp :
        af * w
            ((1 : FiniteEvenFourTorusZ2SliceConfiguration
              (finiteEvenFourTorusDoubleRefinement
                (finiteEvenFourTorusDoubleRefinement H))),
              (1 : FiniteEvenFourTorusZ2SliceConfiguration H)) =
          ac * v
            ((1 : FiniteEvenFourTorusZ2SliceConfiguration
              (finiteEvenFourTorusDoubleRefinement
                (finiteEvenFourTorusDoubleRefinement H))),
              (1 : FiniteEvenFourTorusZ2SliceConfiguration H)) ∧
        ∀ p : α,
          finiteScalarWeightedProjectiveFiberObstruction w v p
            ((1 : FiniteEvenFourTorusZ2SliceConfiguration
              (finiteEvenFourTorusDoubleRefinement
                (finiteEvenFourTorusDoubleRefinement H))),
              (1 : FiniteEvenFourTorusZ2SliceConfiguration H)) = 0 := by
      constructor
      · simpa [af, ac, w, v, α] using hAnchor
      · intro p
        have hob := hProjective p.1 p.2
        simpa [finiteEvenFourTorusZ2GaugeInvariantTwoStepGlobalProjectiveConfigurationFiberObstruction,
          w, v, α] using hob
    have hall := hiff.2 hp
    exact hall (A, b)

/-- Exact direct two-step normalized residual criterion with one global
normalization-sensitive anchor equation. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidual_eq_zero_iff_globalIdentityAnchor_and_projective
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H))
          β energyIdentity energyNontrivial hβ hEnergy *
        finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy 1 1 =
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
          H β energyIdentity energyNontrivial hβ hEnergy *
        finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight
          H β energyIdentity energyNontrivial hβ hEnergy 1 1 ∧
      ∀ (A : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H)))
        (b : FiniteEvenFourTorusZ2SliceConfiguration H),
        finiteEvenFourTorusZ2GaugeInvariantTwoStepGlobalProjectiveConfigurationFiberObstruction
          H β energyIdentity energyNontrivial hβ hEnergy A 1 b 1 = 0 := by
  rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidual_eq_zero_iff_normalizedConfigurationFiberBalance]
  exact finiteEvenFourTorusZ2TwoStepNormalizedConfigurationFiberBalance_iff_globalIdentityAnchor_and_projective
    H β energyIdentity energyNontrivial hβ hEnergy

/-- A single global direct two-step projective mismatch certifies nonvanishing
of the actual normalized direct two-step residual. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidual_ne_zero_of_globalProjectiveConfigurationFiberObstruction_ne_zero
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H)
    (hMismatch :
      finiteEvenFourTorusZ2GaugeInvariantTwoStepGlobalProjectiveConfigurationFiberObstruction
        H β energyIdentity energyNontrivial hβ hEnergy A 1 b 1 ≠ 0) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy ≠ 0 := by
  intro hzero
  have hp :=
    (finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidual_eq_zero_iff_globalIdentityAnchor_and_projective
      H β energyIdentity energyNontrivial hβ hEnergy).1 hzero
  exact hMismatch (hp.2 A b)

/-- Audit-visible strongest Package-O receipt: for one-step and direct two-step
actual normalized transfers, the full normalization dependence is concentrated
in one global identity-anchor equation, while every other finite Wilson shape
constraint is projective and normalization-independent. -/
structure Z2FiniteEvenFourTorusCrossVolumeNormalizedGlobalProjectiveFiberObstructionPackage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) where
  oneStepGlobalCriterion :
    finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
          (finiteEvenFourTorusDoubleRefinement H)
          β energyIdentity energyNontrivial hβ hEnergy *
        finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy 1 1 =
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
          H β energyIdentity energyNontrivial hβ hEnergy *
        finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight
          H β energyIdentity energyNontrivial hβ hEnergy 1 1 ∧
      ∀ (A : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement H))
        (b : FiniteEvenFourTorusZ2SliceConfiguration H),
        finiteEvenFourTorusZ2GaugeInvariantOneStepGlobalProjectiveConfigurationFiberObstruction
          H β energyIdentity energyNontrivial hβ hEnergy A 1 b 1 = 0
  twoStepGlobalCriterion :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H))
          β energyIdentity energyNontrivial hβ hEnergy *
        finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy 1 1 =
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
          H β energyIdentity energyNontrivial hβ hEnergy *
        finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight
          H β energyIdentity energyNontrivial hβ hEnergy 1 1 ∧
      ∀ (A : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H)))
        (b : FiniteEvenFourTorusZ2SliceConfiguration H),
        finiteEvenFourTorusZ2GaugeInvariantTwoStepGlobalProjectiveConfigurationFiberObstruction
          H β energyIdentity energyNontrivial hβ hEnergy A 1 b 1 = 0

/-- Construct the strongest Package-O global projective receipt. -/
noncomputable def z2FiniteEvenFourTorusCrossVolumeNormalizedGlobalProjectiveFiberObstructionPackage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Z2FiniteEvenFourTorusCrossVolumeNormalizedGlobalProjectiveFiberObstructionPackage
      H β energyIdentity energyNontrivial hβ hEnergy where
  oneStepGlobalCriterion :=
    finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidual_eq_zero_iff_globalIdentityAnchor_and_projective
      H β energyIdentity energyNontrivial hβ hEnergy
  twoStepGlobalCriterion :=
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidual_eq_zero_iff_globalIdentityAnchor_and_projective
      H β energyIdentity energyNontrivial hβ hEnergy

end

end MathlibAnalytic
end MGAP4D