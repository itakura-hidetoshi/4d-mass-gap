import MGAP4D.MathlibAnalytic.FiniteScalarWeightedProjectiveFiberObstruction
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeTwoStepNormalizedConfigurationFiberTemporalLinkBoltzmann
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The actual ambient op-norm normalization scalar is never zero.  This uses
the already-proved nonzero raw unfixed-gauge transfer and therefore holds at
all nonnegative couplings covered by the finite Wilson construction. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar_ne_zero
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
      H β energyIdentity energyNontrivial hβ hEnergy ≠ 0 := by
  unfold finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
  apply inv_ne_zero
  simpa only [norm_ne_zero_iff] using
    (finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer_ne_zero
      H β energyIdentity energyNontrivial hβ hEnergy)

/-- Every actual one-step coarse comparison coefficient is strictly positive.
This supplies a canonical nonzero anchor for projective scalar elimination. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight_pos
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H) :
    0 < finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight
      H β energyIdentity energyNontrivial hβ hEnergy A b := by
  unfold finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight
  exact mul_pos
    (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale_pos H A)
    (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_pos
      H β energyIdentity energyNontrivial hβ hEnergy b
      (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H A))

/-- Every coarsest comparison coefficient in the direct two-step problem is
strictly positive. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight_pos
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H) :
    0 < finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight
      H β energyIdentity energyNontrivial hβ hEnergy A b := by
  unfold finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight
  exact mul_pos
    (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale_pos H A)
    (finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_pos
      H β energyIdentity energyNontrivial hβ hEnergy b
      (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
        (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
          (finiteEvenFourTorusDoubleRefinement H) A)))

/-- Pairwise normalization-independent projective obstruction between one-step
fine fibre mass and the corresponding coarse kernel profile. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantOneStepProjectiveConfigurationFiberObstruction
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (b b₀ : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  finiteScalarWeightedProjectiveFiberObstruction
    (finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficient
      H β energyIdentity energyNontrivial hβ hEnergy A)
    (finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight
      H β energyIdentity energyNontrivial hβ hEnergy A)
    b b₀

/-- Exact one-step scalar elimination: actual normalized configuration-fibre
compatibility is equivalent to the normalized equality at the canonical
identity coarse configuration plus vanishing of every pairwise projective
obstruction against that anchor. -/
theorem finiteEvenFourTorusZ2OneStepNormalizedConfigurationFiberBalance_iff_identityAnchor_and_projective
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2OneStepNormalizedConfigurationFiberBalance
        H β energyIdentity energyNontrivial hβ hEnergy ↔
      (∀ A : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement H),
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
            (finiteEvenFourTorusDoubleRefinement H)
            β energyIdentity energyNontrivial hβ hEnergy *
          finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficient
            H β energyIdentity energyNontrivial hβ hEnergy A 1 =
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
            H β energyIdentity energyNontrivial hβ hEnergy *
          finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight
            H β energyIdentity energyNontrivial hβ hEnergy A 1) ∧
      (∀ (A : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement H))
        (b : FiniteEvenFourTorusZ2SliceConfiguration H),
        finiteEvenFourTorusZ2GaugeInvariantOneStepProjectiveConfigurationFiberObstruction
          H β energyIdentity energyNontrivial hβ hEnergy A b 1 = 0) := by
  unfold FiniteEvenFourTorusZ2OneStepNormalizedConfigurationFiberBalance
  constructor
  · intro h
    constructor
    · intro A
      exact h A 1
    · intro A b
      unfold finiteEvenFourTorusZ2GaugeInvariantOneStepProjectiveConfigurationFiberObstruction
      exact finiteScalarWeightedProjectiveFiberObstruction_eq_zero_of_scaled_eq
        (finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
          (finiteEvenFourTorusDoubleRefinement H)
          β energyIdentity energyNontrivial hβ hEnergy)
        (finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
          H β energyIdentity energyNontrivial hβ hEnergy)
        (finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A)
        (finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight
          H β energyIdentity energyNontrivial hβ hEnergy A)
        (finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar_ne_zero
          (finiteEvenFourTorusDoubleRefinement H)
          β energyIdentity energyNontrivial hβ hEnergy)
        (h A) b 1
  · rintro ⟨hAnchor, hProjective⟩ A
    apply
      (finiteScalarWeighted_scaled_eq_all_iff_anchor_and_projective
        (finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
          (finiteEvenFourTorusDoubleRefinement H)
          β energyIdentity energyNontrivial hβ hEnergy)
        (finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
          H β energyIdentity energyNontrivial hβ hEnergy)
        (finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A)
        (finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight
          H β energyIdentity energyNontrivial hβ hEnergy A)
        (1 : FiniteEvenFourTorusZ2SliceConfiguration H)
        (finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar_ne_zero
          (finiteEvenFourTorusDoubleRefinement H)
          β energyIdentity energyNontrivial hβ hEnergy)
        (ne_of_gt
          (finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight_pos
            H β energyIdentity energyNontrivial hβ hEnergy A 1))).2
    refine ⟨hAnchor A, ?_⟩
    intro b
    exact hProjective A b

/-- Exact one-step normalized residual criterion after eliminating normalization
scalars from all non-anchor fibres. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidual_eq_zero_iff_identityAnchor_and_projective
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      (∀ A : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement H),
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
            (finiteEvenFourTorusDoubleRefinement H)
            β energyIdentity energyNontrivial hβ hEnergy *
          finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficient
            H β energyIdentity energyNontrivial hβ hEnergy A 1 =
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
            H β energyIdentity energyNontrivial hβ hEnergy *
          finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight
            H β energyIdentity energyNontrivial hβ hEnergy A 1) ∧
      (∀ (A : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement H))
        (b : FiniteEvenFourTorusZ2SliceConfiguration H),
        finiteEvenFourTorusZ2GaugeInvariantOneStepProjectiveConfigurationFiberObstruction
          H β energyIdentity energyNontrivial hβ hEnergy A b 1 = 0) := by
  rw [finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidual_eq_zero_iff_normalizedConfigurationFiberBalance]
  exact finiteEvenFourTorusZ2OneStepNormalizedConfigurationFiberBalance_iff_identityAnchor_and_projective
    H β energyIdentity energyNontrivial hβ hEnergy

/-- A single nonzero one-step projective fibre obstruction is an unconditional
certificate that the actual normalized one-step residual is nonzero. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidual_ne_zero_of_projectiveConfigurationFiberObstruction_ne_zero
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H)
    (hMismatch :
      finiteEvenFourTorusZ2GaugeInvariantOneStepProjectiveConfigurationFiberObstruction
        H β energyIdentity energyNontrivial hβ hEnergy A b 1 ≠ 0) :
    finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy ≠ 0 := by
  intro hzero
  have hProjective :=
    (finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidual_eq_zero_iff_identityAnchor_and_projective
      H β energyIdentity energyNontrivial hβ hEnergy).1 hzero
  exact hMismatch (hProjective.2 A b)

/-- Pairwise normalization-independent projective obstruction for the direct
two-step finest-to-coarsest configuration-fibre profiles. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantTwoStepProjectiveConfigurationFiberObstruction
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (b b₀ : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  finiteScalarWeightedProjectiveFiberObstruction
    (finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient
      H β energyIdentity energyNontrivial hβ hEnergy A)
    (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight
      H β energyIdentity energyNontrivial hβ hEnergy A)
    b b₀

/-- Exact direct two-step scalar elimination using the identity coarsest
configuration as the positive anchor. -/
theorem finiteEvenFourTorusZ2TwoStepNormalizedConfigurationFiberBalance_iff_identityAnchor_and_projective
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2TwoStepNormalizedConfigurationFiberBalance
        H β energyIdentity energyNontrivial hβ hEnergy ↔
      (∀ A : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H)),
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
            (finiteEvenFourTorusDoubleRefinement
              (finiteEvenFourTorusDoubleRefinement H))
            β energyIdentity energyNontrivial hβ hEnergy *
          finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient
            H β energyIdentity energyNontrivial hβ hEnergy A 1 =
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
            H β energyIdentity energyNontrivial hβ hEnergy *
          finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight
            H β energyIdentity energyNontrivial hβ hEnergy A 1) ∧
      (∀ (A : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H)))
        (b : FiniteEvenFourTorusZ2SliceConfiguration H),
        finiteEvenFourTorusZ2GaugeInvariantTwoStepProjectiveConfigurationFiberObstruction
          H β energyIdentity energyNontrivial hβ hEnergy A b 1 = 0) := by
  unfold FiniteEvenFourTorusZ2TwoStepNormalizedConfigurationFiberBalance
  constructor
  · intro h
    constructor
    · intro A
      exact h A 1
    · intro A b
      unfold finiteEvenFourTorusZ2GaugeInvariantTwoStepProjectiveConfigurationFiberObstruction
      exact finiteScalarWeightedProjectiveFiberObstruction_eq_zero_of_scaled_eq
        (finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H))
          β energyIdentity energyNontrivial hβ hEnergy)
        (finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
          H β energyIdentity energyNontrivial hβ hEnergy)
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A)
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight
          H β energyIdentity energyNontrivial hβ hEnergy A)
        (finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar_ne_zero
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H))
          β energyIdentity energyNontrivial hβ hEnergy)
        (h A) b 1
  · rintro ⟨hAnchor, hProjective⟩ A
    apply
      (finiteScalarWeighted_scaled_eq_all_iff_anchor_and_projective
        (finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H))
          β energyIdentity energyNontrivial hβ hEnergy)
        (finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
          H β energyIdentity energyNontrivial hβ hEnergy)
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A)
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight
          H β energyIdentity energyNontrivial hβ hEnergy A)
        (1 : FiniteEvenFourTorusZ2SliceConfiguration H)
        (finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar_ne_zero
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H))
          β energyIdentity energyNontrivial hβ hEnergy)
        (ne_of_gt
          (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight_pos
            H β energyIdentity energyNontrivial hβ hEnergy A 1))).2
    refine ⟨hAnchor A, ?_⟩
    intro b
    exact hProjective A b

/-- Exact direct two-step normalized residual criterion after projectivizing
all non-anchor configuration fibres. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidual_eq_zero_iff_identityAnchor_and_projective
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      (∀ A : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H)),
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
            (finiteEvenFourTorusDoubleRefinement
              (finiteEvenFourTorusDoubleRefinement H))
            β energyIdentity energyNontrivial hβ hEnergy *
          finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient
            H β energyIdentity energyNontrivial hβ hEnergy A 1 =
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
            H β energyIdentity energyNontrivial hβ hEnergy *
          finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight
            H β energyIdentity energyNontrivial hβ hEnergy A 1) ∧
      (∀ (A : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H)))
        (b : FiniteEvenFourTorusZ2SliceConfiguration H),
        finiteEvenFourTorusZ2GaugeInvariantTwoStepProjectiveConfigurationFiberObstruction
          H β energyIdentity energyNontrivial hβ hEnergy A b 1 = 0) := by
  rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidual_eq_zero_iff_normalizedConfigurationFiberBalance]
  exact finiteEvenFourTorusZ2TwoStepNormalizedConfigurationFiberBalance_iff_identityAnchor_and_projective
    H β energyIdentity energyNontrivial hβ hEnergy

/-- A single nonzero direct two-step projective fibre obstruction certifies
nonvanishing of the actual normalized direct two-step residual. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidual_ne_zero_of_projectiveConfigurationFiberObstruction_ne_zero
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H)
    (hMismatch :
      finiteEvenFourTorusZ2GaugeInvariantTwoStepProjectiveConfigurationFiberObstruction
        H β energyIdentity energyNontrivial hβ hEnergy A b 1 ≠ 0) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy ≠ 0 := by
  intro hzero
  have hProjective :=
    (finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidual_eq_zero_iff_identityAnchor_and_projective
      H β energyIdentity energyNontrivial hβ hEnergy).1 hzero
  exact hMismatch (hProjective.2 A b)

/-- Audit-visible Package-O receipt: actual operator-norm normalization remains
only in one identity-anchor equality for each evaluation configuration; all
remaining cross-fibre shape constraints are normalization-independent
projective obstructions. -/
structure Z2FiniteEvenFourTorusCrossVolumeNormalizedProjectiveFiberObstructionPackage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) where
  normalizationNonzero : ∀ K : ℕ,
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
      K β energyIdentity energyNontrivial hβ hEnergy ≠ 0
  oneStepCriterion :
    finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      (∀ A : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement H),
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
            (finiteEvenFourTorusDoubleRefinement H)
            β energyIdentity energyNontrivial hβ hEnergy *
          finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficient
            H β energyIdentity energyNontrivial hβ hEnergy A 1 =
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
            H β energyIdentity energyNontrivial hβ hEnergy *
          finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight
            H β energyIdentity energyNontrivial hβ hEnergy A 1) ∧
      (∀ (A : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement H))
        (b : FiniteEvenFourTorusZ2SliceConfiguration H),
        finiteEvenFourTorusZ2GaugeInvariantOneStepProjectiveConfigurationFiberObstruction
          H β energyIdentity energyNontrivial hβ hEnergy A b 1 = 0)
  twoStepCriterion :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      (∀ A : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H)),
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
            (finiteEvenFourTorusDoubleRefinement
              (finiteEvenFourTorusDoubleRefinement H))
            β energyIdentity energyNontrivial hβ hEnergy *
          finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient
            H β energyIdentity energyNontrivial hβ hEnergy A 1 =
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
            H β energyIdentity energyNontrivial hβ hEnergy *
          finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight
            H β energyIdentity energyNontrivial hβ hEnergy A 1) ∧
      (∀ (A : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H)))
        (b : FiniteEvenFourTorusZ2SliceConfiguration H),
        finiteEvenFourTorusZ2GaugeInvariantTwoStepProjectiveConfigurationFiberObstruction
          H β energyIdentity energyNontrivial hβ hEnergy A b 1 = 0)

/-- Construct the complete Package-O projective scalar-elimination receipt. -/
noncomputable def z2FiniteEvenFourTorusCrossVolumeNormalizedProjectiveFiberObstructionPackage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Z2FiniteEvenFourTorusCrossVolumeNormalizedProjectiveFiberObstructionPackage
      H β energyIdentity energyNontrivial hβ hEnergy where
  normalizationNonzero := fun K =>
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar_ne_zero
      K β energyIdentity energyNontrivial hβ hEnergy
  oneStepCriterion :=
    finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidual_eq_zero_iff_identityAnchor_and_projective
      H β energyIdentity energyNontrivial hβ hEnergy
  twoStepCriterion :=
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidual_eq_zero_iff_identityAnchor_and_projective
      H β energyIdentity energyNontrivial hβ hEnergy

end

end MathlibAnalytic
end MGAP4D