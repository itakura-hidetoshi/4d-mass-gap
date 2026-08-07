import MGAP4D.MathlibAnalytic.FiniteConstantOneKernelNormalization
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeBetaZeroConfigurationFiberMismatch
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeTwoStepKernelFixedSectorCompatibility
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProduct

noncomputable section

/-- At `β = 0`, every exact temporal-link averaged Wilson one-slab kernel entry
is one.  The energy parameters disappear because every Boltzmann exponent is
zero. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_beta_zero_eq_one
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy =
      fun _ _ => (1 : ℝ) := by
  funext A B
  rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_apply]
  have hcard :
      (Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [hcard]

/-- Hence the actual op-norm-normalized invariant transfer at `β = 0` is the
uniform averaging operator on the complete configuration carrier. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_beta_zero_apply_coe
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H) :
    (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy f).1 A =
      (Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)⁻¹ *
        ∑ B : FiniteEvenFourTorusZ2SliceConfiguration H, f.1 B := by
  rw [finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_apply_coe]
  unfold finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer
  rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_beta_zero_eq_one]
  exact finiteKernelNormalizedOperator_one_apply f.1 A

/-- The raw fibre multiplicity obstruction is exactly cancelled by the actual
operator-norm normalization at `β = 0`: the canonical normalized one-step
cross-volume transfer residual vanishes. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidual_beta_zero_eq_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidualLinearMap
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy = 0 := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  ext A
  change
    (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
        (finiteEvenFourTorusDoubleRefinement H)
        0 energyIdentity energyNontrivial (le_refl 0) hEnergy
        (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H f)).1 A -
      (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H
        (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
          H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy f)).1 A = 0
  apply sub_eq_zero.mpr
  let s := finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingCardinalityScale H
  have hAvg :=
    finiteSurjectiveGroupHom_uniformAverage_comp
      (finiteEvenFourTorusZ2SliceConfigurationCoarseHom H)
      (finiteEvenFourTorusZ2SliceConfigurationCoarseHom_surjective H)
      f.1
  change
    (Fintype.card
        (FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement H)) : ℝ)⁻¹ *
        (∑ B : FiniteEvenFourTorusZ2SliceConfiguration
            (finiteEvenFourTorusDoubleRefinement H),
          f.1 (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H B)) =
      (Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)⁻¹ *
        ∑ b : FiniteEvenFourTorusZ2SliceConfiguration H, f.1 b at hAvg
  calc
    (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
        (finiteEvenFourTorusDoubleRefinement H)
        0 energyIdentity energyNontrivial (le_refl 0) hEnergy
        (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H f)).1 A =
      (Fintype.card
          (FiniteEvenFourTorusZ2SliceConfiguration
            (finiteEvenFourTorusDoubleRefinement H)) : ℝ)⁻¹ *
        ∑ B : FiniteEvenFourTorusZ2SliceConfiguration
            (finiteEvenFourTorusDoubleRefinement H),
          (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H f).1 B := by
      rw [finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_beta_zero_apply_coe]
    _ = (Fintype.card
          (FiniteEvenFourTorusZ2SliceConfiguration
            (finiteEvenFourTorusDoubleRefinement H)) : ℝ)⁻¹ *
        ∑ B : FiniteEvenFourTorusZ2SliceConfiguration
            (finiteEvenFourTorusDoubleRefinement H),
          s * f.1 (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H B) := by
      congr 1
      apply Finset.sum_congr rfl
      intro B _hB
      rw [finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding_apply_coe_eq_scale_mul_rawPullback]
      rw [finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale_eq_cardinality]
      rfl
    _ = s *
        ((Fintype.card
            (FiniteEvenFourTorusZ2SliceConfiguration
              (finiteEvenFourTorusDoubleRefinement H)) : ℝ)⁻¹ *
          ∑ B : FiniteEvenFourTorusZ2SliceConfiguration
              (finiteEvenFourTorusDoubleRefinement H),
            f.1 (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H B)) := by
      rw [← Finset.mul_sum]
      ring
    _ = s *
        ((Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)⁻¹ *
          ∑ b : FiniteEvenFourTorusZ2SliceConfiguration H, f.1 b) := by
      rw [hAvg]
    _ = s *
        (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
          H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy f).1
          (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H A) := by
      rw [finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_beta_zero_apply_coe]
    _ = (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H
        (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
          H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy f)).1 A := by
      rw [finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding_apply_coe_eq_scale_mul_rawPullback]
      rw [finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale_eq_cardinality]
      rfl

/-- Direct two-step normalized compatibility follows functorially from the two
successive one-step normalized compatibilities and the exact embedding cocycle. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidual_beta_zero_eq_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidualLinearMap
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy = 0 := by
  apply LinearMap.ext
  intro f
  change
    finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H))
        0 energyIdentity energyNontrivial (le_refl 0) hEnergy
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingLinearIsometry H f) -
      finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingLinearIsometry H
        (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
          H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy f) = 0
  apply sub_eq_zero.mpr
  have hFineMap :=
    finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidual_beta_zero_eq_zero
      (finiteEvenFourTorusDoubleRefinement H)
      energyIdentity energyNontrivial hEnergy
  have hFine := LinearMap.congr_fun hFineMap
    (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H f)
  rw [finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidualLinearMap_apply]
    at hFine
  have hFineEq := sub_eq_zero.mp hFine
  have hCoarseMap :=
    finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidual_beta_zero_eq_zero
      H energyIdentity energyNontrivial hEnergy
  have hCoarse := LinearMap.congr_fun hCoarseMap f
  rw [finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidualLinearMap_apply]
    at hCoarse
  have hCoarseEq := sub_eq_zero.mp hCoarse
  calc
    finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H))
        0 energyIdentity energyNontrivial (le_refl 0) hEnergy
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingLinearIsometry H f) =
      finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H))
        0 energyIdentity energyNontrivial (le_refl 0) hEnergy
        (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry
          (finiteEvenFourTorusDoubleRefinement H)
          (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H f)) := by
      rw [finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding_twoStep_cocycle]
    _ = finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry
        (finiteEvenFourTorusDoubleRefinement H)
        (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
          (finiteEvenFourTorusDoubleRefinement H)
          0 energyIdentity energyNontrivial (le_refl 0) hEnergy
          (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H f)) :=
      hFineEq
    _ = finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry
        (finiteEvenFourTorusDoubleRefinement H)
        (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H
          (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
            H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy f)) := by
      rw [hCoarseEq]
    _ = finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingLinearIsometry H
        (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
          H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy f) := by
      rw [finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding_twoStep_cocycle]

/-- The β=0 distinction is now exact at the actual operator level: canonical
raw transfer comparison fails, while canonical op-norm-normalized transfer
comparison succeeds. -/
theorem finiteEvenFourTorusZ2OneStepRawNonzero_normalizedZero_beta_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidualLinearMap
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy ≠ 0 ∧
      finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidualLinearMap
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy = 0 :=
  ⟨finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidual_beta_zero_ne_zero
      H energyIdentity energyNontrivial hEnergy,
    finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidual_beta_zero_eq_zero
      H energyIdentity energyNontrivial hEnergy⟩

/-- The same exact raw-failure / normalized-success dichotomy holds for the
direct two-step comparison. -/
theorem finiteEvenFourTorusZ2TwoStepRawNonzero_normalizedZero_beta_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidualLinearMap
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy ≠ 0 ∧
      finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidualLinearMap
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy = 0 :=
  ⟨finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidual_beta_zero_ne_zero
      H energyIdentity energyNontrivial hEnergy,
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidual_beta_zero_eq_zero
      H energyIdentity energyNontrivial hEnergy⟩

end

end MathlibAnalytic
end MGAP4D
