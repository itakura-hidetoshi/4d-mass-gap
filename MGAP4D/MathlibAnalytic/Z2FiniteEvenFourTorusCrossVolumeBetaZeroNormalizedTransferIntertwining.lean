import MGAP4D.MathlibAnalytic.FiniteConstantOneKernelNormalization
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeBetaZeroConfigurationFiberMismatch
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeTwoStepKernelFixedSectorCompatibility
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- At zero coupling the exact temporal-link averaged finite `Z₂` one-slab
kernel is the constant-one kernel. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_beta_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy A B = 1 := by
  rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_apply]
  simp only [zero_mul, neg_zero, Real.exp_zero]
  have hcard :
      (Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simpa [hcard]

/-- The raw zero-coupling one-slab transfer has exact operator norm equal to
the number of boundary configurations. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer_norm_beta_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    ‖finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy‖ =
      (Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ) := by
  unfold finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer
  have hk :
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
          H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy =
        fun _ _ => (1 : ℝ) := by
    funext A B
    exact finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_beta_zero
      H energyIdentity energyNontrivial hEnergy A B
  rw [hk, finiteKernelOperator_one_norm]

/-- The actual ambient op-norm normalization scalar at `β = 0` is exactly the
inverse boundary-configuration cardinality. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar_beta_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy =
      (Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)⁻¹ := by
  unfold finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
  rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabRawTransfer_norm_beta_zero]

/-- The actual ambient normalized `β = 0` transfer is literal uniform averaging
of the boundary wavefunction. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer_apply_beta_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (f : FiniteEvenFourTorusZ2SliceHilbert H)
    (A : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy f A =
      (Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)⁻¹ *
        ∑ B : FiniteEvenFourTorusZ2SliceConfiguration H, f B := by
  unfold finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer
  have hk :
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
          H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy =
        fun _ _ => (1 : ℝ) := by
    funext X Y
    exact finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_beta_zero
      H energyIdentity energyNontrivial hEnergy X Y
  rw [hk]
  exact finiteKernelNormalizedOperator_one_apply f A

/-- The invariant-sector normalized zero-coupling transfer has the same uniform
average formula on its ambient coordinates. -/
theorem finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_apply_coe_beta_zero
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
  exact finiteEvenFourTorusZ2UnfixedGaugeOneSlabTransfer_apply_beta_zero
    H energyIdentity energyNontrivial hEnergy f.1 A

/-- The fibre multiplicity that destroys raw cross-volume intertwining is
cancelled exactly by operator-norm normalization at `β = 0`. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidual_beta_zero_eq_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidualLinearMap
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy = 0 := by
  apply LinearMap.ext
  intro f
  rw [finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidualLinearMap_apply]
  apply sub_eq_zero.mpr
  apply Subtype.ext
  ext A
  rw [finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_apply_coe_beta_zero]
  rw [finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding_apply_coe_eq_scale_mul_rawPullback]
  rw [finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer_apply_coe_beta_zero]
  simp_rw [finiteEvenFourTorusZ2GaugeInvariantCoarseEmbedding_apply_coe_eq_scale_mul_rawPullback]
  simp_rw [finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale_eq_cardinality]
  have havg :
      (Fintype.card
          (FiniteEvenFourTorusZ2SliceConfiguration
            (finiteEvenFourTorusDoubleRefinement H)) : ℝ)⁻¹ *
        (∑ B : FiniteEvenFourTorusZ2SliceConfiguration
            (finiteEvenFourTorusDoubleRefinement H),
          f.1 (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H B)) =
      (Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)⁻¹ *
        ∑ b : FiniteEvenFourTorusZ2SliceConfiguration H, f.1 b := by
    exact finiteSurjectiveGroupHom_uniformAverage_comp
      (finiteEvenFourTorusZ2SliceConfigurationCoarseHom H)
      (finiteEvenFourTorusZ2SliceConfigurationCoarseHom_surjective H)
      f.1
  rw [← Finset.mul_sum]
  calc
    (Fintype.card
        (FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement H)) : ℝ)⁻¹ *
        (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingCardinalityScale H *
          ∑ B : FiniteEvenFourTorusZ2SliceConfiguration
            (finiteEvenFourTorusDoubleRefinement H),
            f.1 (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H B)) =
      finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingCardinalityScale H *
        ((Fintype.card
          (FiniteEvenFourTorusZ2SliceConfiguration
            (finiteEvenFourTorusDoubleRefinement H)) : ℝ)⁻¹ *
          ∑ B : FiniteEvenFourTorusZ2SliceConfiguration
            (finiteEvenFourTorusDoubleRefinement H),
            f.1 (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H B)) := by ring
    _ = finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingCardinalityScale H *
        ((Fintype.card (FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ)⁻¹ *
          ∑ b : FiniteEvenFourTorusZ2SliceConfiguration H, f.1 b) := by
      rw [havg]

/-- Direct two-step normalized intertwining follows by composing the two exact
one-step zero-coupling intertwining identities along the canonical embedding
cocycle. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidual_beta_zero_eq_zero
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidualLinearMap
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy = 0 := by
  apply LinearMap.ext
  intro f
  have hCoarse := LinearMap.congr_fun
    (finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidual_beta_zero_eq_zero
      H energyIdentity energyNontrivial hEnergy) f
  rw [finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidualLinearMap_apply]
    at hCoarse
  have hCoarseEq :
      finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
          (finiteEvenFourTorusDoubleRefinement H)
          0 energyIdentity energyNontrivial (le_refl 0) hEnergy
          (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H f) =
        finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H
          (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
            H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy f) :=
    sub_eq_zero.mp hCoarse
  have hFine := LinearMap.congr_fun
    (finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidual_beta_zero_eq_zero
      (finiteEvenFourTorusDoubleRefinement H)
      energyIdentity energyNontrivial hEnergy)
    (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H f)
  rw [finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidualLinearMap_apply]
    at hFine
  have hFineEq :
      finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H))
          0 energyIdentity energyNontrivial (le_refl 0) hEnergy
          (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry
            (finiteEvenFourTorusDoubleRefinement H)
            (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H f)) =
        finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry
          (finiteEvenFourTorusDoubleRefinement H)
          (finiteEvenFourTorusZ2UnfixedGaugeInvariantOneSlabTransfer
            (finiteEvenFourTorusDoubleRefinement H)
            0 energyIdentity energyNontrivial (le_refl 0) hEnergy
            (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H f)) :=
    sub_eq_zero.mp hFine
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
            (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H f)) := hFineEq
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

/-- At `β = 0`, raw and normalized cross-volume conclusions are sharply
opposite: raw one-step/direct-two-step residuals are nonzero, while the actual
op-norm-normalized residuals vanish exactly. -/
structure Z2FiniteEvenFourTorusCrossVolumeBetaZeroNormalizedTransferPackage
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) where
  oneStepRawResidualNonzero :
    finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidualLinearMap
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy ≠ 0
  oneStepNormalizedResidualZero :
    finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidualLinearMap
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy = 0
  twoStepRawResidualNonzero :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidualLinearMap
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy ≠ 0
  twoStepNormalizedResidualZero :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidualLinearMap
        H 0 energyIdentity energyNontrivial (le_refl 0) hEnergy = 0

/-- Construct the complete beta-zero raw-versus-normalized cross-volume
intertwining receipt. -/
noncomputable def z2FiniteEvenFourTorusCrossVolumeBetaZeroNormalizedTransferPackage
    (H : ℕ)
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Z2FiniteEvenFourTorusCrossVolumeBetaZeroNormalizedTransferPackage
      H energyIdentity energyNontrivial hEnergy where
  oneStepRawResidualNonzero :=
    finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidual_beta_zero_ne_zero
      H energyIdentity energyNontrivial hEnergy
  oneStepNormalizedResidualZero :=
    finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidual_beta_zero_eq_zero
      H energyIdentity energyNontrivial hEnergy
  twoStepRawResidualNonzero :=
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidual_beta_zero_ne_zero
      H energyIdentity energyNontrivial hEnergy
  twoStepNormalizedResidualZero :=
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidual_beta_zero_eq_zero
      H energyIdentity energyNontrivial hEnergy

end

end MathlibAnalytic
end MGAP4D
