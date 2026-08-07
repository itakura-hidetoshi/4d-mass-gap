import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeTwoStepConfigurationFiberKernelEvaluation
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Exact one-step configuration-fibre kernel compatibility statement.  This is
a named condition, not an unconditional assertion about the model. -/
def Z2FiniteEvenFourTorusOneStepConfigurationFiberKernelCompatible
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) : Prop :=
  ∀ (A : FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement H))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H),
    (∑ B : FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement H),
      if finiteEvenFourTorusZ2SliceConfigurationCoarseMap H B = b then
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
            (finiteEvenFourTorusDoubleRefinement H)
            β energyIdentity energyNontrivial hβ hEnergy B A *
          finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H B
      else 0) =
      finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H A *
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
          H β energyIdentity energyNontrivial hβ hEnergy b
          (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H A)

/-- Exact direct two-step configuration-fibre kernel compatibility statement. -/
def Z2FiniteEvenFourTorusTwoStepConfigurationFiberKernelCompatible
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) : Prop :=
  ∀ (A : FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H)))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H),
    (∑ B : FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H)),
      if finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
          (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
            (finiteEvenFourTorusDoubleRefinement H) B) = b then
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
            (finiteEvenFourTorusDoubleRefinement
              (finiteEvenFourTorusDoubleRefinement H))
            β energyIdentity energyNontrivial hβ hEnergy B A *
          finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale H B
      else 0) =
      finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale H A *
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
          H β energyIdentity energyNontrivial hβ hEnergy b
          (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
            (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
              (finiteEvenFourTorusDoubleRefinement H) A))

/-- Package-I reduces the one-step raw operator obstruction exactly to the
explicit configuration-fibre finite-sum equation. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidual_eq_zero_iff_explicitConfigurationFiberKernelCompatible
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      Z2FiniteEvenFourTorusOneStepConfigurationFiberKernelCompatible
        H β energyIdentity energyNontrivial hβ hEnergy := by
  rw [finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidual_eq_zero_iff_configurationFiberKernelCoefficients]
  unfold Z2FiniteEvenFourTorusOneStepConfigurationFiberKernelCompatible
  constructor
  · intro h A b
    have hab := h A b
    unfold finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficient at hab
    unfold finiteFiberPushforwardCoefficient at hab
    unfold finiteEvenFourTorusZ2GaugeInvariantOneStepFineKernelWeight at hab
    unfold finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight at hab
    exact hab
  · intro h A b
    have hab := h A b
    unfold finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficient
    unfold finiteFiberPushforwardCoefficient
    unfold finiteEvenFourTorusZ2GaugeInvariantOneStepFineKernelWeight
    unfold finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight
    exact hab

/-- Package-I reduces the direct two-step raw operator obstruction exactly to
the explicit composed-coarse-map fibre equation. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidual_eq_zero_iff_explicitConfigurationFiberKernelCompatible
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      Z2FiniteEvenFourTorusTwoStepConfigurationFiberKernelCompatible
        H β energyIdentity energyNontrivial hβ hEnergy := by
  rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidual_eq_zero_iff_configurationFiberKernelCoefficients]
  unfold Z2FiniteEvenFourTorusTwoStepConfigurationFiberKernelCompatible
  constructor
  · intro h A b
    have hab := h A b
    rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient_eq_direct]
      at hab
    unfold finiteFiberPushforwardCoefficient at hab
    unfold finiteEvenFourTorusZ2GaugeInvariantTwoStepFineKernelWeight at hab
    unfold finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight at hab
    exact hab
  · intro h A b
    have hab := h A b
    rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient_eq_direct]
    unfold finiteFiberPushforwardCoefficient
    unfold finiteEvenFourTorusZ2GaugeInvariantTwoStepFineKernelWeight
    unfold finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight
    exact hab

/-- One explicit failed one-step configuration-fibre equation certifies that
the actual one-step raw residual is nonzero. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidual_ne_zero_of_configurationFiberKernelMismatch
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (hMismatch :
      ¬ Z2FiniteEvenFourTorusOneStepConfigurationFiberKernelCompatible
        H β energyIdentity energyNontrivial hβ hEnergy) :
    finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy ≠ 0 := by
  intro hZero
  exact hMismatch
    ((finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidual_eq_zero_iff_explicitConfigurationFiberKernelCompatible
      H β energyIdentity energyNontrivial hβ hEnergy).1 hZero)

/-- One explicit failed direct two-step configuration-fibre equation certifies
that the direct raw residual is nonzero. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidual_ne_zero_of_configurationFiberKernelMismatch
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (hMismatch :
      ¬ Z2FiniteEvenFourTorusTwoStepConfigurationFiberKernelCompatible
        H β energyIdentity energyNontrivial hβ hEnergy) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy ≠ 0 := by
  intro hZero
  exact hMismatch
    ((finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidual_eq_zero_iff_explicitConfigurationFiberKernelCompatible
      H β energyIdentity energyNontrivial hβ hEnergy).1 hZero)

/-- Strong one-step projective compatibility stated at the configuration-fibre
kernel level. -/
structure Z2FiniteEvenFourTorusOneStepConfigurationFiberStrongCompatibilityData
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) where
  configurationFiberKernel :
    Z2FiniteEvenFourTorusOneStepConfigurationFiberKernelCompatible
      H β energyIdentity energyNontrivial hβ hEnergy
  normalization :
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
        (finiteEvenFourTorusDoubleRefinement H)
        β energyIdentity energyNontrivial hβ hEnergy =
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
        H β energyIdentity energyNontrivial hβ hEnergy
  fixedSector :
    FiniteDimensionalGroundProjectorDecompositionCompatible
      (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
        (finiteEvenFourTorusDoubleRefinement H)
        β energyIdentity energyNontrivial hβ hEnergy)
      (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
        H β energyIdentity energyNontrivial hβ hEnergy)
      (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H).toLinearMap

/-- Strong direct two-step projective compatibility stated at the explicit
configuration-fibre kernel level. -/
structure Z2FiniteEvenFourTorusTwoStepConfigurationFiberStrongCompatibilityData
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) where
  configurationFiberKernel :
    Z2FiniteEvenFourTorusTwoStepConfigurationFiberKernelCompatible
      H β energyIdentity energyNontrivial hβ hEnergy
  normalization :
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H))
        β energyIdentity energyNontrivial hβ hEnergy =
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
        H β energyIdentity energyNontrivial hβ hEnergy
  fixedSector :
    FiniteDimensionalGroundProjectorDecompositionCompatible
      (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H))
        β energyIdentity energyNontrivial hβ hEnergy)
      (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
        H β energyIdentity energyNontrivial hβ hEnergy)
      (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingLinearIsometry H).toLinearMap

/-- One-step configuration-fibre strong compatibility annihilates the actual
one-step ground-lifted orbit obstruction. -/
theorem Z2FiniteEvenFourTorusOneStepConfigurationFiberStrongCompatibilityData.liftedObstruction_eq_zero
    {H : ℕ}
    {β energyIdentity energyNontrivial : ℝ}
    {hβ : 0 ≤ β}
    {hEnergy : energyIdentity ≤ energyNontrivial}
    (D : Z2FiniteEvenFourTorusOneStepConfigurationFiberStrongCompatibilityData
      H β energyIdentity energyNontrivial hβ hEnergy) :
    finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction
        H β energyIdentity energyNontrivial hβ hEnergy = 0 := by
  have hRaw :=
    (finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidual_eq_zero_iff_explicitConfigurationFiberKernelCompatible
      H β energyIdentity energyNontrivial hβ hEnergy).2 D.configurationFiberKernel
  have hTransfer :
      finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidualLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy = 0 := by
    rw [finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidual_raw_normalization_decomposition]
    rw [hRaw, D.normalization]
    simp
  have hGround :
      finiteEvenFourTorusZ2GaugeInvariantGroundProjectorIntertwiningResidualLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy = 0 :=
    (finiteEvenFourTorusZ2GaugeInvariantGroundProjectorIntertwiningResidual_eq_zero_iff_fixedSectorDecomposition
      H β energyIdentity energyNontrivial hβ hEnergy).2 D.fixedSector
  apply
    (finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction_eq_zero_iff_transfer_eq_ground
      H β energyIdentity energyNontrivial hβ hEnergy).2
  rw [hTransfer, hGround]

/-- Direct two-step configuration-fibre strong compatibility annihilates the
actual direct two-step ground-lifted orbit obstruction. -/
theorem Z2FiniteEvenFourTorusTwoStepConfigurationFiberStrongCompatibilityData.liftedObstruction_eq_zero
    {H : ℕ}
    {β energyIdentity energyNontrivial : ℝ}
    {hβ : 0 ≤ β}
    {hEnergy : energyIdentity ≤ energyNontrivial}
    (D : Z2FiniteEvenFourTorusTwoStepConfigurationFiberStrongCompatibilityData
      H β energyIdentity energyNontrivial hβ hEnergy) :
    finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction
        H β energyIdentity energyNontrivial hβ hEnergy = 0 := by
  have hRaw :=
    (finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidual_eq_zero_iff_explicitConfigurationFiberKernelCompatible
      H β energyIdentity energyNontrivial hβ hEnergy).2 D.configurationFiberKernel
  have hTransfer :
      finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidualLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy = 0 := by
    rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidual_raw_normalization_decomposition]
    rw [hRaw, D.normalization]
    simp
  have hGround :
      finiteEvenFourTorusZ2GaugeInvariantTwoStepGroundProjectorIntertwiningResidualLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy = 0 :=
    (finiteEvenFourTorusZ2GaugeInvariantTwoStepGroundProjectorIntertwiningResidual_eq_zero_iff_fixedSectorDecomposition
      H β energyIdentity energyNontrivial hβ hEnergy).2 D.fixedSector
  apply
    (finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction_eq_zero_iff_transfer_eq_ground
      H β energyIdentity energyNontrivial hβ hEnergy).2
  rw [hTransfer, hGround]

/-- Full Package-I bundle joining generic invariance, one-step configuration
fibres, direct two-step configuration fibres, and exact compatibility receipts. -/
structure Z2FiniteEvenFourTorusCrossVolumeConfigurationFiberKernelFullPackage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) where
  oneStep :
    Z2FiniteEvenFourTorusCrossVolumeOneStepConfigurationFiberKernelPackage
      H β energyIdentity energyNontrivial hβ hEnergy
  twoStep :
    Z2FiniteEvenFourTorusCrossVolumeTwoStepConfigurationFiberKernelPackage
      H β energyIdentity energyNontrivial hβ hEnergy

/-- Construct the complete Package-I receipt. -/
noncomputable def z2FiniteEvenFourTorusCrossVolumeConfigurationFiberKernelFullPackage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Z2FiniteEvenFourTorusCrossVolumeConfigurationFiberKernelFullPackage
      H β energyIdentity energyNontrivial hβ hEnergy where
  oneStep :=
    z2FiniteEvenFourTorusCrossVolumeOneStepConfigurationFiberKernelPackage
      H β energyIdentity energyNontrivial hβ hEnergy
  twoStep :=
    z2FiniteEvenFourTorusCrossVolumeTwoStepConfigurationFiberKernelPackage
      H β energyIdentity energyNontrivial hβ hEnergy

end

end MathlibAnalytic
end MGAP4D
