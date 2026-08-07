import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeTwoStepOrbitFiberKernelCriterion
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A single failed one-step orbit-fibre coefficient equality is an explicit
certificate that the actual raw one-step transfer residual is nonzero. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidual_ne_zero_of_orbitFiberKernelMismatch
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H)
    (hMismatch :
      finiteEvenFourTorusZ2GaugeInvariantOneStepFineOrbitFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q ≠
        finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseOrbitKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q) :
    finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy ≠ 0 := by
  intro hZero
  have hAll :=
    (finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidual_eq_zero_iff_orbitFiberKernelCoefficients
      H β energyIdentity energyNontrivial hβ hEnergy).1 hZero
  exact hMismatch (hAll A q)

/-- A single failed direct two-step orbit-fibre coefficient equality certifies
that the actual direct two-step raw transfer residual is nonzero. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidual_ne_zero_of_orbitFiberKernelMismatch
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H)
    (hMismatch :
      finiteEvenFourTorusZ2GaugeInvariantTwoStepFineOrbitFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q ≠
        finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseOrbitKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy ≠ 0 := by
  intro hZero
  have hAll :=
    (finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidual_eq_zero_iff_orbitFiberKernelCoefficients
      H β energyIdentity energyNontrivial hβ hEnergy).1 hZero
  exact hMismatch (hAll A q)

/-- Strong one-step projective compatibility data.  This is deliberately a
structure of hypotheses, not an unconditional model claim. -/
structure Z2FiniteEvenFourTorusOneStepStrongProjectiveCompatibilityData
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) where
  orbitFiberKernel :
    ∀ (A : FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement H))
      (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H),
      finiteEvenFourTorusZ2GaugeInvariantOneStepFineOrbitFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q =
        finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseOrbitKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q
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

/-- Strong direct two-step projective compatibility data. -/
structure Z2FiniteEvenFourTorusTwoStepStrongProjectiveCompatibilityData
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) where
  orbitFiberKernel :
    ∀ (A : FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H)))
      (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H),
      finiteEvenFourTorusZ2GaugeInvariantTwoStepFineOrbitFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q =
        finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseOrbitKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q
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

/-- One-step strong projective compatibility kills the actual one-step
orbit-carrier ground-lifted obstruction. -/
theorem Z2FiniteEvenFourTorusOneStepStrongProjectiveCompatibilityData.liftedObstruction_eq_zero
    {H : ℕ}
    {β energyIdentity energyNontrivial : ℝ}
    {hβ : 0 ≤ β}
    {hEnergy : energyIdentity ≤ energyNontrivial}
    (D : Z2FiniteEvenFourTorusOneStepStrongProjectiveCompatibilityData
      H β energyIdentity energyNontrivial hβ hEnergy) :
    finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction
        H β energyIdentity energyNontrivial hβ hEnergy = 0 :=
  finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction_eq_zero_of_orbitFiberKernel_normalization_fixedSector
    H β energyIdentity energyNontrivial hβ hEnergy
    D.orbitFiberKernel D.normalization D.fixedSector

/-- Direct two-step strong projective compatibility kills the actual direct
two-step orbit-carrier ground-lifted obstruction. -/
theorem Z2FiniteEvenFourTorusTwoStepStrongProjectiveCompatibilityData.liftedObstruction_eq_zero
    {H : ℕ}
    {β energyIdentity energyNontrivial : ℝ}
    {hβ : 0 ≤ β}
    {hEnergy : energyIdentity ≤ energyNontrivial}
    (D : Z2FiniteEvenFourTorusTwoStepStrongProjectiveCompatibilityData
      H β energyIdentity energyNontrivial hβ hEnergy) :
    finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction
        H β energyIdentity energyNontrivial hβ hEnergy = 0 :=
  finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction_eq_zero_of_orbitFiberKernel_normalization_fixedSector
    H β energyIdentity energyNontrivial hβ hEnergy
    D.orbitFiberKernel D.normalization D.fixedSector

/-- Full one-step/two-step strong projective compatibility data. -/
structure Z2FiniteEvenFourTorusCrossVolumeStrongProjectiveCompatibilityData
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) where
  oneStep :
    Z2FiniteEvenFourTorusOneStepStrongProjectiveCompatibilityData
      H β energyIdentity energyNontrivial hβ hEnergy
  twoStep :
    Z2FiniteEvenFourTorusTwoStepStrongProjectiveCompatibilityData
      H β energyIdentity energyNontrivial hβ hEnergy

/-- Full strong compatibility annihilates both the one-step and direct two-step
actual ground-lifted cross-volume obstructions. -/
theorem Z2FiniteEvenFourTorusCrossVolumeStrongProjectiveCompatibilityData.liftedObstructions_eq_zero
    {H : ℕ}
    {β energyIdentity energyNontrivial : ℝ}
    {hβ : 0 ≤ β}
    {hEnergy : energyIdentity ≤ energyNontrivial}
    (D : Z2FiniteEvenFourTorusCrossVolumeStrongProjectiveCompatibilityData
      H β energyIdentity energyNontrivial hβ hEnergy) :
    finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ∧
      finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction
        H β energyIdentity energyNontrivial hβ hEnergy = 0 := by
  exact ⟨D.oneStep.liftedObstruction_eq_zero,
    D.twoStep.liftedObstruction_eq_zero⟩

/-- Audit-visible full Package-H bundle joining the one-step and direct
 two-step orbit-fibre kernel receipts. -/
structure Z2FiniteEvenFourTorusCrossVolumeOrbitFiberKernelFullPackage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) where
  oneStep :
    Z2FiniteEvenFourTorusCrossVolumeOneStepOrbitFiberKernelPackage
      H β energyIdentity energyNontrivial hβ hEnergy
  twoStep :
    Z2FiniteEvenFourTorusCrossVolumeTwoStepOrbitFiberKernelPackage
      H β energyIdentity energyNontrivial hβ hEnergy

/-- Construct the full Package-H receipt. -/
noncomputable def z2FiniteEvenFourTorusCrossVolumeOrbitFiberKernelFullPackage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Z2FiniteEvenFourTorusCrossVolumeOrbitFiberKernelFullPackage
      H β energyIdentity energyNontrivial hβ hEnergy where
  oneStep :=
    z2FiniteEvenFourTorusCrossVolumeOneStepOrbitFiberKernelPackage
      H β energyIdentity energyNontrivial hβ hEnergy
  twoStep :=
    z2FiniteEvenFourTorusCrossVolumeTwoStepOrbitFiberKernelPackage
      H β energyIdentity energyNontrivial hβ hEnergy

end

end MathlibAnalytic
end MGAP4D
