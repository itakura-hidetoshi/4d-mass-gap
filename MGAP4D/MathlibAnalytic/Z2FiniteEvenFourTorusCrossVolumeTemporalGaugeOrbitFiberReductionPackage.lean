import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeTwoStepTemporalGaugeOrbitFiberReduction
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeOrbitFiberKernelPackage
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Temporal-gauge one-step kernel compatibility, together with the unchanged
normalization and fixed-sector hypotheses, is sufficient for the actual full
one-step ground-lifted obstruction to vanish. -/
theorem finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction_eq_zero_of_temporalGaugeOrbitFiberKernel_normalization_fixedSector
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (hKernel :
      ∀ (A : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement H))
        (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H),
        finiteEvenFourTorusZ2GaugeInvariantOneStepTemporalGaugeFineOrbitFiberKernelCoefficient
            H β energyIdentity energyNontrivial hβ hEnergy A q =
          finiteEvenFourTorusZ2GaugeInvariantOneStepTemporalGaugeCoarseOrbitKernelCoefficient
            H β energyIdentity energyNontrivial hβ hEnergy A q)
    (hNormalization :
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
          (finiteEvenFourTorusDoubleRefinement H)
          β energyIdentity energyNontrivial hβ hEnergy =
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
          H β energyIdentity energyNontrivial hβ hEnergy)
    (hFixedSector :
      FiniteDimensionalGroundProjectorDecompositionCompatible
        (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
          (finiteEvenFourTorusDoubleRefinement H)
          β energyIdentity energyNontrivial hβ hEnergy)
        (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
          H β energyIdentity energyNontrivial hβ hEnergy)
        (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingLinearIsometry H).toLinearMap) :
    finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction
        H β energyIdentity energyNontrivial hβ hEnergy = 0 := by
  have hKernelUnfixed :
      ∀ (A : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement H))
        (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H),
        finiteEvenFourTorusZ2GaugeInvariantOneStepFineOrbitFiberKernelCoefficient
            H β energyIdentity energyNontrivial hβ hEnergy A q =
          finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseOrbitKernelCoefficient
            H β energyIdentity energyNontrivial hβ hEnergy A q := by
    intro A q
    calc
      finiteEvenFourTorusZ2GaugeInvariantOneStepFineOrbitFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q =
        finiteEvenFourTorusZ2GaugeInvariantOneStepTemporalGaugeFineOrbitFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q :=
        finiteEvenFourTorusZ2GaugeInvariantOneStepFineOrbitFiberKernelCoefficient_eq_temporalGauge
          H β energyIdentity energyNontrivial hβ hEnergy A q
      _ = finiteEvenFourTorusZ2GaugeInvariantOneStepTemporalGaugeCoarseOrbitKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q := hKernel A q
      _ = finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseOrbitKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q :=
        (finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseOrbitKernelCoefficient_eq_temporalGauge
          H β energyIdentity energyNontrivial hβ hEnergy A q).symm
  exact finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction_eq_zero_of_orbitFiberKernel_normalization_fixedSector
    H β energyIdentity energyNontrivial hβ hEnergy
    hKernelUnfixed hNormalization hFixedSector

/-- Temporal-gauge direct two-step kernel compatibility, together with the
finest/coarsest normalization equality and direct fixed-sector compatibility,
kills the actual direct two-step ground-lifted obstruction. -/
theorem finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction_eq_zero_of_temporalGaugeOrbitFiberKernel_normalization_fixedSector
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (hKernel :
      ∀ (A : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H)))
        (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H),
        finiteEvenFourTorusZ2GaugeInvariantTwoStepTemporalGaugeFineOrbitFiberKernelCoefficient
            H β energyIdentity energyNontrivial hβ hEnergy A q =
          finiteEvenFourTorusZ2GaugeInvariantTwoStepTemporalGaugeCoarseOrbitKernelCoefficient
            H β energyIdentity energyNontrivial hβ hEnergy A q)
    (hNormalization :
      finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H))
          β energyIdentity energyNontrivial hβ hEnergy =
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabNormalizationScalar
          H β energyIdentity energyNontrivial hβ hEnergy)
    (hFixedSector :
      FiniteDimensionalGroundProjectorDecompositionCompatible
        (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H))
          β energyIdentity energyNontrivial hβ hEnergy)
        (finiteEvenFourTorusZ2UnfixedGaugeInvariantSpectralData
          H β energyIdentity energyNontrivial hβ hEnergy)
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingLinearIsometry H).toLinearMap) :
    finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction
        H β energyIdentity energyNontrivial hβ hEnergy = 0 := by
  have hKernelUnfixed :
      ∀ (A : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H)))
        (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H),
        finiteEvenFourTorusZ2GaugeInvariantTwoStepFineOrbitFiberKernelCoefficient
            H β energyIdentity energyNontrivial hβ hEnergy A q =
          finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseOrbitKernelCoefficient
            H β energyIdentity energyNontrivial hβ hEnergy A q := by
    intro A q
    calc
      finiteEvenFourTorusZ2GaugeInvariantTwoStepFineOrbitFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q =
        finiteEvenFourTorusZ2GaugeInvariantTwoStepTemporalGaugeFineOrbitFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q :=
        finiteEvenFourTorusZ2GaugeInvariantTwoStepFineOrbitFiberKernelCoefficient_eq_temporalGauge
          H β energyIdentity energyNontrivial hβ hEnergy A q
      _ = finiteEvenFourTorusZ2GaugeInvariantTwoStepTemporalGaugeCoarseOrbitKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q := hKernel A q
      _ = finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseOrbitKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q :=
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseOrbitKernelCoefficient_eq_temporalGauge
          H β energyIdentity energyNontrivial hβ hEnergy A q).symm
  exact finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction_eq_zero_of_orbitFiberKernel_normalization_fixedSector
    H β energyIdentity energyNontrivial hβ hEnergy
    hKernelUnfixed hNormalization hFixedSector

/-- Strong one-step projective compatibility formulated entirely with the
temporal-gauge Gram-kernel orbit-fibre condition at the kernel level. -/
structure Z2FiniteEvenFourTorusOneStepTemporalGaugeStrongProjectiveCompatibilityData
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) where
  temporalGaugeOrbitFiberKernel :
    ∀ (A : FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement H))
      (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H),
      finiteEvenFourTorusZ2GaugeInvariantOneStepTemporalGaugeFineOrbitFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q =
        finiteEvenFourTorusZ2GaugeInvariantOneStepTemporalGaugeCoarseOrbitKernelCoefficient
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

/-- Strong direct two-step compatibility with temporal-gauge kernel data. -/
structure Z2FiniteEvenFourTorusTwoStepTemporalGaugeStrongProjectiveCompatibilityData
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) where
  temporalGaugeOrbitFiberKernel :
    ∀ (A : FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H)))
      (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H),
      finiteEvenFourTorusZ2GaugeInvariantTwoStepTemporalGaugeFineOrbitFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q =
        finiteEvenFourTorusZ2GaugeInvariantTwoStepTemporalGaugeCoarseOrbitKernelCoefficient
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

/-- The one-step temporal-gauge strong data kills the actual one-step lifted
obstruction. -/
theorem Z2FiniteEvenFourTorusOneStepTemporalGaugeStrongProjectiveCompatibilityData.liftedObstruction_eq_zero
    {H : ℕ}
    {β energyIdentity energyNontrivial : ℝ}
    {hβ : 0 ≤ β}
    {hEnergy : energyIdentity ≤ energyNontrivial}
    (D : Z2FiniteEvenFourTorusOneStepTemporalGaugeStrongProjectiveCompatibilityData
      H β energyIdentity energyNontrivial hβ hEnergy) :
    finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction
        H β energyIdentity energyNontrivial hβ hEnergy = 0 :=
  finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction_eq_zero_of_temporalGaugeOrbitFiberKernel_normalization_fixedSector
    H β energyIdentity energyNontrivial hβ hEnergy
    D.temporalGaugeOrbitFiberKernel D.normalization D.fixedSector

/-- The direct two-step temporal-gauge strong data kills the actual direct
lifted obstruction. -/
theorem Z2FiniteEvenFourTorusTwoStepTemporalGaugeStrongProjectiveCompatibilityData.liftedObstruction_eq_zero
    {H : ℕ}
    {β energyIdentity energyNontrivial : ℝ}
    {hβ : 0 ≤ β}
    {hEnergy : energyIdentity ≤ energyNontrivial}
    (D : Z2FiniteEvenFourTorusTwoStepTemporalGaugeStrongProjectiveCompatibilityData
      H β energyIdentity energyNontrivial hβ hEnergy) :
    finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction
        H β energyIdentity energyNontrivial hβ hEnergy = 0 :=
  finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction_eq_zero_of_temporalGaugeOrbitFiberKernel_normalization_fixedSector
    H β energyIdentity energyNontrivial hβ hEnergy
    D.temporalGaugeOrbitFiberKernel D.normalization D.fixedSector

/-- Final one-step/direct-two-step Package-I bundle. -/
structure Z2FiniteEvenFourTorusCrossVolumeTemporalGaugeOrbitFiberReductionFullPackage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) where
  oneStep :
    Z2FiniteEvenFourTorusCrossVolumeOneStepTemporalGaugeOrbitFiberReductionPackage
      H β energyIdentity energyNontrivial hβ hEnergy
  twoStep :
    Z2FiniteEvenFourTorusCrossVolumeTwoStepTemporalGaugeOrbitFiberReductionPackage
      H β energyIdentity energyNontrivial hβ hEnergy

/-- Construct the complete Package-I reduction receipt. -/
noncomputable def z2FiniteEvenFourTorusCrossVolumeTemporalGaugeOrbitFiberReductionFullPackage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Z2FiniteEvenFourTorusCrossVolumeTemporalGaugeOrbitFiberReductionFullPackage
      H β energyIdentity energyNontrivial hβ hEnergy where
  oneStep :=
    z2FiniteEvenFourTorusCrossVolumeOneStepTemporalGaugeOrbitFiberReductionPackage
      H β energyIdentity energyNontrivial hβ hEnergy
  twoStep :=
    z2FiniteEvenFourTorusCrossVolumeTwoStepTemporalGaugeOrbitFiberReductionPackage
      H β energyIdentity energyNontrivial hβ hEnergy

end

end MathlibAnalytic
end MGAP4D
