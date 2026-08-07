import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeOneStepOrbitFiberKernelCriterion
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeTwoStepKernelFixedSectorCompatibility
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProduct

noncomputable section

/-- Finest-volume raw-kernel coefficient for the direct two-step comparison,
including the exact two-step embedding scale. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantTwoStepFineKernelWeight
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))) : ℝ :=
  finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))
      β energyIdentity energyNontrivial hβ hEnergy B A *
    finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale H B

/-- Coarsest raw-kernel coefficient viewed from one finest evaluation
configuration in the direct two-step comparison. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale H A *
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
      H β energyIdentity energyNontrivial hβ hEnergy b
      (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
        (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
          (finiteEvenFourTorusDoubleRefinement H) A))

/-- Direct finest-to-coarsest orbit-fibre coefficient. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantTwoStepFineOrbitFiberKernelCoefficient
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H) : ℝ :=
  finiteGroupOrbitFiberCoefficient
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (FiniteEvenFourTorusZ2SliceConfiguration H)
    (fun B : FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H)) =>
      finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
        (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
          (finiteEvenFourTorusDoubleRefinement H) B))
    (finiteEvenFourTorusZ2GaugeInvariantTwoStepFineKernelWeight
      H β energyIdentity energyNontrivial hβ hEnergy A)
    q

/-- Coarsest orbit coefficient in the direct two-step comparison. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseOrbitKernelCoefficient
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H) : ℝ :=
  finiteGroupOrbitAggregateCoefficient
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (FiniteEvenFourTorusZ2SliceConfiguration H)
    (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight
      H β energyIdentity energyNontrivial hβ hEnergy A)
    q

/-- At a fixed finest evaluation configuration, the direct two-step raw-kernel
equation against every coarsest invariant observable is equivalent to equality
on every coarsest residual-gauge orbit. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepKernelEquation_iff_orbitFiberCoefficients
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))) :
    (∀ f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H,
      (∑ B : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H)),
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
            (finiteEvenFourTorusDoubleRefinement
              (finiteEvenFourTorusDoubleRefinement H))
            β energyIdentity energyNontrivial hβ hEnergy B A *
          (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale H B *
            f.1
              (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
                (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
                  (finiteEvenFourTorusDoubleRefinement H) B)))) =
        finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale H A *
          (∑ b : FiniteEvenFourTorusZ2SliceConfiguration H,
            finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
                H β energyIdentity energyNontrivial hβ hEnergy b
                (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
                  (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
                    (finiteEvenFourTorusDoubleRefinement H) A)) * f.1 b)) ↔
      ∀ q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H,
        finiteEvenFourTorusZ2GaugeInvariantTwoStepFineOrbitFiberKernelCoefficient
            H β energyIdentity energyNontrivial hβ hEnergy A q =
          finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseOrbitKernelCoefficient
            H β energyIdentity energyNontrivial hβ hEnergy A q := by
  have hGeneric :=
    finiteGroupInvariant_crossSum_eq_iff_orbitFiberSums
      (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
      (FiniteEvenFourTorusZ2SliceConfiguration H)
      (fun B : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H)) =>
        finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
          (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
            (finiteEvenFourTorusDoubleRefinement H) B))
      (finiteEvenFourTorusZ2GaugeInvariantTwoStepFineKernelWeight
        H β energyIdentity energyNontrivial hβ hEnergy A)
      (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight
        H β energyIdentity energyNontrivial hβ hEnergy A)
  simpa [finiteEvenFourTorusZ2GaugeInvariantTwoStepFineKernelWeight,
    finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight,
    finiteEvenFourTorusZ2GaugeInvariantTwoStepFineOrbitFiberKernelCoefficient,
    finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseOrbitKernelCoefficient,
    Finset.mul_sum, mul_assoc] using hGeneric

/-- Package-G direct two-step raw residual vanishes exactly when the actual
finest kernel and coarsest kernel agree after direct coarse-map/gauge-orbit
aggregation with the exact two-step embedding scale. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidual_eq_zero_iff_orbitFiberKernelCoefficients
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      ∀ (A : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H)))
        (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H),
        finiteEvenFourTorusZ2GaugeInvariantTwoStepFineOrbitFiberKernelCoefficient
            H β energyIdentity energyNontrivial hβ hEnergy A q =
          finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseOrbitKernelCoefficient
            H β energyIdentity energyNontrivial hβ hEnergy A q := by
  rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidual_eq_zero_iff_kernelEquation]
  constructor
  · intro h A
    exact
      (finiteEvenFourTorusZ2GaugeInvariantTwoStepKernelEquation_iff_orbitFiberCoefficients
        H β energyIdentity energyNontrivial hβ hEnergy A).1
        (fun f => h f A)
  · intro h f A
    exact
      (finiteEvenFourTorusZ2GaugeInvariantTwoStepKernelEquation_iff_orbitFiberCoefficients
        H β energyIdentity energyNontrivial hβ hEnergy A).2
        (h A) f

/-- Direct two-step configuration pushforward equals successive finest-to-
intermediate and intermediate-to-coarsest fibre pushforwards. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepFineKernelPushforward_cocycle
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteFiberPushforwardCoefficient
        (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H)
        (finiteFiberPushforwardCoefficient
          (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
            (finiteEvenFourTorusDoubleRefinement H))
          (finiteEvenFourTorusZ2GaugeInvariantTwoStepFineKernelWeight
            H β energyIdentity energyNontrivial hβ hEnergy A)) b =
      finiteFiberPushforwardCoefficient
        (fun B : FiniteEvenFourTorusZ2SliceConfiguration
            (finiteEvenFourTorusDoubleRefinement
              (finiteEvenFourTorusDoubleRefinement H)) =>
          finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
            (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
              (finiteEvenFourTorusDoubleRefinement H) B))
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepFineKernelWeight
          H β energyIdentity energyNontrivial hβ hEnergy A) b :=
  finiteFiberPushforwardCoefficient_comp
    (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H)
    (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
      (finiteEvenFourTorusDoubleRefinement H))
    (finiteEvenFourTorusZ2GaugeInvariantTwoStepFineKernelWeight
      H β energyIdentity energyNontrivial hβ hEnergy A) b

/-- The direct two-step orbit-fibre coefficient is therefore also the orbit
aggregation of the successive two-stage configuration pushforward. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepFineOrbitFiberKernelCoefficient_eq_successivePushforwardAggregate
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepFineOrbitFiberKernelCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A q =
      finiteGroupOrbitAggregateCoefficient
        (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
        (FiniteEvenFourTorusZ2SliceConfiguration H)
        (finiteFiberPushforwardCoefficient
          (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H)
          (finiteFiberPushforwardCoefficient
            (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
              (finiteEvenFourTorusDoubleRefinement H))
            (finiteEvenFourTorusZ2GaugeInvariantTwoStepFineKernelWeight
              H β energyIdentity energyNontrivial hβ hEnergy A))) q := by
  rw [← finiteEvenFourTorusZ2GaugeInvariantTwoStepFineKernelPushforward_cocycle
    H β energyIdentity energyNontrivial hβ hEnergy A]
  symm
  exact finiteGroupOrbitAggregate_fiberPushforward
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (FiniteEvenFourTorusZ2SliceConfiguration H)
    (fun B : FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H)) =>
      finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
        (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
          (finiteEvenFourTorusDoubleRefinement H) B))
    (finiteEvenFourTorusZ2GaugeInvariantTwoStepFineKernelWeight
      H β energyIdentity energyNontrivial hβ hEnergy A) q

/-- Strong direct two-step projective compatibility at orbit-fibre kernel,
normalization, and fixed-sector levels is sufficient for the full direct
Package-F ground-lifted obstruction to vanish. -/
theorem finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction_eq_zero_of_orbitFiberKernel_normalization_fixedSector
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (hKernel :
      ∀ (A : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H)))
        (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H),
        finiteEvenFourTorusZ2GaugeInvariantTwoStepFineOrbitFiberKernelCoefficient
            H β energyIdentity energyNontrivial hβ hEnergy A q =
          finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseOrbitKernelCoefficient
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
  have hRaw :
      finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidualLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy = 0 :=
    (finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidual_eq_zero_iff_orbitFiberKernelCoefficients
      H β energyIdentity energyNontrivial hβ hEnergy).2 hKernel
  have hTransfer :
      finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidualLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy = 0 := by
    rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabTransferIntertwiningResidual_raw_normalization_decomposition]
    rw [hRaw, hNormalization]
    simp
  have hGround :
      finiteEvenFourTorusZ2GaugeInvariantTwoStepGroundProjectorIntertwiningResidualLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy = 0 :=
    (finiteEvenFourTorusZ2GaugeInvariantTwoStepGroundProjectorIntertwiningResidual_eq_zero_iff_fixedSectorDecomposition
      H β energyIdentity energyNontrivial hβ hEnergy).2 hFixedSector
  apply
    (finiteEvenFourTorusZ2GaugeOrbitTwoStepGroundLiftedIntertwiningObstruction_eq_zero_iff_transfer_eq_ground
      H β energyIdentity energyNontrivial hβ hEnergy).2
  rw [hTransfer, hGround]

/-- Audit-visible direct two-step Package-H bundle. -/
structure Z2FiniteEvenFourTorusCrossVolumeTwoStepOrbitFiberKernelPackage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) where
  fineOrbitFiberKernelCoefficient :
    FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H)) →
      FiniteEvenFourTorusZ2ResidualGaugeOrbit H → ℝ
  fineOrbitFiberKernelCoefficient_eq : fineOrbitFiberKernelCoefficient =
    finiteEvenFourTorusZ2GaugeInvariantTwoStepFineOrbitFiberKernelCoefficient
      H β energyIdentity energyNontrivial hβ hEnergy
  coarseOrbitKernelCoefficient :
    FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H)) →
      FiniteEvenFourTorusZ2ResidualGaugeOrbit H → ℝ
  coarseOrbitKernelCoefficient_eq : coarseOrbitKernelCoefficient =
    finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseOrbitKernelCoefficient
      H β energyIdentity energyNontrivial hβ hEnergy
  rawResidualCriterion :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      ∀ A q, fineOrbitFiberKernelCoefficient A q =
        coarseOrbitKernelCoefficient A q
  pushforwardCocycle :
    ∀ A b,
      finiteFiberPushforwardCoefficient
          (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H)
          (finiteFiberPushforwardCoefficient
            (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
              (finiteEvenFourTorusDoubleRefinement H))
            (finiteEvenFourTorusZ2GaugeInvariantTwoStepFineKernelWeight
              H β energyIdentity energyNontrivial hβ hEnergy A)) b =
        finiteFiberPushforwardCoefficient
          (fun B : FiniteEvenFourTorusZ2SliceConfiguration
              (finiteEvenFourTorusDoubleRefinement
                (finiteEvenFourTorusDoubleRefinement H)) =>
            finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
              (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
                (finiteEvenFourTorusDoubleRefinement H) B))
          (finiteEvenFourTorusZ2GaugeInvariantTwoStepFineKernelWeight
            H β energyIdentity energyNontrivial hβ hEnergy A) b

/-- Construct the two-step Package-H receipt. -/
noncomputable def z2FiniteEvenFourTorusCrossVolumeTwoStepOrbitFiberKernelPackage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Z2FiniteEvenFourTorusCrossVolumeTwoStepOrbitFiberKernelPackage
      H β energyIdentity energyNontrivial hβ hEnergy where
  fineOrbitFiberKernelCoefficient :=
    finiteEvenFourTorusZ2GaugeInvariantTwoStepFineOrbitFiberKernelCoefficient
      H β energyIdentity energyNontrivial hβ hEnergy
  fineOrbitFiberKernelCoefficient_eq := rfl
  coarseOrbitKernelCoefficient :=
    finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseOrbitKernelCoefficient
      H β energyIdentity energyNontrivial hβ hEnergy
  coarseOrbitKernelCoefficient_eq := rfl
  rawResidualCriterion :=
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidual_eq_zero_iff_orbitFiberKernelCoefficients
      H β energyIdentity energyNontrivial hβ hEnergy
  pushforwardCocycle :=
    finiteEvenFourTorusZ2GaugeInvariantTwoStepFineKernelPushforward_cocycle
      H β energyIdentity energyNontrivial hβ hEnergy

end

end MathlibAnalytic
end MGAP4D
