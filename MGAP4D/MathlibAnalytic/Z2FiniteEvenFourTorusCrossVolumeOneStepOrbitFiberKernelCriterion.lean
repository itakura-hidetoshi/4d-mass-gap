import MGAP4D.MathlibAnalytic.FiniteGroupInvariantOrbitFiberKernelCriterion
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeKernelFixedSectorCompatibility
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators InnerProduct

noncomputable section

/-- Fine-volume raw-kernel coefficient, including the exact normalized
coarse-embedding pointwise scale. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantOneStepFineKernelWeight
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A B : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H)) : ℝ :=
  finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
      (finiteEvenFourTorusDoubleRefinement H)
      β energyIdentity energyNontrivial hβ hEnergy B A *
    finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H B

/-- Coarse-volume raw-kernel coefficient seen from one fine evaluation
configuration. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H) : ℝ :=
  finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H A *
    finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
      H β energyIdentity energyNontrivial hβ hEnergy b
      (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H A)

/-- Fine raw-kernel mass pushed through the actual configuration coarse map
and then aggregated over one coarse residual-gauge orbit. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantOneStepFineOrbitFiberKernelCoefficient
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H) : ℝ :=
  finiteGroupOrbitFiberCoefficient
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (FiniteEvenFourTorusZ2SliceConfiguration H)
    (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H)
    (finiteEvenFourTorusZ2GaugeInvariantOneStepFineKernelWeight
      H β energyIdentity energyNontrivial hβ hEnergy A)
    q

/-- Coarse raw-kernel mass aggregated over one coarse residual-gauge orbit,
with the exact fine-evaluation embedding scale retained. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseOrbitKernelCoefficient
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H) : ℝ :=
  finiteGroupOrbitAggregateCoefficient
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (FiniteEvenFourTorusZ2SliceConfiguration H)
    (finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight
      H β energyIdentity energyNontrivial hβ hEnergy A)
    q

set_option maxHeartbeats 800000 in
/-- At one fixed fine evaluation configuration, the actual raw-kernel equation
against every coarse gauge-invariant observable is equivalent to equality of
fine and coarse kernel mass on every coarse residual-gauge orbit. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneStepKernelEquation_iff_orbitFiberCoefficients
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H)) :
    (∀ f : FiniteEvenFourTorusZ2GaugeInvariantSliceHilbert H,
      (∑ B : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement H),
        finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
            (finiteEvenFourTorusDoubleRefinement H)
            β energyIdentity energyNontrivial hβ hEnergy B A *
          (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H B *
            f.1 (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H B))) =
        finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H A *
          (∑ b : FiniteEvenFourTorusZ2SliceConfiguration H,
            finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
                H β energyIdentity energyNontrivial hβ hEnergy b
                (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H A) * f.1 b)) ↔
      ∀ q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H,
        finiteEvenFourTorusZ2GaugeInvariantOneStepFineOrbitFiberKernelCoefficient
            H β energyIdentity energyNontrivial hβ hEnergy A q =
          finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseOrbitKernelCoefficient
            H β energyIdentity energyNontrivial hβ hEnergy A q := by
  have hGeneric :=
    finiteGroupInvariant_crossSum_eq_iff_orbitFiberSums
      (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
      (FiniteEvenFourTorusZ2SliceConfiguration H)
      (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H)
      (finiteEvenFourTorusZ2GaugeInvariantOneStepFineKernelWeight
        H β energyIdentity energyNontrivial hβ hEnergy A)
      (finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight
        H β energyIdentity energyNontrivial hβ hEnergy A)
  constructor
  · intro h
    have hOrbit := hGeneric.mp (by
      intro f
      simpa only [finiteEvenFourTorusZ2GaugeInvariantOneStepFineKernelWeight,
        finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight,
        Finset.mul_sum, mul_assoc] using h f)
    intro q
    simpa only [finiteEvenFourTorusZ2GaugeInvariantOneStepFineOrbitFiberKernelCoefficient,
      finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseOrbitKernelCoefficient] using hOrbit q
  · intro h
    have hFunctional := hGeneric.mpr (by
      intro q
      simpa only [finiteEvenFourTorusZ2GaugeInvariantOneStepFineOrbitFiberKernelCoefficient,
        finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseOrbitKernelCoefficient] using h q)
    intro f
    simpa only [finiteEvenFourTorusZ2GaugeInvariantOneStepFineKernelWeight,
      finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight,
      Finset.mul_sum, mul_assoc] using hFunctional f

/-- Package-G one-step raw transfer residual vanishes exactly when the actual
fine kernel, after coarse-map and gauge-orbit aggregation with the exact
embedding scale, agrees orbitwise with the coarse kernel. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidual_eq_zero_iff_orbitFiberKernelCoefficients
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      ∀ (A : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement H))
        (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H),
        finiteEvenFourTorusZ2GaugeInvariantOneStepFineOrbitFiberKernelCoefficient
            H β energyIdentity energyNontrivial hβ hEnergy A q =
          finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseOrbitKernelCoefficient
            H β energyIdentity energyNontrivial hβ hEnergy A q := by
  rw [finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidual_eq_zero_iff_kernelEquation]
  constructor
  · intro h A
    exact
      (finiteEvenFourTorusZ2GaugeInvariantOneStepKernelEquation_iff_orbitFiberCoefficients
        H β energyIdentity energyNontrivial hβ hEnergy A).1
        (fun f => h f A)
  · intro h f A
    exact
      (finiteEvenFourTorusZ2GaugeInvariantOneStepKernelEquation_iff_orbitFiberCoefficients
        H β energyIdentity energyNontrivial hβ hEnergy A).2
        (h A) f

/-- The one-step orbit-fibre coefficient can equivalently be computed by first
pushing the fine coefficients to individual coarse configurations and then
aggregating them over the coarse gauge orbit. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneStepFineOrbitFiberKernelCoefficient_eq_aggregate_pushforward
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H) :
    finiteEvenFourTorusZ2GaugeInvariantOneStepFineOrbitFiberKernelCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A q =
      finiteGroupOrbitAggregateCoefficient
        (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
        (FiniteEvenFourTorusZ2SliceConfiguration H)
        (finiteFiberPushforwardCoefficient
          (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H)
          (finiteEvenFourTorusZ2GaugeInvariantOneStepFineKernelWeight
            H β energyIdentity energyNontrivial hβ hEnergy A)) q := by
  symm
  exact finiteGroupOrbitAggregate_fiberPushforward
    (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
    (FiniteEvenFourTorusZ2SliceConfiguration H)
    (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H)
    (finiteEvenFourTorusZ2GaugeInvariantOneStepFineKernelWeight
      H β energyIdentity energyNontrivial hβ hEnergy A) q

/-- Strong one-step projective compatibility at kernel, normalization, and
fixed-sector levels is sufficient for the full Package-F ground-lifted
cross-volume obstruction to vanish.  No one of these hypotheses is asserted
unconditionally. -/
theorem finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction_eq_zero_of_orbitFiberKernel_normalization_fixedSector
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (hKernel :
      ∀ (A : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement H))
        (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H),
        finiteEvenFourTorusZ2GaugeInvariantOneStepFineOrbitFiberKernelCoefficient
            H β energyIdentity energyNontrivial hβ hEnergy A q =
          finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseOrbitKernelCoefficient
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
  have hRaw :
      finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidualLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy = 0 :=
    (finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidual_eq_zero_iff_orbitFiberKernelCoefficients
      H β energyIdentity energyNontrivial hβ hEnergy).2 hKernel
  have hTransfer :
      finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidualLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy = 0 := by
    rw [finiteEvenFourTorusZ2GaugeInvariantOneSlabTransferIntertwiningResidual_raw_normalization_decomposition]
    rw [hRaw, hNormalization]
    simp
  have hGround :
      finiteEvenFourTorusZ2GaugeInvariantGroundProjectorIntertwiningResidualLinearMap
          H β energyIdentity energyNontrivial hβ hEnergy = 0 :=
    (finiteEvenFourTorusZ2GaugeInvariantGroundProjectorIntertwiningResidual_eq_zero_iff_fixedSectorDecomposition
      H β energyIdentity energyNontrivial hβ hEnergy).2 hFixedSector
  apply
    (finiteEvenFourTorusZ2GaugeOrbitGroundLiftedIntertwiningObstruction_eq_zero_iff_transfer_eq_ground
      H β energyIdentity energyNontrivial hβ hEnergy).2
  rw [hTransfer, hGround]

/-- Audit-visible one-step Package-H bundle. -/
structure Z2FiniteEvenFourTorusCrossVolumeOneStepOrbitFiberKernelPackage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) where
  fineOrbitFiberKernelCoefficient :
    FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement H) →
      FiniteEvenFourTorusZ2ResidualGaugeOrbit H → ℝ
  fineOrbitFiberKernelCoefficient_eq : fineOrbitFiberKernelCoefficient =
    finiteEvenFourTorusZ2GaugeInvariantOneStepFineOrbitFiberKernelCoefficient
      H β energyIdentity energyNontrivial hβ hEnergy
  coarseOrbitKernelCoefficient :
    FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement H) →
      FiniteEvenFourTorusZ2ResidualGaugeOrbit H → ℝ
  coarseOrbitKernelCoefficient_eq : coarseOrbitKernelCoefficient =
    finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseOrbitKernelCoefficient
      H β energyIdentity energyNontrivial hβ hEnergy
  rawResidualCriterion :
    finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      ∀ A q, fineOrbitFiberKernelCoefficient A q =
        coarseOrbitKernelCoefficient A q

/-- Construct the one-step Package-H receipt. -/
noncomputable def z2FiniteEvenFourTorusCrossVolumeOneStepOrbitFiberKernelPackage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Z2FiniteEvenFourTorusCrossVolumeOneStepOrbitFiberKernelPackage
      H β energyIdentity energyNontrivial hβ hEnergy where
  fineOrbitFiberKernelCoefficient :=
    finiteEvenFourTorusZ2GaugeInvariantOneStepFineOrbitFiberKernelCoefficient
      H β energyIdentity energyNontrivial hβ hEnergy
  fineOrbitFiberKernelCoefficient_eq := rfl
  coarseOrbitKernelCoefficient :=
    finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseOrbitKernelCoefficient
      H β energyIdentity energyNontrivial hβ hEnergy
  coarseOrbitKernelCoefficient_eq := rfl
  rawResidualCriterion :=
    finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidual_eq_zero_iff_orbitFiberKernelCoefficients
      H β energyIdentity energyNontrivial hβ hEnergy

end

end MathlibAnalytic
end MGAP4D
