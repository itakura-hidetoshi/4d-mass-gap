import MGAP4D.MathlibAnalytic.FiniteGroupOrbitFiberRightAverageCancellation
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeOneStepOrbitFiberKernelCriterion
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusResidualGaugeOneSlabKernelInvariance
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The exact pointwise normalization scale of the canonical one-step invariant
embedding is constant on fine residual-gauge orbits. -/
theorem finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale_smul
    (H : ℕ)
    (g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup
      (finiteEvenFourTorusDoubleRefinement H))
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H)) :
    finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H (g • A) =
      finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H A := by
  simp only [finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale,
    finiteEvenFourTorusZ2FineGaugeOrbitOfConfiguration,
    finiteEvenFourTorusZ2CoarseGaugeOrbitOfFineConfiguration,
    finiteEvenFourTorusZ2SliceConfigurationCoarseMap_smul,
    finiteGroupOrbitClass_smul]

/-- Fine one-step orbit-fibre coefficient written directly with the actual
temporal-gauge Gram kernel rather than the unfixed temporal-link average. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantOneStepTemporalGaugeFineOrbitFiberKernelCoefficient
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
    (fun B : FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement H) =>
      (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
        (finiteEvenFourTorusDoubleRefinement H)
        β energyIdentity energyNontrivial hβ hEnergy).kernel B A *
      finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H B)
    q

/-- Coarse one-step orbit coefficient written directly with the temporal-gauge
Gram kernel. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantOneStepTemporalGaugeCoarseOrbitKernelCoefficient
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
    (fun b : FiniteEvenFourTorusZ2SliceConfiguration H =>
      finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H A *
        (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
          H β energyIdentity energyNontrivial hβ hEnergy).kernel b
            (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H A))
    q

/-- The fine Package-H coefficient is unchanged when the unfixed-gauge kernel
is replaced by the underlying temporal-gauge Gram kernel.  The residual-gauge
right average cancels exactly on each coarse orbit fibre. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneStepFineOrbitFiberKernelCoefficient_eq_temporalGauge
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H) :
    finiteEvenFourTorusZ2GaugeInvariantOneStepFineOrbitFiberKernelCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A q =
      finiteEvenFourTorusZ2GaugeInvariantOneStepTemporalGaugeFineOrbitFiberKernelCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A q := by
  let Gf := FiniteEvenFourTorusZ2ResidualSliceGaugeGroup
    (finiteEvenFourTorusDoubleRefinement H)
  let Gc := FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H
  let αf := FiniteEvenFourTorusZ2SliceConfiguration
    (finiteEvenFourTorusDoubleRefinement H)
  let αc := FiniteEvenFourTorusZ2SliceConfiguration H
  let K := (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
    (finiteEvenFourTorusDoubleRefinement H)
    β energyIdentity energyNontrivial hβ hEnergy).kernel
  let scale := finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H
  change
    finiteGroupOrbitFiberCoefficient Gc αc
        (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H)
        (fun B : αf =>
          finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
              (finiteEvenFourTorusDoubleRefinement H)
              β energyIdentity energyNontrivial hβ hEnergy B A * scale B) q =
      finiteGroupOrbitFiberCoefficient Gc αc
        (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H)
        (fun B : αf => K B A * scale B) q
  calc
    finiteGroupOrbitFiberCoefficient Gc αc
        (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H)
        (fun B : αf =>
          finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
              (finiteEvenFourTorusDoubleRefinement H)
              β energyIdentity energyNontrivial hβ hEnergy B A * scale B) q =
      finiteGroupOrbitFiberCoefficient Gc αc
        (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H)
        (fun B : αf =>
          finiteGroupRightAveragedKernel Gf αf K B A * scale B) q := by
      apply congrArg (fun w : αf → ℝ =>
        finiteGroupOrbitFiberCoefficient Gc αc
          (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H) w q)
      funext B
      rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_eq_rightAverage]
    _ = finiteGroupOrbitFiberCoefficient Gc αc
        (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H)
        (fun B : αf => K B A * scale B) q := by
      exact finiteGroupOrbitFiberCoefficient_rightAverage_eq_raw
        Gf Gc αf αc
        (finiteEvenFourTorusZ2ResidualSliceGaugeCoarseMap H)
        (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H)
        (finiteEvenFourTorusZ2SliceConfigurationCoarseMap_smul H)
        K
        (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel_smul
          (finiteEvenFourTorusDoubleRefinement H)
          β energyIdentity energyNontrivial hβ hEnergy)
        scale
        (finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale_smul H)
        A q

/-- The coarse Package-H coefficient likewise loses its residual-gauge right
average after coarse-orbit aggregation. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseOrbitKernelCoefficient_eq_temporalGauge
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H) :
    finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseOrbitKernelCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A q =
      finiteEvenFourTorusZ2GaugeInvariantOneStepTemporalGaugeCoarseOrbitKernelCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A q := by
  let G := FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H
  let α := FiniteEvenFourTorusZ2SliceConfiguration H
  let K := (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
    H β energyIdentity energyNontrivial hβ hEnergy).kernel
  let c := finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H A
  let Ac := finiteEvenFourTorusZ2SliceConfigurationCoarseMap H A
  change
    finiteGroupOrbitAggregateCoefficient G α
        (fun b : α => c *
          finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
            H β energyIdentity energyNontrivial hβ hEnergy b Ac) q =
      finiteGroupOrbitAggregateCoefficient G α
        (fun b : α => c * K b Ac) q
  calc
    finiteGroupOrbitAggregateCoefficient G α
        (fun b : α => c *
          finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
            H β energyIdentity energyNontrivial hβ hEnergy b Ac) q =
      finiteGroupOrbitAggregateCoefficient G α
        (fun b : α => c * finiteGroupRightAveragedKernel G α K b Ac) q := by
      apply congrArg (fun w : α → ℝ =>
        finiteGroupOrbitAggregateCoefficient G α w q)
      funext b
      rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_eq_rightAverage]
    _ = finiteGroupOrbitAggregateCoefficient G α
        (fun b : α => c * K b Ac) q := by
      exact finiteGroupOrbitAggregateCoefficient_rightAverage_mul_constant_eq_raw
        G α K
        (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel_smul
          H β energyIdentity energyNontrivial hβ hEnergy)
        c Ac q

/-- The actual one-step raw transfer residual therefore vanishes exactly when
the temporal-gauge Gram kernel satisfies the corresponding orbit-fibre coarse
identity. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidual_eq_zero_iff_temporalGaugeOrbitFiberKernelCoefficients
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      ∀ (A : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement H))
        (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H),
        finiteEvenFourTorusZ2GaugeInvariantOneStepTemporalGaugeFineOrbitFiberKernelCoefficient
            H β energyIdentity energyNontrivial hβ hEnergy A q =
          finiteEvenFourTorusZ2GaugeInvariantOneStepTemporalGaugeCoarseOrbitKernelCoefficient
            H β energyIdentity energyNontrivial hβ hEnergy A q := by
  rw [finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidual_eq_zero_iff_orbitFiberKernelCoefficients]
  constructor
  · intro h A q
    calc
      finiteEvenFourTorusZ2GaugeInvariantOneStepTemporalGaugeFineOrbitFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q =
        finiteEvenFourTorusZ2GaugeInvariantOneStepFineOrbitFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q :=
        (finiteEvenFourTorusZ2GaugeInvariantOneStepFineOrbitFiberKernelCoefficient_eq_temporalGauge
          H β energyIdentity energyNontrivial hβ hEnergy A q).symm
      _ = finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseOrbitKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q := h A q
      _ = finiteEvenFourTorusZ2GaugeInvariantOneStepTemporalGaugeCoarseOrbitKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q :=
        finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseOrbitKernelCoefficient_eq_temporalGauge
          H β energyIdentity energyNontrivial hβ hEnergy A q
  · intro h A q
    calc
      finiteEvenFourTorusZ2GaugeInvariantOneStepFineOrbitFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q =
        finiteEvenFourTorusZ2GaugeInvariantOneStepTemporalGaugeFineOrbitFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q :=
        finiteEvenFourTorusZ2GaugeInvariantOneStepFineOrbitFiberKernelCoefficient_eq_temporalGauge
          H β energyIdentity energyNontrivial hβ hEnergy A q
      _ = finiteEvenFourTorusZ2GaugeInvariantOneStepTemporalGaugeCoarseOrbitKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q := h A q
      _ = finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseOrbitKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q :=
        (finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseOrbitKernelCoefficient_eq_temporalGauge
          H β energyIdentity energyNontrivial hβ hEnergy A q).symm

/-- A single temporal-gauge orbit-fibre mismatch is already an explicit
certificate that the actual unfixed-gauge one-step raw residual is nonzero. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidual_ne_zero_of_temporalGaugeOrbitFiberKernelMismatch
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H)
    (hMismatch :
      finiteEvenFourTorusZ2GaugeInvariantOneStepTemporalGaugeFineOrbitFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q ≠
        finiteEvenFourTorusZ2GaugeInvariantOneStepTemporalGaugeCoarseOrbitKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q) :
    finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy ≠ 0 := by
  intro hZero
  have hAll :=
    (finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidual_eq_zero_iff_temporalGaugeOrbitFiberKernelCoefficients
      H β energyIdentity energyNontrivial hβ hEnergy).1 hZero
  exact hMismatch (hAll A q)

/-- Audit-visible one-step Package-I reduction receipt. -/
structure Z2FiniteEvenFourTorusCrossVolumeOneStepTemporalGaugeOrbitFiberReductionPackage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) where
  fineTemporalCoefficient :
    FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement H) →
      FiniteEvenFourTorusZ2ResidualGaugeOrbit H → ℝ
  fineTemporalCoefficient_eq : fineTemporalCoefficient =
    finiteEvenFourTorusZ2GaugeInvariantOneStepTemporalGaugeFineOrbitFiberKernelCoefficient
      H β energyIdentity energyNontrivial hβ hEnergy
  coarseTemporalCoefficient :
    FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement H) →
      FiniteEvenFourTorusZ2ResidualGaugeOrbit H → ℝ
  coarseTemporalCoefficient_eq : coarseTemporalCoefficient =
    finiteEvenFourTorusZ2GaugeInvariantOneStepTemporalGaugeCoarseOrbitKernelCoefficient
      H β energyIdentity energyNontrivial hβ hEnergy
  rawResidualCriterion :
    finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      ∀ A q, fineTemporalCoefficient A q = coarseTemporalCoefficient A q

/-- Construct the one-step Package-I receipt. -/
noncomputable def z2FiniteEvenFourTorusCrossVolumeOneStepTemporalGaugeOrbitFiberReductionPackage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Z2FiniteEvenFourTorusCrossVolumeOneStepTemporalGaugeOrbitFiberReductionPackage
      H β energyIdentity energyNontrivial hβ hEnergy where
  fineTemporalCoefficient :=
    finiteEvenFourTorusZ2GaugeInvariantOneStepTemporalGaugeFineOrbitFiberKernelCoefficient
      H β energyIdentity energyNontrivial hβ hEnergy
  fineTemporalCoefficient_eq := rfl
  coarseTemporalCoefficient :=
    finiteEvenFourTorusZ2GaugeInvariantOneStepTemporalGaugeCoarseOrbitKernelCoefficient
      H β energyIdentity energyNontrivial hβ hEnergy
  coarseTemporalCoefficient_eq := rfl
  rawResidualCriterion :=
    finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidual_eq_zero_iff_temporalGaugeOrbitFiberKernelCoefficients
      H β energyIdentity energyNontrivial hβ hEnergy

end

end MathlibAnalytic
end MGAP4D
