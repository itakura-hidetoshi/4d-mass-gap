import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeTemporalGaugeOrbitFiberReduction
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeTwoStepOrbitFiberKernelCriterion
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The exact direct two-step embedding scale is constant on finest residual-
gauge orbits. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale_smul
    (H : ℕ)
    (g : FiniteEvenFourTorusZ2ResidualSliceGaugeGroup
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale H (g • A) =
      finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale H A := by
  unfold finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale
  rw [finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale_smul
    (finiteEvenFourTorusDoubleRefinement H) g A]
  rw [finiteEvenFourTorusZ2SliceConfigurationCoarseMap_smul]
  rw [finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale_smul]

/-- Direct finest-to-coarsest orbit-fibre coefficient written with the finest
actual temporal-gauge Gram kernel. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantTwoStepTemporalGaugeFineOrbitFiberKernelCoefficient
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
    (fun B : FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H)) =>
      (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H))
        β energyIdentity energyNontrivial hβ hEnergy).kernel B A *
      finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale H B)
    q

/-- Direct coarsest orbit coefficient written with the coarsest temporal-gauge
Gram kernel. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantTwoStepTemporalGaugeCoarseOrbitKernelCoefficient
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
    (fun b : FiniteEvenFourTorusZ2SliceConfiguration H =>
      finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale H A *
        (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
          H β energyIdentity energyNontrivial hβ hEnergy).kernel b
            (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
              (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
                (finiteEvenFourTorusDoubleRefinement H) A)))
    q

/-- The direct two-step fine Package-H coefficient is exactly its temporal-
gauge Gram-kernel version. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepFineOrbitFiberKernelCoefficient_eq_temporalGauge
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
      finiteEvenFourTorusZ2GaugeInvariantTwoStepTemporalGaugeFineOrbitFiberKernelCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A q := by
  let H₁ := finiteEvenFourTorusDoubleRefinement H
  let H₂ := finiteEvenFourTorusDoubleRefinement H₁
  let Gf := FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H₂
  let Gc := FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H
  let αf := FiniteEvenFourTorusZ2SliceConfiguration H₂
  let αc := FiniteEvenFourTorusZ2SliceConfiguration H
  let C : αf → αc := fun B =>
    finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
      (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H₁ B)
  let φ : Gf → Gc := fun g =>
    finiteEvenFourTorusZ2ResidualSliceGaugeCoarseMap H
      (finiteEvenFourTorusZ2ResidualSliceGaugeCoarseMap H₁ g)
  let K := (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
    H₂ β energyIdentity energyNontrivial hβ hEnergy).kernel
  let scale := finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale H
  have hC : ∀ g : Gf, ∀ B : αf, C (g • B) = φ g • C B := by
    intro g B
    dsimp [C, φ, H₁, H₂]
    rw [finiteEvenFourTorusZ2SliceConfigurationCoarseMap_smul]
    rw [finiteEvenFourTorusZ2SliceConfigurationCoarseMap_smul]
  change
    finiteGroupOrbitFiberCoefficient Gc αc C
        (fun B : αf =>
          finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
              H₂ β energyIdentity energyNontrivial hβ hEnergy B A * scale B) q =
      finiteGroupOrbitFiberCoefficient Gc αc C
        (fun B : αf => K B A * scale B) q
  calc
    finiteGroupOrbitFiberCoefficient Gc αc C
        (fun B : αf =>
          finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel
              H₂ β energyIdentity energyNontrivial hβ hEnergy B A * scale B) q =
      finiteGroupOrbitFiberCoefficient Gc αc C
        (fun B : αf => finiteGroupRightAveragedKernel Gf αf K B A * scale B) q := by
      apply congrArg (fun w : αf → ℝ =>
        finiteGroupOrbitFiberCoefficient Gc αc C w q)
      funext B
      rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_eq_rightAverage]
    _ = finiteGroupOrbitFiberCoefficient Gc αc C
        (fun B : αf => K B A * scale B) q := by
      exact finiteGroupOrbitFiberCoefficient_rightAverage_eq_raw
        Gf Gc αf αc φ C hC K
        (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel_smul
          H₂ β energyIdentity energyNontrivial hβ hEnergy)
        scale
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale_smul H)
        A q

/-- The direct two-step coarse Package-H coefficient is also exactly its
coarsest temporal-gauge version. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseOrbitKernelCoefficient_eq_temporalGauge
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseOrbitKernelCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A q =
      finiteEvenFourTorusZ2GaugeInvariantTwoStepTemporalGaugeCoarseOrbitKernelCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A q := by
  let G := FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H
  let α := FiniteEvenFourTorusZ2SliceConfiguration H
  let K := (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
    H β energyIdentity energyNontrivial hβ hEnergy).kernel
  let c := finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale H A
  let Ac := finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
    (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
      (finiteEvenFourTorusDoubleRefinement H) A)
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

/-- Direct two-step raw transfer compatibility is therefore equivalent to a
pure temporal-gauge Gram-kernel orbit-fibre identity. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidual_eq_zero_iff_temporalGaugeOrbitFiberKernelCoefficients
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
        finiteEvenFourTorusZ2GaugeInvariantTwoStepTemporalGaugeFineOrbitFiberKernelCoefficient
            H β energyIdentity energyNontrivial hβ hEnergy A q =
          finiteEvenFourTorusZ2GaugeInvariantTwoStepTemporalGaugeCoarseOrbitKernelCoefficient
            H β energyIdentity energyNontrivial hβ hEnergy A q := by
  rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidual_eq_zero_iff_orbitFiberKernelCoefficients]
  constructor
  · intro h A q
    calc
      finiteEvenFourTorusZ2GaugeInvariantTwoStepTemporalGaugeFineOrbitFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q =
        finiteEvenFourTorusZ2GaugeInvariantTwoStepFineOrbitFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q :=
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepFineOrbitFiberKernelCoefficient_eq_temporalGauge
          H β energyIdentity energyNontrivial hβ hEnergy A q).symm
      _ = finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseOrbitKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q := h A q
      _ = finiteEvenFourTorusZ2GaugeInvariantTwoStepTemporalGaugeCoarseOrbitKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q :=
        finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseOrbitKernelCoefficient_eq_temporalGauge
          H β energyIdentity energyNontrivial hβ hEnergy A q
  · intro h A q
    calc
      finiteEvenFourTorusZ2GaugeInvariantTwoStepFineOrbitFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q =
        finiteEvenFourTorusZ2GaugeInvariantTwoStepTemporalGaugeFineOrbitFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q :=
        finiteEvenFourTorusZ2GaugeInvariantTwoStepFineOrbitFiberKernelCoefficient_eq_temporalGauge
          H β energyIdentity energyNontrivial hβ hEnergy A q
      _ = finiteEvenFourTorusZ2GaugeInvariantTwoStepTemporalGaugeCoarseOrbitKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q := h A q
      _ = finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseOrbitKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q :=
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseOrbitKernelCoefficient_eq_temporalGauge
          H β energyIdentity energyNontrivial hβ hEnergy A q).symm

/-- A direct temporal-gauge two-step orbit-fibre mismatch certifies a nonzero
actual direct two-step raw residual. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidual_ne_zero_of_temporalGaugeOrbitFiberKernelMismatch
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H)
    (hMismatch :
      finiteEvenFourTorusZ2GaugeInvariantTwoStepTemporalGaugeFineOrbitFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q ≠
        finiteEvenFourTorusZ2GaugeInvariantTwoStepTemporalGaugeCoarseOrbitKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy ≠ 0 := by
  intro hZero
  have hAll :=
    (finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidual_eq_zero_iff_temporalGaugeOrbitFiberKernelCoefficients
      H β energyIdentity energyNontrivial hβ hEnergy).1 hZero
  exact hMismatch (hAll A q)

/-- The temporal-gauge finest coefficient still obeys the exact configuration
fibre-pushforward cocycle before final orbit aggregation. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepTemporalGaugeFineOrbitFiberKernelCoefficient_eq_successivePushforwardAggregate
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepTemporalGaugeFineOrbitFiberKernelCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A q =
      finiteGroupOrbitAggregateCoefficient
        (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
        (FiniteEvenFourTorusZ2SliceConfiguration H)
        (finiteFiberPushforwardCoefficient
          (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H)
          (finiteFiberPushforwardCoefficient
            (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
              (finiteEvenFourTorusDoubleRefinement H))
            (fun B : FiniteEvenFourTorusZ2SliceConfiguration
                (finiteEvenFourTorusDoubleRefinement
                  (finiteEvenFourTorusDoubleRefinement H)) =>
              (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
                (finiteEvenFourTorusDoubleRefinement
                  (finiteEvenFourTorusDoubleRefinement H))
                β energyIdentity energyNontrivial hβ hEnergy).kernel B A *
              finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale H B))) q := by
  let weight := fun B : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)) =>
    (finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H))
      β energyIdentity energyNontrivial hβ hEnergy).kernel B A *
    finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale H B
  let directMap := fun B : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)) =>
    finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
      (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
        (finiteEvenFourTorusDoubleRefinement H) B)
  change
    finiteGroupOrbitFiberCoefficient
        (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
        (FiniteEvenFourTorusZ2SliceConfiguration H)
        directMap weight q = _
  calc
    finiteGroupOrbitFiberCoefficient
        (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
        (FiniteEvenFourTorusZ2SliceConfiguration H)
        directMap weight q =
      finiteGroupOrbitAggregateCoefficient
        (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
        (FiniteEvenFourTorusZ2SliceConfiguration H)
        (finiteFiberPushforwardCoefficient directMap weight) q := by
          symm
          exact finiteGroupOrbitAggregate_fiberPushforward
            (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
            (FiniteEvenFourTorusZ2SliceConfiguration H)
            directMap weight q
    _ = finiteGroupOrbitAggregateCoefficient
        (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
        (FiniteEvenFourTorusZ2SliceConfiguration H)
        (finiteFiberPushforwardCoefficient
          (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H)
          (finiteFiberPushforwardCoefficient
            (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
              (finiteEvenFourTorusDoubleRefinement H)) weight)) q := by
          apply congrArg (fun a : FiniteEvenFourTorusZ2SliceConfiguration H → ℝ =>
            finiteGroupOrbitAggregateCoefficient
              (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
              (FiniteEvenFourTorusZ2SliceConfiguration H) a q)
          funext b
          symm
          exact finiteFiberPushforwardCoefficient_comp
            (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H)
            (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
              (finiteEvenFourTorusDoubleRefinement H)) weight b

/-- Audit-visible direct two-step Package-I reduction receipt. -/
structure Z2FiniteEvenFourTorusCrossVolumeTwoStepTemporalGaugeOrbitFiberReductionPackage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) where
  fineTemporalCoefficient :
    FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H)) →
      FiniteEvenFourTorusZ2ResidualGaugeOrbit H → ℝ
  fineTemporalCoefficient_eq : fineTemporalCoefficient =
    finiteEvenFourTorusZ2GaugeInvariantTwoStepTemporalGaugeFineOrbitFiberKernelCoefficient
      H β energyIdentity energyNontrivial hβ hEnergy
  coarseTemporalCoefficient :
    FiniteEvenFourTorusZ2SliceConfiguration
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H)) →
      FiniteEvenFourTorusZ2ResidualGaugeOrbit H → ℝ
  coarseTemporalCoefficient_eq : coarseTemporalCoefficient =
    finiteEvenFourTorusZ2GaugeInvariantTwoStepTemporalGaugeCoarseOrbitKernelCoefficient
      H β energyIdentity energyNontrivial hβ hEnergy
  rawResidualCriterion :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      ∀ A q, fineTemporalCoefficient A q = coarseTemporalCoefficient A q

/-- Construct the direct two-step Package-I receipt. -/
noncomputable def z2FiniteEvenFourTorusCrossVolumeTwoStepTemporalGaugeOrbitFiberReductionPackage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Z2FiniteEvenFourTorusCrossVolumeTwoStepTemporalGaugeOrbitFiberReductionPackage
      H β energyIdentity energyNontrivial hβ hEnergy where
  fineTemporalCoefficient :=
    finiteEvenFourTorusZ2GaugeInvariantTwoStepTemporalGaugeFineOrbitFiberKernelCoefficient
      H β energyIdentity energyNontrivial hβ hEnergy
  fineTemporalCoefficient_eq := rfl
  coarseTemporalCoefficient :=
    finiteEvenFourTorusZ2GaugeInvariantTwoStepTemporalGaugeCoarseOrbitKernelCoefficient
      H β energyIdentity energyNontrivial hβ hEnergy
  coarseTemporalCoefficient_eq := rfl
  rawResidualCriterion :=
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidual_eq_zero_iff_temporalGaugeOrbitFiberKernelCoefficients
      H β energyIdentity energyNontrivial hβ hEnergy

end

end MathlibAnalytic
end MGAP4D
