import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeTemporalGaugeOrbitFiberReduction
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- One-step fine orbit-fibre coefficient written directly as an exponential
of the actual fine temporal-gauge one-slab Wilson action. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantOneStepBoltzmannFineOrbitFiberCoefficient
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
      Real.exp (-β *
        finiteEvenFourTorusZ2TemporalGaugeOneSlabAction
          (finiteEvenFourTorusDoubleRefinement H)
          β energyIdentity energyNontrivial B A) *
      finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H B)
    q

/-- One-step coarse orbit coefficient written directly as an exponential of
the actual coarse temporal-gauge one-slab Wilson action. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantOneStepBoltzmannCoarseOrbitCoefficient
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
        Real.exp (-β *
          finiteEvenFourTorusZ2TemporalGaugeOneSlabAction
            H β energyIdentity energyNontrivial b
              (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H A)))
    q

/-- The one-step fine temporal-gauge Gram coefficient is definitionally the
same finite orbit-fibre sum after replacing the Gram kernel by its exact
Boltzmann action formula. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneStepTemporalGaugeFineOrbitFiberKernelCoefficient_eq_boltzmann
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H) :
    finiteEvenFourTorusZ2GaugeInvariantOneStepTemporalGaugeFineOrbitFiberKernelCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A q =
      finiteEvenFourTorusZ2GaugeInvariantOneStepBoltzmannFineOrbitFiberCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A q := by
  unfold finiteEvenFourTorusZ2GaugeInvariantOneStepTemporalGaugeFineOrbitFiberKernelCoefficient
    finiteEvenFourTorusZ2GaugeInvariantOneStepBoltzmannFineOrbitFiberCoefficient
  apply congrArg (fun w : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H) → ℝ =>
    finiteGroupOrbitFiberCoefficient
      (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
      (FiniteEvenFourTorusZ2SliceConfiguration H)
      (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H) w q)
  funext B
  rw [finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel_eq_boltzmann]

/-- The one-step coarse temporal-gauge coefficient is the corresponding
coarse Boltzmann action orbit sum. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneStepTemporalGaugeCoarseOrbitKernelCoefficient_eq_boltzmann
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H) :
    finiteEvenFourTorusZ2GaugeInvariantOneStepTemporalGaugeCoarseOrbitKernelCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A q =
      finiteEvenFourTorusZ2GaugeInvariantOneStepBoltzmannCoarseOrbitCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A q := by
  unfold finiteEvenFourTorusZ2GaugeInvariantOneStepTemporalGaugeCoarseOrbitKernelCoefficient
    finiteEvenFourTorusZ2GaugeInvariantOneStepBoltzmannCoarseOrbitCoefficient
  apply congrArg (fun w : FiniteEvenFourTorusZ2SliceConfiguration H → ℝ =>
    finiteGroupOrbitAggregateCoefficient
      (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
      (FiniteEvenFourTorusZ2SliceConfiguration H) w q)
  funext b
  rw [finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel_eq_boltzmann]

/-- Exact finite Boltzmann action balance required by one-step raw projective
compatibility. -/
def FiniteEvenFourTorusZ2OneStepBoltzmannOrbitFiberBalance
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) : Prop :=
  ∀ (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H),
    finiteEvenFourTorusZ2GaugeInvariantOneStepBoltzmannFineOrbitFiberCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A q =
      finiteEvenFourTorusZ2GaugeInvariantOneStepBoltzmannCoarseOrbitCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A q

/-- The actual one-step raw transfer residual vanishes exactly when the
explicit Boltzmann action orbit-fibre balance holds. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidual_eq_zero_iff_boltzmannOrbitFiberBalance
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      FiniteEvenFourTorusZ2OneStepBoltzmannOrbitFiberBalance
        H β energyIdentity energyNontrivial hβ hEnergy := by
  rw [finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidual_eq_zero_iff_temporalGaugeOrbitFiberKernelCoefficients]
  unfold FiniteEvenFourTorusZ2OneStepBoltzmannOrbitFiberBalance
  constructor
  · intro h A q
    calc
      finiteEvenFourTorusZ2GaugeInvariantOneStepBoltzmannFineOrbitFiberCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q =
        finiteEvenFourTorusZ2GaugeInvariantOneStepTemporalGaugeFineOrbitFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q :=
        (finiteEvenFourTorusZ2GaugeInvariantOneStepTemporalGaugeFineOrbitFiberKernelCoefficient_eq_boltzmann
          H β energyIdentity energyNontrivial hβ hEnergy A q).symm
      _ = finiteEvenFourTorusZ2GaugeInvariantOneStepTemporalGaugeCoarseOrbitKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q := h A q
      _ = finiteEvenFourTorusZ2GaugeInvariantOneStepBoltzmannCoarseOrbitCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q :=
        finiteEvenFourTorusZ2GaugeInvariantOneStepTemporalGaugeCoarseOrbitKernelCoefficient_eq_boltzmann
          H β energyIdentity energyNontrivial hβ hEnergy A q
  · intro h A q
    calc
      finiteEvenFourTorusZ2GaugeInvariantOneStepTemporalGaugeFineOrbitFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q =
        finiteEvenFourTorusZ2GaugeInvariantOneStepBoltzmannFineOrbitFiberCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q :=
        finiteEvenFourTorusZ2GaugeInvariantOneStepTemporalGaugeFineOrbitFiberKernelCoefficient_eq_boltzmann
          H β energyIdentity energyNontrivial hβ hEnergy A q
      _ = finiteEvenFourTorusZ2GaugeInvariantOneStepBoltzmannCoarseOrbitCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q := h A q
      _ = finiteEvenFourTorusZ2GaugeInvariantOneStepTemporalGaugeCoarseOrbitKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q :=
        (finiteEvenFourTorusZ2GaugeInvariantOneStepTemporalGaugeCoarseOrbitKernelCoefficient_eq_boltzmann
          H β energyIdentity energyNontrivial hβ hEnergy A q).symm

/-- The one-step Boltzmann balance is literally equality of two finite sums,
with the left sum restricted by the coarse orbit of the fine configuration and
the right sum restricted by the coarse residual-gauge orbit. -/
theorem finiteEvenFourTorusZ2OneStepBoltzmannOrbitFiberBalance_iff_explicitSums
    (H : ℕ) (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β) (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2OneStepBoltzmannOrbitFiberBalance
        H β energyIdentity energyNontrivial hβ hEnergy ↔
    ∀ (A : FiniteEvenFourTorusZ2SliceConfiguration (finiteEvenFourTorusDoubleRefinement H))
      (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H),
      (∑ B : FiniteEvenFourTorusZ2SliceConfiguration (finiteEvenFourTorusDoubleRefinement H),
        if finiteGroupOrbitClass (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
            (FiniteEvenFourTorusZ2SliceConfiguration H)
            (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H B) = q then
          Real.exp (-β * finiteEvenFourTorusZ2TemporalGaugeOneSlabAction
            (finiteEvenFourTorusDoubleRefinement H) β energyIdentity energyNontrivial B A) *
            finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H B
        else 0) =
      ∑ b : FiniteEvenFourTorusZ2SliceConfiguration H,
        if finiteGroupOrbitClass (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
            (FiniteEvenFourTorusZ2SliceConfiguration H) b = q then
          finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H A *
            Real.exp (-β * finiteEvenFourTorusZ2TemporalGaugeOneSlabAction
              H β energyIdentity energyNontrivial b
                (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H A))
        else 0 := by
  rfl

/-- One explicit failure of the finite Boltzmann fibre sum certifies a nonzero
actual one-step raw transfer residual. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidual_ne_zero_of_boltzmannOrbitFiberMismatch
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H)
    (hMismatch :
      finiteEvenFourTorusZ2GaugeInvariantOneStepBoltzmannFineOrbitFiberCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q ≠
        finiteEvenFourTorusZ2GaugeInvariantOneStepBoltzmannCoarseOrbitCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q) :
    finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy ≠ 0 := by
  intro hZero
  have hBalance :=
    (finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidual_eq_zero_iff_boltzmannOrbitFiberBalance
      H β energyIdentity energyNontrivial hβ hEnergy).1 hZero
  exact hMismatch (hBalance A q)

end

end MathlibAnalytic
end MGAP4D
