import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeBoltzmannOrbitFiberBalance
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeTwoStepTemporalGaugeOrbitFiberReduction
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Direct two-step finest orbit-fibre coefficient written entirely with the
finest temporal-gauge one-slab Wilson action. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantTwoStepBoltzmannFineOrbitFiberCoefficient
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
      Real.exp (-β *
        finiteEvenFourTorusZ2TemporalGaugeOneSlabAction
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H))
          β energyIdentity energyNontrivial B A) *
      finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale H B)
    q

/-- Direct two-step coarsest orbit coefficient written with the coarsest
one-slab Wilson action. -/
noncomputable def finiteEvenFourTorusZ2GaugeInvariantTwoStepBoltzmannCoarseOrbitCoefficient
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
        Real.exp (-β *
          finiteEvenFourTorusZ2TemporalGaugeOneSlabAction
            H β energyIdentity energyNontrivial b
              (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
                (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
                  (finiteEvenFourTorusDoubleRefinement H) A))))
    q

/-- The direct finest temporal-gauge Gram coefficient equals its exact
Boltzmann action coefficient. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepTemporalGaugeFineOrbitFiberKernelCoefficient_eq_boltzmann
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
      finiteEvenFourTorusZ2GaugeInvariantTwoStepBoltzmannFineOrbitFiberCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A q := by
  unfold finiteEvenFourTorusZ2GaugeInvariantTwoStepTemporalGaugeFineOrbitFiberKernelCoefficient
    finiteEvenFourTorusZ2GaugeInvariantTwoStepBoltzmannFineOrbitFiberCoefficient
  apply congrArg (fun w : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)) → ℝ =>
    finiteGroupOrbitFiberCoefficient
      (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
      (FiniteEvenFourTorusZ2SliceConfiguration H)
      (fun B => finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
        (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
          (finiteEvenFourTorusDoubleRefinement H) B)) w q)
  funext B
  rw [finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel_eq_boltzmann]

/-- The direct coarsest temporal-gauge Gram coefficient equals its exact
Boltzmann action coefficient. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepTemporalGaugeCoarseOrbitKernelCoefficient_eq_boltzmann
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepTemporalGaugeCoarseOrbitKernelCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A q =
      finiteEvenFourTorusZ2GaugeInvariantTwoStepBoltzmannCoarseOrbitCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A q := by
  unfold finiteEvenFourTorusZ2GaugeInvariantTwoStepTemporalGaugeCoarseOrbitKernelCoefficient
    finiteEvenFourTorusZ2GaugeInvariantTwoStepBoltzmannCoarseOrbitCoefficient
  apply congrArg (fun w : FiniteEvenFourTorusZ2SliceConfiguration H → ℝ =>
    finiteGroupOrbitAggregateCoefficient
      (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
      (FiniteEvenFourTorusZ2SliceConfiguration H) w q)
  funext b
  rw [finiteEvenFourTorusZ2TemporalGaugeOneSlabGramKernel_eq_boltzmann]

/-- Exact direct two-step Boltzmann action balance. -/
def FiniteEvenFourTorusZ2TwoStepBoltzmannOrbitFiberBalance
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) : Prop :=
  ∀ (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H),
    finiteEvenFourTorusZ2GaugeInvariantTwoStepBoltzmannFineOrbitFiberCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A q =
      finiteEvenFourTorusZ2GaugeInvariantTwoStepBoltzmannCoarseOrbitCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A q

/-- The actual direct two-step raw residual vanishes exactly when the explicit
finest/coarsest Boltzmann action balance holds. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidual_eq_zero_iff_boltzmannOrbitFiberBalance
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      FiniteEvenFourTorusZ2TwoStepBoltzmannOrbitFiberBalance
        H β energyIdentity energyNontrivial hβ hEnergy := by
  rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidual_eq_zero_iff_temporalGaugeOrbitFiberKernelCoefficients]
  unfold FiniteEvenFourTorusZ2TwoStepBoltzmannOrbitFiberBalance
  constructor
  · intro h A q
    calc
      finiteEvenFourTorusZ2GaugeInvariantTwoStepBoltzmannFineOrbitFiberCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q =
        finiteEvenFourTorusZ2GaugeInvariantTwoStepTemporalGaugeFineOrbitFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q :=
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepTemporalGaugeFineOrbitFiberKernelCoefficient_eq_boltzmann
          H β energyIdentity energyNontrivial hβ hEnergy A q).symm
      _ = finiteEvenFourTorusZ2GaugeInvariantTwoStepTemporalGaugeCoarseOrbitKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q := h A q
      _ = finiteEvenFourTorusZ2GaugeInvariantTwoStepBoltzmannCoarseOrbitCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q :=
        finiteEvenFourTorusZ2GaugeInvariantTwoStepTemporalGaugeCoarseOrbitKernelCoefficient_eq_boltzmann
          H β energyIdentity energyNontrivial hβ hEnergy A q
  · intro h A q
    calc
      finiteEvenFourTorusZ2GaugeInvariantTwoStepTemporalGaugeFineOrbitFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q =
        finiteEvenFourTorusZ2GaugeInvariantTwoStepBoltzmannFineOrbitFiberCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q :=
        finiteEvenFourTorusZ2GaugeInvariantTwoStepTemporalGaugeFineOrbitFiberKernelCoefficient_eq_boltzmann
          H β energyIdentity energyNontrivial hβ hEnergy A q
      _ = finiteEvenFourTorusZ2GaugeInvariantTwoStepBoltzmannCoarseOrbitCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q := h A q
      _ = finiteEvenFourTorusZ2GaugeInvariantTwoStepTemporalGaugeCoarseOrbitKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q :=
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepTemporalGaugeCoarseOrbitKernelCoefficient_eq_boltzmann
          H β energyIdentity energyNontrivial hβ hEnergy A q).symm

/-- The direct two-step Boltzmann balance is literally an equality of finite
exponential action sums on every coarsest residual-gauge orbit. -/
theorem finiteEvenFourTorusZ2TwoStepBoltzmannOrbitFiberBalance_iff_explicitSums
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2TwoStepBoltzmannOrbitFiberBalance
        H β energyIdentity energyNontrivial hβ hEnergy ↔
      ∀ (A : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H)))
        (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H),
        (∑ B : FiniteEvenFourTorusZ2SliceConfiguration
            (finiteEvenFourTorusDoubleRefinement
              (finiteEvenFourTorusDoubleRefinement H)),
          if finiteGroupOrbitClass
              (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
              (FiniteEvenFourTorusZ2SliceConfiguration H)
              (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
                (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
                  (finiteEvenFourTorusDoubleRefinement H) B)) = q then
            Real.exp (-β *
              finiteEvenFourTorusZ2TemporalGaugeOneSlabAction
                (finiteEvenFourTorusDoubleRefinement
                  (finiteEvenFourTorusDoubleRefinement H))
                β energyIdentity energyNontrivial B A) *
              finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale H B
          else 0) =
        ∑ b : FiniteEvenFourTorusZ2SliceConfiguration H,
          if finiteGroupOrbitClass
              (FiniteEvenFourTorusZ2ResidualSliceGaugeGroup H)
              (FiniteEvenFourTorusZ2SliceConfiguration H) b = q then
            finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale H A *
              Real.exp (-β *
                finiteEvenFourTorusZ2TemporalGaugeOneSlabAction
                  H β energyIdentity energyNontrivial b
                    (finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
                      (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
                        (finiteEvenFourTorusDoubleRefinement H) A)))
          else 0 := by
  rfl

/-- One explicit direct two-step Boltzmann fibre mismatch certifies a nonzero
actual direct raw residual. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidual_ne_zero_of_boltzmannOrbitFiberMismatch
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H)
    (hMismatch :
      finiteEvenFourTorusZ2GaugeInvariantTwoStepBoltzmannFineOrbitFiberCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q ≠
        finiteEvenFourTorusZ2GaugeInvariantTwoStepBoltzmannCoarseOrbitCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A q) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy ≠ 0 := by
  intro hZero
  have hBalance :=
    (finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidual_eq_zero_iff_boltzmannOrbitFiberBalance
      H β energyIdentity energyNontrivial hβ hEnergy).1 hZero
  exact hMismatch (hBalance A q)

/-- The finest Boltzmann weight obeys the same exact successive configuration
fibre-pushforward cocycle before orbit aggregation. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepBoltzmannFineOrbitFiberCoefficient_eq_successivePushforwardAggregate
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (q : FiniteEvenFourTorusZ2ResidualGaugeOrbit H) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepBoltzmannFineOrbitFiberCoefficient
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
              Real.exp (-β *
                finiteEvenFourTorusZ2TemporalGaugeOneSlabAction
                  (finiteEvenFourTorusDoubleRefinement
                    (finiteEvenFourTorusDoubleRefinement H))
                  β energyIdentity energyNontrivial B A) *
              finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale H B))) q := by
  let weight := fun B : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)) =>
    Real.exp (-β *
      finiteEvenFourTorusZ2TemporalGaugeOneSlabAction
        (finiteEvenFourTorusDoubleRefinement
          (finiteEvenFourTorusDoubleRefinement H))
        β energyIdentity energyNontrivial B A) *
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

end

end MathlibAnalytic
end MGAP4D
