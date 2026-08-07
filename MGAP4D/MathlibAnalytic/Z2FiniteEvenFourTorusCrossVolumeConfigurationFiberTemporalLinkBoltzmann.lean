import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeTwoStepConfigurationFiberKernelEvaluation
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusCrossVolumeTwoStepBoltzmannOrbitFiberBalance
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The one-step fine configuration-fibre coefficient is the literal temporal-
link Boltzmann sum over fine configurations in one coarse-map fibre.  The
right-boundary gauge average is kept as an explicit finite temporal-link sum,
so no separate invariance of the temporal-gauge kernel is assumed. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficient_eq_temporalLinkBoltzmannSum
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A b =
      ∑ B : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement H),
        if finiteEvenFourTorusZ2SliceConfigurationCoarseMap H B = b then
          ((Fintype.card
              (FiniteEvenFourTorusZ2TemporalLinkField
                (finiteEvenFourTorusDoubleRefinement H)) : ℝ)⁻¹ *
            ∑ U : FiniteEvenFourTorusZ2TemporalLinkField
                (finiteEvenFourTorusDoubleRefinement H),
              Real.exp (-β *
                finiteEvenFourTorusZ2TemporalGaugeOneSlabAction
                  (finiteEvenFourTorusDoubleRefinement H)
                  β energyIdentity energyNontrivial B (U • A))) *
            finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H B
        else 0 := by
  classical
  unfold finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficient
    finiteFiberPushforwardCoefficient
    finiteEvenFourTorusZ2GaugeInvariantOneStepFineKernelWeight
  apply Finset.sum_congr rfl
  intro B _hB
  by_cases hCb : finiteEvenFourTorusZ2SliceConfigurationCoarseMap H B = b
  · simp only [hCb, if_pos]
    rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_apply]
    simp_rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabAction_eq_temporalGauge_smul]
  · simp [hCb]

/-- The one-step coarse comparison coefficient has the corresponding explicit
coarse temporal-link Boltzmann form. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight_eq_temporalLinkBoltzmannSum
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement H))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight
        H β energyIdentity energyNontrivial hβ hEnergy A b =
      finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H A *
        ((Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) : ℝ)⁻¹ *
          ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
            Real.exp (-β *
              finiteEvenFourTorusZ2TemporalGaugeOneSlabAction
                H β energyIdentity energyNontrivial b
                  (U • finiteEvenFourTorusZ2SliceConfigurationCoarseMap H A))) := by
  unfold finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight
  rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_apply]
  simp_rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabAction_eq_temporalGauge_smul]

/-- Exact one-step configuration-fibre balance after fully exposing the finite
sum over temporal-link fields.  This is a condition, not an unconditional
identity of the model. -/
def FiniteEvenFourTorusZ2OneStepTemporalLinkConfigurationFiberBalance
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
        ((Fintype.card
            (FiniteEvenFourTorusZ2TemporalLinkField
              (finiteEvenFourTorusDoubleRefinement H)) : ℝ)⁻¹ *
          ∑ U : FiniteEvenFourTorusZ2TemporalLinkField
              (finiteEvenFourTorusDoubleRefinement H),
            Real.exp (-β *
              finiteEvenFourTorusZ2TemporalGaugeOneSlabAction
                (finiteEvenFourTorusDoubleRefinement H)
                β energyIdentity energyNontrivial B (U • A))) *
          finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H B
      else 0) =
    finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H A *
      ((Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) : ℝ)⁻¹ *
        ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
          Real.exp (-β *
            finiteEvenFourTorusZ2TemporalGaugeOneSlabAction
              H β energyIdentity energyNontrivial b
                (U • finiteEvenFourTorusZ2SliceConfigurationCoarseMap H A)))

/-- The actual one-step raw transfer residual vanishes exactly when the explicit
configuration-fibre / temporal-link Boltzmann balance holds. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidual_eq_zero_iff_temporalLinkConfigurationFiberBalance
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      FiniteEvenFourTorusZ2OneStepTemporalLinkConfigurationFiberBalance
        H β energyIdentity energyNontrivial hβ hEnergy := by
  rw [finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidual_eq_zero_iff_configurationFiberKernelCoefficients]
  unfold FiniteEvenFourTorusZ2OneStepTemporalLinkConfigurationFiberBalance
  constructor
  · intro h A b
    calc
      (∑ B : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement H),
        if finiteEvenFourTorusZ2SliceConfigurationCoarseMap H B = b then
          ((Fintype.card
              (FiniteEvenFourTorusZ2TemporalLinkField
                (finiteEvenFourTorusDoubleRefinement H)) : ℝ)⁻¹ *
            ∑ U : FiniteEvenFourTorusZ2TemporalLinkField
                (finiteEvenFourTorusDoubleRefinement H),
              Real.exp (-β *
                finiteEvenFourTorusZ2TemporalGaugeOneSlabAction
                  (finiteEvenFourTorusDoubleRefinement H)
                  β energyIdentity energyNontrivial B (U • A))) *
            finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H B
        else 0) =
          finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficient
            H β energyIdentity energyNontrivial hβ hEnergy A b :=
        (finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficient_eq_temporalLinkBoltzmannSum
          H β energyIdentity energyNontrivial hβ hEnergy A b).symm
      _ = finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight
          H β energyIdentity energyNontrivial hβ hEnergy A b := h A b
      _ = finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H A *
          ((Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) : ℝ)⁻¹ *
            ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
              Real.exp (-β *
                finiteEvenFourTorusZ2TemporalGaugeOneSlabAction
                  H β energyIdentity energyNontrivial b
                    (U • finiteEvenFourTorusZ2SliceConfigurationCoarseMap H A))) :=
        finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight_eq_temporalLinkBoltzmannSum
          H β energyIdentity energyNontrivial hβ hEnergy A b
  · intro h A b
    calc
      finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A b =
        (∑ B : FiniteEvenFourTorusZ2SliceConfiguration
            (finiteEvenFourTorusDoubleRefinement H),
          if finiteEvenFourTorusZ2SliceConfigurationCoarseMap H B = b then
            ((Fintype.card
                (FiniteEvenFourTorusZ2TemporalLinkField
                  (finiteEvenFourTorusDoubleRefinement H)) : ℝ)⁻¹ *
              ∑ U : FiniteEvenFourTorusZ2TemporalLinkField
                  (finiteEvenFourTorusDoubleRefinement H),
                Real.exp (-β *
                  finiteEvenFourTorusZ2TemporalGaugeOneSlabAction
                    (finiteEvenFourTorusDoubleRefinement H)
                    β energyIdentity energyNontrivial B (U • A))) *
              finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H B
          else 0) :=
        finiteEvenFourTorusZ2GaugeInvariantOneStepFineConfigurationFiberKernelCoefficient_eq_temporalLinkBoltzmannSum
          H β energyIdentity energyNontrivial hβ hEnergy A b
      _ = finiteEvenFourTorusZ2GaugeInvariantCoarseEmbeddingPointwiseScale H A *
          ((Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) : ℝ)⁻¹ *
            ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
              Real.exp (-β *
                finiteEvenFourTorusZ2TemporalGaugeOneSlabAction
                  H β energyIdentity energyNontrivial b
                    (U • finiteEvenFourTorusZ2SliceConfigurationCoarseMap H A))) := h A b
      _ = finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight
          H β energyIdentity energyNontrivial hβ hEnergy A b :=
        (finiteEvenFourTorusZ2GaugeInvariantOneStepCoarseKernelWeight_eq_temporalLinkBoltzmannSum
          H β energyIdentity energyNontrivial hβ hEnergy A b).symm

/-- The configuration-fibre temporal-link condition and Package J's orbit-
fibre temporal-gauge Boltzmann condition are exactly equivalent because both
characterize the same actual raw transfer residual. -/
theorem finiteEvenFourTorusZ2OneStepTemporalLinkConfigurationFiberBalance_iff_boltzmannOrbitFiberBalance
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2OneStepTemporalLinkConfigurationFiberBalance
        H β energyIdentity energyNontrivial hβ hEnergy ↔
      FiniteEvenFourTorusZ2OneStepBoltzmannOrbitFiberBalance
        H β energyIdentity energyNontrivial hβ hEnergy := by
  constructor
  · intro h
    have hRaw :=
      (finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidual_eq_zero_iff_temporalLinkConfigurationFiberBalance
        H β energyIdentity energyNontrivial hβ hEnergy).2 h
    exact
      (finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidual_eq_zero_iff_boltzmannOrbitFiberBalance
        H β energyIdentity energyNontrivial hβ hEnergy).1 hRaw
  · intro h
    have hRaw :=
      (finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidual_eq_zero_iff_boltzmannOrbitFiberBalance
        H β energyIdentity energyNontrivial hβ hEnergy).2 h
    exact
      (finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidual_eq_zero_iff_temporalLinkConfigurationFiberBalance
        H β energyIdentity energyNontrivial hβ hEnergy).1 hRaw

/-- The direct two-step finest configuration-fibre coefficient is the literal
finest temporal-link Boltzmann sum over the composed coarse-map fibre. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient_eq_temporalLinkBoltzmannSum
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy A b =
      ∑ B : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H)),
        if finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
            (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
              (finiteEvenFourTorusDoubleRefinement H) B) = b then
          ((Fintype.card
              (FiniteEvenFourTorusZ2TemporalLinkField
                (finiteEvenFourTorusDoubleRefinement
                  (finiteEvenFourTorusDoubleRefinement H))) : ℝ)⁻¹ *
            ∑ U : FiniteEvenFourTorusZ2TemporalLinkField
                (finiteEvenFourTorusDoubleRefinement
                  (finiteEvenFourTorusDoubleRefinement H)),
              Real.exp (-β *
                finiteEvenFourTorusZ2TemporalGaugeOneSlabAction
                  (finiteEvenFourTorusDoubleRefinement
                    (finiteEvenFourTorusDoubleRefinement H))
                  β energyIdentity energyNontrivial B (U • A))) *
            finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale H B
        else 0 := by
  classical
  rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient_eq_direct]
  unfold finiteFiberPushforwardCoefficient
    finiteEvenFourTorusZ2GaugeInvariantTwoStepFineKernelWeight
  apply Finset.sum_congr rfl
  intro B _hB
  by_cases hCb :
      finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
        (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
          (finiteEvenFourTorusDoubleRefinement H) B) = b
  · simp only [hCb, if_pos]
    rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_apply]
    simp_rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabAction_eq_temporalGauge_smul]
  · simp [hCb]

/-- The direct two-step coarsest comparison coefficient has the corresponding
explicit coarsest temporal-link Boltzmann form. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight_eq_temporalLinkBoltzmannSum
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (A : FiniteEvenFourTorusZ2SliceConfiguration
      (finiteEvenFourTorusDoubleRefinement
        (finiteEvenFourTorusDoubleRefinement H)))
    (b : FiniteEvenFourTorusZ2SliceConfiguration H) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight
        H β energyIdentity energyNontrivial hβ hEnergy A b =
      finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale H A *
        ((Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) : ℝ)⁻¹ *
          ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
            Real.exp (-β *
              finiteEvenFourTorusZ2TemporalGaugeOneSlabAction
                H β energyIdentity energyNontrivial b
                  (U • finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
                    (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
                      (finiteEvenFourTorusDoubleRefinement H) A)))) := by
  unfold finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight
  rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabKernel_apply]
  simp_rw [finiteEvenFourTorusZ2UnfixedGaugeOneSlabAction_eq_temporalGauge_smul]

/-- Exact direct two-step configuration-fibre balance with the temporal-link
averages exposed as finite Boltzmann sums. -/
def FiniteEvenFourTorusZ2TwoStepTemporalLinkConfigurationFiberBalance
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
        ((Fintype.card
            (FiniteEvenFourTorusZ2TemporalLinkField
              (finiteEvenFourTorusDoubleRefinement
                (finiteEvenFourTorusDoubleRefinement H))) : ℝ)⁻¹ *
          ∑ U : FiniteEvenFourTorusZ2TemporalLinkField
              (finiteEvenFourTorusDoubleRefinement
                (finiteEvenFourTorusDoubleRefinement H)),
            Real.exp (-β *
              finiteEvenFourTorusZ2TemporalGaugeOneSlabAction
                (finiteEvenFourTorusDoubleRefinement
                  (finiteEvenFourTorusDoubleRefinement H))
                β energyIdentity energyNontrivial B (U • A))) *
          finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale H B
      else 0) =
    finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale H A *
      ((Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) : ℝ)⁻¹ *
        ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
          Real.exp (-β *
            finiteEvenFourTorusZ2TemporalGaugeOneSlabAction
              H β energyIdentity energyNontrivial b
                (U • finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
                  (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
                    (finiteEvenFourTorusDoubleRefinement H) A))))

/-- The actual direct two-step raw residual vanishes exactly when the explicit
finest/coarsest temporal-link Boltzmann configuration-fibre balance holds. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidual_eq_zero_iff_temporalLinkConfigurationFiberBalance
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      FiniteEvenFourTorusZ2TwoStepTemporalLinkConfigurationFiberBalance
        H β energyIdentity energyNontrivial hβ hEnergy := by
  rw [finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidual_eq_zero_iff_configurationFiberKernelCoefficients]
  unfold FiniteEvenFourTorusZ2TwoStepTemporalLinkConfigurationFiberBalance
  constructor
  · intro h A b
    calc
      (∑ B : FiniteEvenFourTorusZ2SliceConfiguration
          (finiteEvenFourTorusDoubleRefinement
            (finiteEvenFourTorusDoubleRefinement H)),
        if finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
            (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
              (finiteEvenFourTorusDoubleRefinement H) B) = b then
          ((Fintype.card
              (FiniteEvenFourTorusZ2TemporalLinkField
                (finiteEvenFourTorusDoubleRefinement
                  (finiteEvenFourTorusDoubleRefinement H))) : ℝ)⁻¹ *
            ∑ U : FiniteEvenFourTorusZ2TemporalLinkField
                (finiteEvenFourTorusDoubleRefinement
                  (finiteEvenFourTorusDoubleRefinement H)),
              Real.exp (-β *
                finiteEvenFourTorusZ2TemporalGaugeOneSlabAction
                  (finiteEvenFourTorusDoubleRefinement
                    (finiteEvenFourTorusDoubleRefinement H))
                  β energyIdentity energyNontrivial B (U • A))) *
            finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale H B
        else 0) =
          finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient
            H β energyIdentity energyNontrivial hβ hEnergy A b :=
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient_eq_temporalLinkBoltzmannSum
          H β energyIdentity energyNontrivial hβ hEnergy A b).symm
      _ = finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight
          H β energyIdentity energyNontrivial hβ hEnergy A b := h A b
      _ = finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale H A *
          ((Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) : ℝ)⁻¹ *
            ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
              Real.exp (-β *
                finiteEvenFourTorusZ2TemporalGaugeOneSlabAction
                  H β energyIdentity energyNontrivial b
                    (U • finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
                      (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
                        (finiteEvenFourTorusDoubleRefinement H) A)))) :=
        finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight_eq_temporalLinkBoltzmannSum
          H β energyIdentity energyNontrivial hβ hEnergy A b
  · intro h A b
    calc
      finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy A b =
        (∑ B : FiniteEvenFourTorusZ2SliceConfiguration
            (finiteEvenFourTorusDoubleRefinement
              (finiteEvenFourTorusDoubleRefinement H)),
          if finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
              (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
                (finiteEvenFourTorusDoubleRefinement H) B) = b then
            ((Fintype.card
                (FiniteEvenFourTorusZ2TemporalLinkField
                  (finiteEvenFourTorusDoubleRefinement
                    (finiteEvenFourTorusDoubleRefinement H))) : ℝ)⁻¹ *
              ∑ U : FiniteEvenFourTorusZ2TemporalLinkField
                  (finiteEvenFourTorusDoubleRefinement
                    (finiteEvenFourTorusDoubleRefinement H)),
                Real.exp (-β *
                  finiteEvenFourTorusZ2TemporalGaugeOneSlabAction
                    (finiteEvenFourTorusDoubleRefinement
                      (finiteEvenFourTorusDoubleRefinement H))
                    β energyIdentity energyNontrivial B (U • A))) *
              finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale H B
          else 0) :=
        finiteEvenFourTorusZ2GaugeInvariantTwoStepFineConfigurationFiberKernelCoefficient_eq_temporalLinkBoltzmannSum
          H β energyIdentity energyNontrivial hβ hEnergy A b
      _ = finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseEmbeddingPointwiseScale H A *
          ((Fintype.card (FiniteEvenFourTorusZ2TemporalLinkField H) : ℝ)⁻¹ *
            ∑ U : FiniteEvenFourTorusZ2TemporalLinkField H,
              Real.exp (-β *
                finiteEvenFourTorusZ2TemporalGaugeOneSlabAction
                  H β energyIdentity energyNontrivial b
                    (U • finiteEvenFourTorusZ2SliceConfigurationCoarseMap H
                      (finiteEvenFourTorusZ2SliceConfigurationCoarseMap
                        (finiteEvenFourTorusDoubleRefinement H) A)))) := h A b
      _ = finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight
          H β energyIdentity energyNontrivial hβ hEnergy A b :=
        (finiteEvenFourTorusZ2GaugeInvariantTwoStepCoarseKernelWeight_eq_temporalLinkBoltzmannSum
          H β energyIdentity energyNontrivial hβ hEnergy A b).symm

/-- The direct configuration-fibre temporal-link balance and Package J's direct
orbit-fibre Boltzmann balance are exact equivalent presentations of the same
raw cross-volume obstruction. -/
theorem finiteEvenFourTorusZ2TwoStepTemporalLinkConfigurationFiberBalance_iff_boltzmannOrbitFiberBalance
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    FiniteEvenFourTorusZ2TwoStepTemporalLinkConfigurationFiberBalance
        H β energyIdentity energyNontrivial hβ hEnergy ↔
      FiniteEvenFourTorusZ2TwoStepBoltzmannOrbitFiberBalance
        H β energyIdentity energyNontrivial hβ hEnergy := by
  constructor
  · intro h
    have hRaw :=
      (finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidual_eq_zero_iff_temporalLinkConfigurationFiberBalance
        H β energyIdentity energyNontrivial hβ hEnergy).2 h
    exact
      (finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidual_eq_zero_iff_boltzmannOrbitFiberBalance
        H β energyIdentity energyNontrivial hβ hEnergy).1 hRaw
  · intro h
    have hRaw :=
      (finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidual_eq_zero_iff_boltzmannOrbitFiberBalance
        H β energyIdentity energyNontrivial hβ hEnergy).2 h
    exact
      (finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidual_eq_zero_iff_temporalLinkConfigurationFiberBalance
        H β energyIdentity energyNontrivial hβ hEnergy).1 hRaw

/-- A failed one-step temporal-link configuration-fibre balance certifies a
nonzero actual one-step raw transfer residual. -/
theorem finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidual_ne_zero_of_temporalLinkConfigurationFiberMismatch
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (hMismatch :
      ¬ FiniteEvenFourTorusZ2OneStepTemporalLinkConfigurationFiberBalance
        H β energyIdentity energyNontrivial hβ hEnergy) :
    finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy ≠ 0 := by
  intro hZero
  exact hMismatch
    ((finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidual_eq_zero_iff_temporalLinkConfigurationFiberBalance
      H β energyIdentity energyNontrivial hβ hEnergy).1 hZero)

/-- A failed direct two-step temporal-link configuration-fibre balance certifies
that the actual direct raw residual is nonzero. -/
theorem finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidual_ne_zero_of_temporalLinkConfigurationFiberMismatch
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial)
    (hMismatch :
      ¬ FiniteEvenFourTorusZ2TwoStepTemporalLinkConfigurationFiberBalance
        H β energyIdentity energyNontrivial hβ hEnergy) :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy ≠ 0 := by
  intro hZero
  exact hMismatch
    ((finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidual_eq_zero_iff_temporalLinkConfigurationFiberBalance
      H β energyIdentity energyNontrivial hβ hEnergy).1 hZero)

/-- Audit-visible Package-K bundle: configuration-fibre reduction, explicit
finite temporal-link Boltzmann formulae, and equivalence with Package J's
orbit-fibre Boltzmann presentation. -/
structure Z2FiniteEvenFourTorusCrossVolumeConfigurationFiberTemporalLinkBoltzmannPackage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) where
  oneStepRawCriterion :
    finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      FiniteEvenFourTorusZ2OneStepTemporalLinkConfigurationFiberBalance
        H β energyIdentity energyNontrivial hβ hEnergy
  oneStepOrbitBridge :
    FiniteEvenFourTorusZ2OneStepTemporalLinkConfigurationFiberBalance
        H β energyIdentity energyNontrivial hβ hEnergy ↔
      FiniteEvenFourTorusZ2OneStepBoltzmannOrbitFiberBalance
        H β energyIdentity energyNontrivial hβ hEnergy
  twoStepRawCriterion :
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidualLinearMap
        H β energyIdentity energyNontrivial hβ hEnergy = 0 ↔
      FiniteEvenFourTorusZ2TwoStepTemporalLinkConfigurationFiberBalance
        H β energyIdentity energyNontrivial hβ hEnergy
  twoStepOrbitBridge :
    FiniteEvenFourTorusZ2TwoStepTemporalLinkConfigurationFiberBalance
        H β energyIdentity energyNontrivial hβ hEnergy ↔
      FiniteEvenFourTorusZ2TwoStepBoltzmannOrbitFiberBalance
        H β energyIdentity energyNontrivial hβ hEnergy

/-- Construct the complete Package-K receipt. -/
noncomputable def z2FiniteEvenFourTorusCrossVolumeConfigurationFiberTemporalLinkBoltzmannPackage
    (H : ℕ)
    (β energyIdentity energyNontrivial : ℝ)
    (hβ : 0 ≤ β)
    (hEnergy : energyIdentity ≤ energyNontrivial) :
    Z2FiniteEvenFourTorusCrossVolumeConfigurationFiberTemporalLinkBoltzmannPackage
      H β energyIdentity energyNontrivial hβ hEnergy where
  oneStepRawCriterion :=
    finiteEvenFourTorusZ2GaugeInvariantOneSlabRawTransferIntertwiningResidual_eq_zero_iff_temporalLinkConfigurationFiberBalance
      H β energyIdentity energyNontrivial hβ hEnergy
  oneStepOrbitBridge :=
    finiteEvenFourTorusZ2OneStepTemporalLinkConfigurationFiberBalance_iff_boltzmannOrbitFiberBalance
      H β energyIdentity energyNontrivial hβ hEnergy
  twoStepRawCriterion :=
    finiteEvenFourTorusZ2GaugeInvariantTwoStepOneSlabRawTransferIntertwiningResidual_eq_zero_iff_temporalLinkConfigurationFiberBalance
      H β energyIdentity energyNontrivial hβ hEnergy
  twoStepOrbitBridge :=
    finiteEvenFourTorusZ2TwoStepTemporalLinkConfigurationFiberBalance_iff_boltzmannOrbitFiberBalance
      H β energyIdentity energyNontrivial hβ hEnergy

end

end MathlibAnalytic
end MGAP4D
