import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPerronPosteriorCanonicalEnvelopeContinuousExtension
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPerronPosteriorEnvelopeContinuationClosure
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The fixed numerical barrier used for the actual high-temperature
continuation. -/
def finiteEvenFourTorusZ2PerronPosteriorHighTemperatureBarrier : ℝ :=
  1 / 2

/-- The local crossing rate, viewed as a real coupling family. -/
def finiteEvenFourTorusZ2PerronPosteriorCrossingRateFamily
    (energyIdentity energyNontrivial : ℝ)
    (parameter : ℝ) : ℝ :=
  z2WilsonTemporalCrossingRate
    parameter energyIdentity energyNontrivial

/-- The corresponding one-coordinate likelihood-ratio family. -/
def finiteEvenFourTorusZ2PerronPosteriorLikelihoodRatioFamily
    (energyIdentity energyNontrivial : ℝ)
    (parameter : ℝ) : ℝ :=
  finiteZ2CrossingLikelihoodRatio
    (finiteEvenFourTorusZ2PerronPosteriorCrossingRateFamily
      energyIdentity energyNontrivial parameter)

/-- The source amplitude in the bidirectional asymptotic response. -/
def finiteEvenFourTorusZ2PerronPosteriorSourceMagnitudeFamily
    (energyIdentity energyNontrivial : ℝ)
    (parameter : ℝ) : ℝ :=
  let ratio :=
    finiteEvenFourTorusZ2PerronPosteriorLikelihoodRatioFamily
      energyIdentity energyNontrivial parameter
  ratio - ratio⁻¹

/-- The target-envelope amplitude in the bidirectional asymptotic response. -/
def finiteEvenFourTorusZ2PerronPosteriorTargetMagnitudeFamily
    (energyIdentity energyNontrivial : ℝ)
    (parameter : ℝ) : ℝ :=
  finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTiltSourceAmplitude
    parameter energyIdentity energyNontrivial

/-- The local shared-plaquette coefficient as a coupling family. -/
def finiteEvenFourTorusZ2PerronPosteriorLocalCoefficientFamily
    (energyIdentity energyNontrivial : ℝ)
    (parameter : ℝ) : ℝ :=
  finiteEvenFourTorusZ2PerronPosteriorLocalCoefficient
    parameter energyIdentity energyNontrivial

/-- The actual asymptotic bootstrap map evaluated at the fixed barrier `1/2`. -/
def finiteEvenFourTorusZ2PerronPosteriorHalfBarrierMap
    (energyIdentity energyNontrivial : ℝ)
    (parameter : ℝ) : ℝ :=
  finiteEvenFourTorusZ2PerronPosteriorAsymptoticBootstrapMap
    parameter energyIdentity energyNontrivial
    finiteEvenFourTorusZ2PerronPosteriorHighTemperatureBarrier

@[simp] theorem finiteEvenFourTorusZ2PerronPosteriorCrossingRateFamily_zero
    (energyIdentity energyNontrivial : ℝ) :
    finiteEvenFourTorusZ2PerronPosteriorCrossingRateFamily
      energyIdentity energyNontrivial 0 = 0 := by
  norm_num [finiteEvenFourTorusZ2PerronPosteriorCrossingRateFamily,
    z2WilsonTemporalCrossingRate,
    z2WilsonTemporalCrossingWeightSum,
    z2WilsonWeightIdentity, z2WilsonWeightNontrivial]

@[simp] theorem finiteEvenFourTorusZ2PerronPosteriorLikelihoodRatioFamily_zero
    (energyIdentity energyNontrivial : ℝ) :
    finiteEvenFourTorusZ2PerronPosteriorLikelihoodRatioFamily
      energyIdentity energyNontrivial 0 = 1 := by
  simp [finiteEvenFourTorusZ2PerronPosteriorLikelihoodRatioFamily,
    finiteZ2CrossingLikelihoodRatio]

@[simp] theorem finiteEvenFourTorusZ2PerronPosteriorSourceMagnitudeFamily_zero
    (energyIdentity energyNontrivial : ℝ) :
    finiteEvenFourTorusZ2PerronPosteriorSourceMagnitudeFamily
      energyIdentity energyNontrivial 0 = 0 := by
  simp [finiteEvenFourTorusZ2PerronPosteriorSourceMagnitudeFamily]

@[simp] theorem finiteEvenFourTorusZ2PerronPosteriorTargetMagnitudeFamily_zero
    (energyIdentity energyNontrivial : ℝ) :
    finiteEvenFourTorusZ2PerronPosteriorTargetMagnitudeFamily
      energyIdentity energyNontrivial 0 = 0 := by
  norm_num [finiteEvenFourTorusZ2PerronPosteriorTargetMagnitudeFamily,
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTiltSourceAmplitude,
    finiteZ2CrossingLikelihoodRatio,
    z2WilsonTemporalCrossingRate,
    z2WilsonTemporalCrossingWeightSum,
    z2WilsonWeightIdentity, z2WilsonWeightNontrivial]

@[simp] theorem finiteEvenFourTorusZ2PerronPosteriorLocalCoefficientFamily_zero
    (energyIdentity energyNontrivial : ℝ) :
    finiteEvenFourTorusZ2PerronPosteriorLocalCoefficientFamily
      energyIdentity energyNontrivial 0 = 0 := by
  norm_num [finiteEvenFourTorusZ2PerronPosteriorLocalCoefficientFamily,
    finiteEvenFourTorusZ2PerronPosteriorLocalCoefficient,
    finitePositiveWeightCrossRatioInfluenceTransform]

/-- The local crossing rate is continuous at zero coupling. -/
theorem continuousAt_finiteEvenFourTorusZ2PerronPosteriorCrossingRateFamily
    (energyIdentity energyNontrivial : ℝ) :
    ContinuousAt
      (finiteEvenFourTorusZ2PerronPosteriorCrossingRateFamily
        energyIdentity energyNontrivial) 0 := by
  unfold finiteEvenFourTorusZ2PerronPosteriorCrossingRateFamily
    z2WilsonTemporalCrossingRate z2WilsonTemporalCrossingWeightSum
    z2WilsonWeightIdentity z2WilsonWeightNontrivial
  fun_prop

/-- The likelihood-ratio family is continuous at zero coupling. -/
theorem continuousAt_finiteEvenFourTorusZ2PerronPosteriorLikelihoodRatioFamily
    (energyIdentity energyNontrivial : ℝ) :
    ContinuousAt
      (finiteEvenFourTorusZ2PerronPosteriorLikelihoodRatioFamily
        energyIdentity energyNontrivial) 0 := by
  let q := finiteEvenFourTorusZ2PerronPosteriorCrossingRateFamily
    energyIdentity energyNontrivial
  have hq : ContinuousAt q 0 :=
    continuousAt_finiteEvenFourTorusZ2PerronPosteriorCrossingRateFamily
      energyIdentity energyNontrivial
  have hden : 1 - q 0 ≠ 0 := by simp [q]
  unfold finiteEvenFourTorusZ2PerronPosteriorLikelihoodRatioFamily
    finiteZ2CrossingLikelihoodRatio
  exact (continuousAt_const.add hq).div
    (continuousAt_const.sub hq) hden

/-- The source amplitude is continuous at zero coupling. -/
theorem continuousAt_finiteEvenFourTorusZ2PerronPosteriorSourceMagnitudeFamily
    (energyIdentity energyNontrivial : ℝ) :
    ContinuousAt
      (finiteEvenFourTorusZ2PerronPosteriorSourceMagnitudeFamily
        energyIdentity energyNontrivial) 0 := by
  let ratio := finiteEvenFourTorusZ2PerronPosteriorLikelihoodRatioFamily
    energyIdentity energyNontrivial
  have hRatio : ContinuousAt ratio 0 :=
    continuousAt_finiteEvenFourTorusZ2PerronPosteriorLikelihoodRatioFamily
      energyIdentity energyNontrivial
  have hRatioNe : ratio 0 ≠ 0 := by simp [ratio]
  unfold finiteEvenFourTorusZ2PerronPosteriorSourceMagnitudeFamily
  exact hRatio.sub (hRatio.inv₀ hRatioNe)

/-- The target-envelope amplitude is continuous at zero coupling. -/
theorem continuousAt_finiteEvenFourTorusZ2PerronPosteriorTargetMagnitudeFamily
    (energyIdentity energyNontrivial : ℝ) :
    ContinuousAt
      (finiteEvenFourTorusZ2PerronPosteriorTargetMagnitudeFamily
        energyIdentity energyNontrivial) 0 := by
  let ratio := finiteEvenFourTorusZ2PerronPosteriorLikelihoodRatioFamily
    energyIdentity energyNontrivial
  have hRatio : ContinuousAt ratio 0 :=
    continuousAt_finiteEvenFourTorusZ2PerronPosteriorLikelihoodRatioFamily
      energyIdentity energyNontrivial
  have hRatioNe : ratio 0 ≠ 0 := by simp [ratio]
  have hInv : ContinuousAt (fun parameter => (ratio parameter)⁻¹) 0 :=
    hRatio.inv₀ hRatioNe
  have hInvNe : (ratio 0)⁻¹ ≠ 0 := by simp [ratio]
  have hQuotient : ContinuousAt (fun parameter =>
      ratio parameter / (ratio parameter)⁻¹) 0 :=
    hRatio.div hInv hInvNe
  have hQuotientNe : ratio 0 / (ratio 0)⁻¹ ≠ 0 := by simp [ratio]
  unfold finiteEvenFourTorusZ2PerronPosteriorTargetMagnitudeFamily
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTiltSourceAmplitude
  exact continuousAt_const.mul
    (continuousAt_const.sub (hQuotient.inv₀ hQuotientNe))

/-- The local shared-plaquette coefficient is continuous at zero coupling. -/
theorem continuousAt_finiteEvenFourTorusZ2PerronPosteriorLocalCoefficientFamily
    (energyIdentity energyNontrivial : ℝ) :
    ContinuousAt
      (finiteEvenFourTorusZ2PerronPosteriorLocalCoefficientFamily
        energyIdentity energyNontrivial) 0 := by
  unfold finiteEvenFourTorusZ2PerronPosteriorLocalCoefficientFamily
    finiteEvenFourTorusZ2PerronPosteriorLocalCoefficient
    finitePositiveWeightCrossRatioInfluenceTransform
  fun_prop

/-- The actual asymptotic map at barrier `1/2` is continuous at zero coupling. -/
theorem continuousAt_finiteEvenFourTorusZ2PerronPosteriorHalfBarrierMap
    (energyIdentity energyNontrivial : ℝ) :
    ContinuousAt
      (finiteEvenFourTorusZ2PerronPosteriorHalfBarrierMap
        energyIdentity energyNontrivial) 0 := by
  let ratio := finiteEvenFourTorusZ2PerronPosteriorLikelihoodRatioFamily
    energyIdentity energyNontrivial
  let source := finiteEvenFourTorusZ2PerronPosteriorSourceMagnitudeFamily
    energyIdentity energyNontrivial
  let target := finiteEvenFourTorusZ2PerronPosteriorTargetMagnitudeFamily
    energyIdentity energyNontrivial
  let local := finiteEvenFourTorusZ2PerronPosteriorLocalCoefficientFamily
    energyIdentity energyNontrivial
  have hRatio : ContinuousAt ratio 0 :=
    continuousAt_finiteEvenFourTorusZ2PerronPosteriorLikelihoodRatioFamily
      energyIdentity energyNontrivial
  have hSource : ContinuousAt source 0 :=
    continuousAt_finiteEvenFourTorusZ2PerronPosteriorSourceMagnitudeFamily
      energyIdentity energyNontrivial
  have hTarget : ContinuousAt target 0 :=
    continuousAt_finiteEvenFourTorusZ2PerronPosteriorTargetMagnitudeFamily
      energyIdentity energyNontrivial
  have hLocal : ContinuousAt local 0 :=
    continuousAt_finiteEvenFourTorusZ2PerronPosteriorLocalCoefficientFamily
      energyIdentity energyNontrivial
  have hResponse : ContinuousAt (fun parameter =>
      target parameter * source parameter *
        (1 - finiteEvenFourTorusZ2PerronPosteriorHighTemperatureBarrier)⁻¹) 0 :=
    (hTarget.mul hSource).mul continuousAt_const
  have hMap : ContinuousAt (fun parameter =>
      2 * local parameter + ratio parameter *
        (target parameter * source parameter *
          (1 - finiteEvenFourTorusZ2PerronPosteriorHighTemperatureBarrier)⁻¹)) 0 :=
    (continuousAt_const.mul hLocal).add (hRatio.mul hResponse)
  simpa [finiteEvenFourTorusZ2PerronPosteriorHalfBarrierMap,
    finiteEvenFourTorusZ2PerronPosteriorAsymptoticBootstrapMap,
    finiteInfluenceKernelBidirectionalAsymptoticResponseCoefficient,
    finiteEvenFourTorusZ2PerronPosteriorHighTemperatureBarrier,
    finiteEvenFourTorusZ2PerronPosteriorLikelihoodRatioFamily,
    finiteEvenFourTorusZ2PerronPosteriorSourceMagnitudeFamily,
    finiteEvenFourTorusZ2PerronPosteriorTargetMagnitudeFamily,
    finiteEvenFourTorusZ2PerronPosteriorLocalCoefficientFamily]
    using hMap

/-- The half-barrier asymptotic map starts exactly at zero. -/
@[simp] theorem finiteEvenFourTorusZ2PerronPosteriorHalfBarrierMap_zero
    (energyIdentity energyNontrivial : ℝ) :
    finiteEvenFourTorusZ2PerronPosteriorHalfBarrierMap
      energyIdentity energyNontrivial 0 = 0 := by
  norm_num [finiteEvenFourTorusZ2PerronPosteriorHalfBarrierMap,
    finiteEvenFourTorusZ2PerronPosteriorAsymptoticBootstrapMap,
    finiteInfluenceKernelBidirectionalAsymptoticResponseCoefficient,
    finiteEvenFourTorusZ2PerronPosteriorHighTemperatureBarrier,
    finiteEvenFourTorusZ2PerronPosteriorLocalCoefficient,
    finitePositiveWeightCrossRatioInfluenceTransform,
    finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTiltSourceAmplitude,
    finiteZ2CrossingLikelihoodRatio,
    z2WilsonTemporalCrossingRate,
    z2WilsonTemporalCrossingWeightSum,
    z2WilsonWeightIdentity, z2WilsonWeightNontrivial]

/-- Continuity at the exactly decoupled seed produces a strictly positive,
volume-independent coupling interval on which the actual asymptotic map sends
`1/2` strictly inside itself. -/
theorem exists_finiteEvenFourTorusZ2PerronPosteriorHalfBarrierCutoff
    (energyIdentity energyNontrivial : ℝ) :
    ∃ couplingCutoff : ℝ,
      0 < couplingCutoff ∧
      ∀ parameter : ℝ,
        0 < parameter → parameter ≤ couplingCutoff →
          finiteEvenFourTorusZ2PerronPosteriorHalfBarrierMap
            energyIdentity energyNontrivial parameter <
              finiteEvenFourTorusZ2PerronPosteriorHighTemperatureBarrier := by
  let F := finiteEvenFourTorusZ2PerronPosteriorHalfBarrierMap
    energyIdentity energyNontrivial
  have hContinuous : ContinuousAt F 0 :=
    continuousAt_finiteEvenFourTorusZ2PerronPosteriorHalfBarrierMap
      energyIdentity energyNontrivial
  rw [Metric.continuousAt_iff] at hContinuous
  obtain ⟨delta, hDelta, hControl⟩ :=
    hContinuous (1 / 2) (by norm_num)
  refine ⟨delta / 2, by positivity, ?_⟩
  intro parameter hParameter hParameterCutoff
  have hDistance : dist parameter 0 < delta := by
    rw [Real.dist_eq]
    simp [abs_of_pos hParameter]
    linarith
  have hImageDistance := hControl hDistance
  have hAbs : |F parameter| < 1 / 2 := by
    simpa [F, Real.dist_eq] using hImageDistance
  have hUpper : F parameter < 1 / 2 :=
    lt_of_le_of_lt (le_abs_self (F parameter)) hAbs
  simpa [F, finiteEvenFourTorusZ2PerronPosteriorHighTemperatureBarrier]
    using hUpper

/-- The exact concrete continuation family exists throughout one common
positive high-temperature interval, with numerical barrier `1/2`. -/
theorem exists_finiteEvenFourTorusZ2PerronPosteriorActualContinuationFamily
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial) :
    ∃ couplingCutoff : ℝ,
      0 < couplingCutoff ∧
      ∀ (β : ℝ) (hβ : 0 < β),
        β ≤ couplingCutoff →
          Z2PerronPosteriorCanonicalEnvelopeContinuationFamilyData
            β energyIdentity energyNontrivial hβ hEnergy := by
  obtain ⟨couplingCutoff, hCutoffPos, hMap⟩ :=
    exists_finiteEvenFourTorusZ2PerronPosteriorHalfBarrierCutoff
      energyIdentity energyNontrivial
  refine ⟨couplingCutoff, hCutoffPos, ?_⟩
  intro β hβ hβCutoff
  refine
    { barrier := finiteEvenFourTorusZ2PerronPosteriorHighTemperatureBarrier
      barrier_nonneg := by
        norm_num [finiteEvenFourTorusZ2PerronPosteriorHighTemperatureBarrier]
      barrier_lt_one := by
        norm_num [finiteEvenFourTorusZ2PerronPosteriorHighTemperatureBarrier]
      atVolume := fun H => ?_ }
  refine
    { rowCoefficient :=
        finiteEvenFourTorusZ2PerronPosteriorEnvelopeRowCoefficientExtension
          H energyIdentity energyNontrivial
      columnCoefficient :=
        finiteEvenFourTorusZ2PerronPosteriorEnvelopeColumnCoefficientExtension
          H energyIdentity energyNontrivial
      rowCoefficient_continuousOn :=
        (continuous_finiteEvenFourTorusZ2PerronPosteriorEnvelopeRowCoefficientExtension
          H energyIdentity energyNontrivial hEnergy.le).continuousOn
      columnCoefficient_continuousOn :=
        (continuous_finiteEvenFourTorusZ2PerronPosteriorEnvelopeColumnCoefficientExtension
          H energyIdentity energyNontrivial hEnergy.le).continuousOn
      rowCoefficient_zero_lt := by
        rw [finiteEvenFourTorusZ2PerronPosteriorEnvelopeRowCoefficientExtension_zero
          H energyIdentity energyNontrivial hEnergy.le]
        norm_num [finiteEvenFourTorusZ2PerronPosteriorHighTemperatureBarrier]
      columnCoefficient_zero_lt := by
        rw [finiteEvenFourTorusZ2PerronPosteriorEnvelopeColumnCoefficientExtension_zero
          H energyIdentity energyNontrivial hEnergy.le]
        norm_num [finiteEvenFourTorusZ2PerronPosteriorHighTemperatureBarrier]
      rowCoefficient_eq_envelope := by
        intro parameter hParameter
        exact
          finiteEvenFourTorusZ2PerronPosteriorEnvelopeRowCoefficientExtension_eq_existing
            H parameter energyIdentity energyNontrivial hParameter.1 hEnergy
      columnCoefficient_eq_envelope := by
        intro parameter hParameter
        exact
          finiteEvenFourTorusZ2PerronPosteriorEnvelopeColumnCoefficientExtension_eq_existing
            H parameter energyIdentity energyNontrivial hParameter.1 hEnergy
      asymptoticBootstrapMap_lt := by
        intro parameter hParameter
        have hParameterCutoff : parameter ≤ couplingCutoff :=
          le_trans hParameter.2 hβCutoff
        simpa [finiteEvenFourTorusZ2PerronPosteriorHalfBarrierMap]
          using hMap parameter hParameter.1 hParameterCutoff }

/-- Unconditional actual strict posterior Dobrushin data at every finite side
and every boundary environment throughout the common high-temperature
interval. -/
theorem exists_finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureDobrushin
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial) :
    ∃ couplingCutoff : ℝ,
      0 < couplingCutoff ∧
      ∀ (β : ℝ) (hβ : 0 < β),
        β ≤ couplingCutoff →
        ∀ (H : ℕ)
          (environment : FiniteEvenFourTorusZ2SliceConfiguration H),
          FinitePositiveWeightDobrushinL1MatrixData
            (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
              H β energyIdentity energyNontrivial hβ.le hEnergy.le
              environment) := by
  obtain ⟨couplingCutoff, hCutoffPos, hFamily⟩ :=
    exists_finiteEvenFourTorusZ2PerronPosteriorActualContinuationFamily
      energyIdentity energyNontrivial hEnergy
  refine ⟨couplingCutoff, hCutoffPos, ?_⟩
  intro β hβ hβCutoff H environment
  exact
    (hFamily β hβ hβCutoff).toDobrushinData H environment

end

end MathlibAnalytic
end MGAP4D
