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

/-- The canonical cross-ratio influence transform is continuous on the whole
real line. -/
theorem continuous_finitePositiveWeightCrossRatioInfluenceTransform :
    Continuous finitePositiveWeightCrossRatioInfluenceTransform := by
  unfold finitePositiveWeightCrossRatioInfluenceTransform
  exact continuous_const.mul
    ((Real.continuous_exp.sub continuous_const).div
      (Real.continuous_exp.add continuous_const)
      (fun radius => by positivity))

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
    finiteEvenFourTorusZ2PerronPosteriorLocalInfluenceMajorant,
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
  have hNumerator :
      Continuous (fun parameter : ℝ =>
        Real.exp (-parameter * energyIdentity) -
          Real.exp (-parameter * energyNontrivial)) := by
    fun_prop
  have hDenominator :
      Continuous (fun parameter : ℝ =>
        Real.exp (-parameter * energyIdentity) +
          Real.exp (-parameter * energyNontrivial)) := by
    fun_prop
  exact
    (hNumerator.div hDenominator
      (fun parameter => by positivity)).continuousAt

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
    finiteEvenFourTorusZ2PerronPosteriorLocalInfluenceMajorant
  have hRadius :
      Continuous (fun parameter : ℝ =>
        12 * parameter * (energyNontrivial - energyIdentity)) := by
    fun_prop
  exact
    (continuous_const.mul
      (continuous_finitePositiveWeightCrossRatioInfluenceTransform.comp
        hRadius)).continuousAt

/-- The actual asymptotic map at barrier `1/2` is continuous at zero coupling. -/
theorem continuousAt_finiteEvenFourTorusZ2PerronPosteriorHalfBarrierMap
    (energyIdentity energyNontrivial : ℝ) :
    ContinuousAt
      (finiteEvenFourTorusZ2PerronPosteriorHalfBarrierMap
        energyIdentity energyNontrivial) 0 := by
  let ratioFamily :=
    finiteEvenFourTorusZ2PerronPosteriorLikelihoodRatioFamily
      energyIdentity energyNontrivial
  let sourceFamily :=
    finiteEvenFourTorusZ2PerronPosteriorSourceMagnitudeFamily
      energyIdentity energyNontrivial
  let targetFamily :=
    finiteEvenFourTorusZ2PerronPosteriorTargetMagnitudeFamily
      energyIdentity energyNontrivial
  let localFamily :=
    finiteEvenFourTorusZ2PerronPosteriorLocalCoefficientFamily
      energyIdentity energyNontrivial
  have hRatio : ContinuousAt ratioFamily 0 :=
    continuousAt_finiteEvenFourTorusZ2PerronPosteriorLikelihoodRatioFamily
      energyIdentity energyNontrivial
  have hSource : ContinuousAt sourceFamily 0 :=
    continuousAt_finiteEvenFourTorusZ2PerronPosteriorSourceMagnitudeFamily
      energyIdentity energyNontrivial
  have hTarget : ContinuousAt targetFamily 0 :=
    continuousAt_finiteEvenFourTorusZ2PerronPosteriorTargetMagnitudeFamily
      energyIdentity energyNontrivial
  have hLocal : ContinuousAt localFamily 0 :=
    continuousAt_finiteEvenFourTorusZ2PerronPosteriorLocalCoefficientFamily
      energyIdentity energyNontrivial
  have hResponse : ContinuousAt (fun parameter =>
      targetFamily parameter * sourceFamily parameter *
        (1 - finiteEvenFourTorusZ2PerronPosteriorHighTemperatureBarrier)⁻¹) 0 :=
    (hTarget.mul hSource).mul continuousAt_const
  have hMap : ContinuousAt (fun parameter =>
      2 * localFamily parameter + ratioFamily parameter *
        (targetFamily parameter * sourceFamily parameter *
          (1 - finiteEvenFourTorusZ2PerronPosteriorHighTemperatureBarrier)⁻¹)) 0 :=
    (continuousAt_const.mul hLocal).add (hRatio.mul hResponse)
  change ContinuousAt (fun parameter =>
    2 * localFamily parameter + ratioFamily parameter *
      (targetFamily parameter * sourceFamily parameter *
        (1 - finiteEvenFourTorusZ2PerronPosteriorHighTemperatureBarrier)⁻¹)) 0
  exact hMap

/-- The half-barrier asymptotic map starts exactly at zero. -/
@[simp] theorem finiteEvenFourTorusZ2PerronPosteriorHalfBarrierMap_zero
    (energyIdentity energyNontrivial : ℝ) :
    finiteEvenFourTorusZ2PerronPosteriorHalfBarrierMap
      energyIdentity energyNontrivial 0 = 0 := by
  change
    2 * finiteEvenFourTorusZ2PerronPosteriorLocalCoefficientFamily
          energyIdentity energyNontrivial 0 +
      finiteEvenFourTorusZ2PerronPosteriorLikelihoodRatioFamily
          energyIdentity energyNontrivial 0 *
        finiteInfluenceKernelBidirectionalAsymptoticResponseCoefficient
          finiteEvenFourTorusZ2PerronPosteriorHighTemperatureBarrier
          (finiteEvenFourTorusZ2PerronPosteriorTargetMagnitudeFamily
            energyIdentity energyNontrivial 0)
          (finiteEvenFourTorusZ2PerronPosteriorSourceMagnitudeFamily
            energyIdentity energyNontrivial 0) = 0
  simp [finiteInfluenceKernelBidirectionalAsymptoticResponseCoefficient]

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

/-- Canonical common cutoff selected from zero-coupling continuity. -/
noncomputable def finiteEvenFourTorusZ2PerronPosteriorHalfBarrierCutoff
    (energyIdentity energyNontrivial : ℝ) : ℝ :=
  Classical.choose
    (exists_finiteEvenFourTorusZ2PerronPosteriorHalfBarrierCutoff
      energyIdentity energyNontrivial)

/-- The selected common cutoff is strictly positive. -/
theorem finiteEvenFourTorusZ2PerronPosteriorHalfBarrierCutoff_pos
    (energyIdentity energyNontrivial : ℝ) :
    0 < finiteEvenFourTorusZ2PerronPosteriorHalfBarrierCutoff
      energyIdentity energyNontrivial :=
  (Classical.choose_spec
    (exists_finiteEvenFourTorusZ2PerronPosteriorHalfBarrierCutoff
      energyIdentity energyNontrivial)).1

/-- The selected cutoff realizes the strict half-barrier inequality. -/
theorem finiteEvenFourTorusZ2PerronPosteriorHalfBarrierCutoff_map_lt
    (energyIdentity energyNontrivial : ℝ)
    (parameter : ℝ)
    (hParameter : 0 < parameter)
    (hParameterCutoff :
      parameter ≤ finiteEvenFourTorusZ2PerronPosteriorHalfBarrierCutoff
        energyIdentity energyNontrivial) :
    finiteEvenFourTorusZ2PerronPosteriorHalfBarrierMap
        energyIdentity energyNontrivial parameter <
      finiteEvenFourTorusZ2PerronPosteriorHighTemperatureBarrier :=
  (Classical.choose_spec
    (exists_finiteEvenFourTorusZ2PerronPosteriorHalfBarrierCutoff
      energyIdentity energyNontrivial)).2
    parameter hParameter hParameterCutoff

/-- Concrete Type-valued package for the common actual high-temperature
continuation interval. -/
structure Z2PerronPosteriorActualHighTemperatureContinuationData
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial) where
  couplingCutoff : ℝ
  couplingCutoff_pos : 0 < couplingCutoff
  halfBarrierMap_lt :
    ∀ parameter : ℝ,
      0 < parameter → parameter ≤ couplingCutoff →
        finiteEvenFourTorusZ2PerronPosteriorHalfBarrierMap
          energyIdentity energyNontrivial parameter <
            finiteEvenFourTorusZ2PerronPosteriorHighTemperatureBarrier
  continuationFamily :
    ∀ (β : ℝ) (hβ : 0 < β),
      β ≤ couplingCutoff →
        Z2PerronPosteriorCanonicalEnvelopeContinuationFamilyData
          β energyIdentity energyNontrivial hβ hEnergy

/-- Canonical actual continuation data obtained from the decoupled seed and
the fixed numerical barrier `1/2`. -/
noncomputable def finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial) :
    Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy := by
  refine
    { couplingCutoff :=
        finiteEvenFourTorusZ2PerronPosteriorHalfBarrierCutoff
          energyIdentity energyNontrivial
      couplingCutoff_pos :=
        finiteEvenFourTorusZ2PerronPosteriorHalfBarrierCutoff_pos
          energyIdentity energyNontrivial
      halfBarrierMap_lt :=
        finiteEvenFourTorusZ2PerronPosteriorHalfBarrierCutoff_map_lt
          energyIdentity energyNontrivial
      continuationFamily := ?_ }
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
        have hParameterCutoff :
            parameter ≤
              finiteEvenFourTorusZ2PerronPosteriorHalfBarrierCutoff
                energyIdentity energyNontrivial :=
          le_trans hParameter.2 hβCutoff
        simpa [finiteEvenFourTorusZ2PerronPosteriorHalfBarrierMap]
          using
            finiteEvenFourTorusZ2PerronPosteriorHalfBarrierCutoff_map_lt
              energyIdentity energyNontrivial parameter
              hParameter.1 hParameterCutoff }

namespace Z2PerronPosteriorActualHighTemperatureContinuationData

/-- Actual strict posterior Dobrushin data at every coupling below the common
cutoff, every finite side, and every boundary environment. -/
noncomputable def toDobrushinData
    {energyIdentity energyNontrivial : ℝ}
    {hEnergy : energyIdentity < energyNontrivial}
    (C : Z2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff : β ≤ C.couplingCutoff)
    (H : ℕ)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H) :
    FinitePositiveWeightDobrushinL1MatrixData
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
        H β energyIdentity energyNontrivial hβ.le hEnergy.le environment) :=
  (C.continuationFamily β hβ hβCutoff).toDobrushinData H environment

end Z2PerronPosteriorActualHighTemperatureContinuationData

/-- The canonical common high-temperature cutoff is strictly positive. -/
theorem finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureCouplingCutoff_pos
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial) :
    0 <
      (finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
        energyIdentity energyNontrivial hEnergy).couplingCutoff :=
  (finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
    energyIdentity energyNontrivial hEnergy).couplingCutoff_pos

/-- Canonical unconditional actual strict posterior Dobrushin data throughout
the constructed common high-temperature interval. -/
noncomputable def finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureDobrushinData
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤
        (finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
          energyIdentity energyNontrivial hEnergy).couplingCutoff)
    (H : ℕ)
    (environment : FiniteEvenFourTorusZ2SliceConfiguration H) :
    FinitePositiveWeightDobrushinL1MatrixData
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedPosteriorWeight
        H β energyIdentity energyNontrivial hβ.le hEnergy.le environment) :=
  (finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy).toDobrushinData
    β hβ hβCutoff H environment

end

end MathlibAnalytic
end MGAP4D
