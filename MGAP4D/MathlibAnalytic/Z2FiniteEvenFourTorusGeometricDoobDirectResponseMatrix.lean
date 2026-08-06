import MGAP4D.MathlibAnalytic.FiniteInfluenceKernelObservableResponseMatrixColumnBound
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPerronPosteriorActualHighTemperatureContinuation
import MGAP4D.MathlibAnalytic.Z2FiniteEvenFourTorusPerronPosteriorBidirectionalKernelResponse
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Continuity of the unit target-response amplitude at the decoupled seed
produces a positive common interval on which that amplitude is below `1/4`. -/
theorem exists_finiteEvenFourTorusZ2GeometricDoobTargetMagnitudeQuarterCutoff
    (energyIdentity energyNontrivial : ℝ) :
    ∃ cutoff : ℝ,
      0 < cutoff ∧
      ∀ parameter : ℝ,
        0 < parameter → parameter ≤ cutoff →
          finiteEvenFourTorusZ2PerronPosteriorTargetMagnitudeFamily
              energyIdentity energyNontrivial parameter < 1 / 4 := by
  let F :=
    finiteEvenFourTorusZ2PerronPosteriorTargetMagnitudeFamily
      energyIdentity energyNontrivial
  have hContinuous : ContinuousAt F 0 :=
    continuousAt_finiteEvenFourTorusZ2PerronPosteriorTargetMagnitudeFamily
      energyIdentity energyNontrivial
  rw [Metric.continuousAt_iff] at hContinuous
  obtain ⟨delta, hDelta, hControl⟩ :=
    hContinuous (1 / 4) (by norm_num)
  refine ⟨delta / 2, by positivity, ?_⟩
  intro parameter hParameter hParameterCutoff
  have hDistance : dist parameter 0 < delta := by
    rw [Real.dist_eq]
    simp [abs_of_pos hParameter]
    linarith
  have hImageDistance := hControl hDistance
  have hAbs : |F parameter| < 1 / 4 := by
    simpa [F, Real.dist_eq] using hImageDistance
  exact lt_of_le_of_lt (le_abs_self (F parameter)) hAbs

/-- Canonical target-amplitude cutoff selected from zero-coupling
continuity. -/
noncomputable def finiteEvenFourTorusZ2GeometricDoobTargetMagnitudeQuarterCutoff
    (energyIdentity energyNontrivial : ℝ) : ℝ :=
  Classical.choose
    (exists_finiteEvenFourTorusZ2GeometricDoobTargetMagnitudeQuarterCutoff
      energyIdentity energyNontrivial)

/-- The canonical target-amplitude cutoff is strictly positive. -/
theorem finiteEvenFourTorusZ2GeometricDoobTargetMagnitudeQuarterCutoff_pos
    (energyIdentity energyNontrivial : ℝ) :
    0 < finiteEvenFourTorusZ2GeometricDoobTargetMagnitudeQuarterCutoff
      energyIdentity energyNontrivial :=
  (Classical.choose_spec
    (exists_finiteEvenFourTorusZ2GeometricDoobTargetMagnitudeQuarterCutoff
      energyIdentity energyNontrivial)).1

/-- The selected cutoff realizes the strict target-amplitude bound. -/
theorem finiteEvenFourTorusZ2GeometricDoobTargetMagnitude_lt_quarter
    (energyIdentity energyNontrivial : ℝ)
    (parameter : ℝ)
    (hParameter : 0 < parameter)
    (hParameterCutoff :
      parameter ≤
        finiteEvenFourTorusZ2GeometricDoobTargetMagnitudeQuarterCutoff
          energyIdentity energyNontrivial) :
    finiteEvenFourTorusZ2PerronPosteriorTargetMagnitudeFamily
        energyIdentity energyNontrivial parameter < 1 / 4 :=
  (Classical.choose_spec
    (exists_finiteEvenFourTorusZ2GeometricDoobTargetMagnitudeQuarterCutoff
      energyIdentity energyNontrivial)).2
    parameter hParameter hParameterCutoff

/-- Common direct-response cutoff: intersect the already constructed actual
posterior continuation interval with the unit target-response interval. -/
noncomputable def finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial) : ℝ :=
  min
    (finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy).couplingCutoff
    (finiteEvenFourTorusZ2GeometricDoobTargetMagnitudeQuarterCutoff
      energyIdentity energyNontrivial)

/-- The direct-response cutoff is strictly positive and volume independent. -/
theorem finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff_pos
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial) :
    0 < finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
      energyIdentity energyNontrivial hEnergy := by
  unfold finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
  exact lt_min
    (finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureCouplingCutoff_pos
      energyIdentity energyNontrivial hEnergy)
    (finiteEvenFourTorusZ2GeometricDoobTargetMagnitudeQuarterCutoff_pos
      energyIdentity energyNontrivial)

/-- The direct-response cutoff remains inside the actual posterior
continuation interval. -/
theorem finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff_le_actual
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial) :
    finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy ≤
      (finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
        energyIdentity energyNontrivial hEnergy).couplingCutoff := by
  unfold finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
  exact min_le_left _ _

/-- The direct-response cutoff also lies inside the unit target-amplitude
interval. -/
theorem finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff_le_target
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial) :
    finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy ≤
      finiteEvenFourTorusZ2GeometricDoobTargetMagnitudeQuarterCutoff
        energyIdentity energyNontrivial := by
  unfold finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
  exact min_le_right _ _

/-- On the direct-response interval, every canonical posterior envelope row
coefficient remains strictly below the actual continuation barrier `1/2`. -/
theorem finiteEvenFourTorusZ2GeometricDoobCanonicalEnvelopeRowCoefficient_lt_half
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy)
    (H : ℕ) :
    finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeRowCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy < 1 / 2 := by
  let C :=
    finiteEvenFourTorusZ2PerronPosteriorActualHighTemperatureContinuationData
      energyIdentity energyNontrivial hEnergy
  have hβActual : β ≤ C.couplingCutoff :=
    hβCutoff.trans
      (finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff_le_actual
        energyIdentity energyNontrivial hEnergy)
  have hEndpoint :=
    ((C.continuationFamily β hβ hβActual).endpoint_envelopeCoefficients_lt H).1
  change
    finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeRowCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy <
      finiteEvenFourTorusZ2PerronPosteriorHighTemperatureBarrier
    at hEndpoint
  simpa [finiteEvenFourTorusZ2PerronPosteriorHighTemperatureBarrier]
    using hEndpoint

/-- The unit target-response amplitude is below `1/4` throughout the direct
interval. -/
theorem finiteEvenFourTorusZ2GeometricDoobTargetMagnitude_lt_quarter_of_cutoff
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy) :
    finiteEvenFourTorusZ2PerronPosteriorTargetMagnitudeFamily
        energyIdentity energyNontrivial β < 1 / 4 :=
  finiteEvenFourTorusZ2GeometricDoobTargetMagnitude_lt_quarter
    energyIdentity energyNontrivial β hβ
    (hβCutoff.trans
      (finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff_le_target
        energyIdentity energyNontrivial hEnergy))

/-- At every finite side, the unit observable response has asymptotic
coefficient strictly below `1/2`. -/
theorem finiteEvenFourTorusZ2GeometricDoobUnitAsymptoticResponse_lt_half
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy)
    (H : ℕ) :
    finiteInfluenceKernelBidirectionalAsymptoticResponseCoefficient
        (finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeRowCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy)
        (finiteEvenFourTorusZ2PerronPosteriorTargetMagnitudeFamily
          energyIdentity energyNontrivial β)
        1 < 1 / 2 := by
  let rowCoefficient :=
    finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeRowCoefficient
      H β energyIdentity energyNontrivial hβ hEnergy
  let targetMagnitude :=
    finiteEvenFourTorusZ2PerronPosteriorTargetMagnitudeFamily
      energyIdentity energyNontrivial β
  have hRowHalf : rowCoefficient < 1 / 2 := by
    simpa [rowCoefficient] using
      finiteEvenFourTorusZ2GeometricDoobCanonicalEnvelopeRowCoefficient_lt_half
        energyIdentity energyNontrivial hEnergy β hβ hβCutoff H
  have hRowOne : rowCoefficient < 1 := lt_trans hRowHalf (by norm_num)
  have hDen : 0 < 1 - rowCoefficient := sub_pos.mpr hRowOne
  have hTargetQuarter : targetMagnitude < 1 / 4 := by
    simpa [targetMagnitude] using
      finiteEvenFourTorusZ2GeometricDoobTargetMagnitude_lt_quarter_of_cutoff
        energyIdentity energyNontrivial hEnergy β hβ hβCutoff
  have hInvLt : (1 - rowCoefficient)⁻¹ < 2 := by
    apply (inv_lt_iff₀ hDen).2
    nlinarith
  unfold finiteInfluenceKernelBidirectionalAsymptoticResponseCoefficient
  simp only [mul_one]
  calc
    targetMagnitude * (1 - rowCoefficient)⁻¹ <
        (1 / 4) * (1 - rowCoefficient)⁻¹ :=
      mul_lt_mul_of_pos_right hTargetQuarter (inv_pos.mpr hDen)
    _ < (1 / 4) * 2 :=
      mul_lt_mul_of_pos_left hInvLt (by norm_num)
    _ = 1 / 2 := by norm_num

/-- Some finite stationary-comparison depth realizes the common strict
unit-response coefficient at every finite side. -/
theorem exists_finiteEvenFourTorusZ2GeometricDoobDirectResponseIterations
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy)
    (H : ℕ) :
    ∃ iterations : ℕ,
      finiteInfluenceKernelBidirectionalFiniteResponseCoefficient
          (FiniteEvenFourTorusSpatialLink H)
          iterations
          (finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeRowCoefficient
            H β energyIdentity energyNontrivial hβ hEnergy)
          (finiteEvenFourTorusZ2PerronPosteriorTargetMagnitudeFamily
            energyIdentity energyNontrivial β)
          1 < 1 / 2 := by
  have hCard : 0 < Fintype.card (FiniteEvenFourTorusSpatialLink H) :=
    Fintype.card_pos_iff.mpr
      ⟨(⟨0, by simp⟩, ⟨1, by norm_num⟩)⟩
  have hRowNonneg :
      0 ≤ finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeRowCoefficient
        H β energyIdentity energyNontrivial hβ hEnergy :=
    finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeRowCoefficient_nonneg
      H β energyIdentity energyNontrivial hβ hEnergy
  have hRowLtOne :
      finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeRowCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy < 1 :=
    lt_trans
      (finiteEvenFourTorusZ2GeometricDoobCanonicalEnvelopeRowCoefficient_lt_half
        energyIdentity energyNontrivial hEnergy β hβ hβCutoff H)
      (by norm_num)
  have hTargetNonneg :
      0 ≤ finiteEvenFourTorusZ2PerronPosteriorTargetMagnitudeFamily
        energyIdentity energyNontrivial β := by
    simpa [finiteEvenFourTorusZ2PerronPosteriorTargetMagnitudeFamily] using
      finiteEvenFourTorusZ2PerronPosteriorTargetTiltSourceAmplitude_nonneg
        β energyIdentity energyNontrivial hβ hEnergy
  exact
    exists_finiteInfluenceKernelBidirectionalFiniteResponseCoefficient_lt
      hCard hRowNonneg hRowLtOne hTargetNonneg (by norm_num)
      (finiteEvenFourTorusZ2GeometricDoobUnitAsymptoticResponse_lt_half
        energyIdentity energyNontrivial hEnergy β hβ hβCutoff H)

/-- Canonical finite response-depth selector at one side. -/
noncomputable def finiteEvenFourTorusZ2GeometricDoobDirectResponseIterations
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy)
    (H : ℕ) : ℕ :=
  Classical.choose
    (exists_finiteEvenFourTorusZ2GeometricDoobDirectResponseIterations
      energyIdentity energyNontrivial hEnergy β hβ hβCutoff H)

/-- The selected depth realizes the strict finite response coefficient. -/
theorem finiteEvenFourTorusZ2GeometricDoobDirectResponseCoefficient_lt_half
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy)
    (H : ℕ) :
    finiteInfluenceKernelBidirectionalFiniteResponseCoefficient
        (FiniteEvenFourTorusSpatialLink H)
        (finiteEvenFourTorusZ2GeometricDoobDirectResponseIterations
          energyIdentity energyNontrivial hEnergy β hβ hβCutoff H)
        (finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeRowCoefficient
          H β energyIdentity energyNontrivial hβ hEnergy)
        (finiteEvenFourTorusZ2PerronPosteriorTargetMagnitudeFamily
          energyIdentity energyNontrivial β)
        1 < 1 / 2 :=
  Classical.choose_spec
    (exists_finiteEvenFourTorusZ2GeometricDoobDirectResponseIterations
      energyIdentity energyNontrivial hEnergy β hβ hβCutoff H)

/-- Coordinate-resolved unit observable-response matrix for the actual
Perron-smoothed posterior comparison underlying the geometric Doob row. -/
noncomputable def finiteEvenFourTorusZ2GeometricDoobDirectResponseInfluence
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy)
    (H : ℕ)
    (target source : FiniteEvenFourTorusSpatialLink H) : ℝ :=
  finiteInfluenceKernelObservableResponseEntry
    (finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeKernel
      H β energyIdentity energyNontrivial hβ hEnergy)
    (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTiltSourceEnvelope
      H β energyIdentity energyNontrivial target)
    (finiteEvenFourTorusZ2GeometricDoobDirectResponseIterations
      energyIdentity energyNontrivial hEnergy β hβ hβCutoff H)
    source

/-- Every direct response-matrix entry is nonnegative. -/
theorem finiteEvenFourTorusZ2GeometricDoobDirectResponseInfluence_nonneg
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy)
    (H : ℕ)
    (target source : FiniteEvenFourTorusSpatialLink H) :
    0 ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseInfluence
      energyIdentity energyNontrivial hEnergy β hβ hβCutoff
      H target source := by
  unfold finiteEvenFourTorusZ2GeometricDoobDirectResponseInfluence
  exact
    finiteInfluenceKernelObservableResponseEntry_nonneg
      (finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeKernel
        H β energyIdentity energyNontrivial hβ hEnergy)
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTiltSourceEnvelope
        H β energyIdentity energyNontrivial target)
      (finiteEvenFourTorusZ2UnfixedGaugePerronSmoothedTargetTiltSourceEnvelope_nonneg
        H β energyIdentity energyNontrivial hβ hEnergy target)
      (finiteEvenFourTorusZ2GeometricDoobDirectResponseIterations
        energyIdentity energyNontrivial hEnergy β hβ hβCutoff H)
      source

/-- Every source column of the actual coordinate-resolved response matrix has
the same volume-independent strict bound `1/2`. -/
theorem finiteEvenFourTorusZ2GeometricDoobDirectResponseInfluence_columnSum_lt_half
    (energyIdentity energyNontrivial : ℝ)
    (hEnergy : energyIdentity < energyNontrivial)
    (β : ℝ)
    (hβ : 0 < β)
    (hβCutoff :
      β ≤ finiteEvenFourTorusZ2GeometricDoobDirectResponseCutoff
        energyIdentity energyNontrivial hEnergy)
    (H : ℕ)
    (source : FiniteEvenFourTorusSpatialLink H) :
    (∑ target : FiniteEvenFourTorusSpatialLink H,
      finiteEvenFourTorusZ2GeometricDoobDirectResponseInfluence
        energyIdentity energyNontrivial hEnergy β hβ hβCutoff
        H target source) < 1 / 2 := by
  let kernel :=
    finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeKernel
      H β energyIdentity energyNontrivial hβ hEnergy
  let rowCoefficient :=
    finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeRowCoefficient
      H β energyIdentity energyNontrivial hβ hEnergy
  let envelopeMagnitude :=
    finiteEvenFourTorusZ2PerronPosteriorTargetMagnitudeFamily
      energyIdentity energyNontrivial β
  let iterations :=
    finiteEvenFourTorusZ2GeometricDoobDirectResponseIterations
      energyIdentity energyNontrivial hEnergy β hβ hβCutoff H
  have hCard : 0 < Fintype.card (FiniteEvenFourTorusSpatialLink H) :=
    Fintype.card_pos_iff.mpr ⟨source⟩
  have hRowNonneg : 0 ≤ rowCoefficient := by
    simpa [rowCoefficient] using
      finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeRowCoefficient_nonneg
        H β energyIdentity energyNontrivial hβ hEnergy
  have hRowSum :
      ∀ target : FiniteEvenFourTorusSpatialLink H,
        finiteInfluenceKernelRowSum kernel target ≤ rowCoefficient := by
    intro target
    have hMaximum := finiteInfluenceKernelRowSum_le_maximum kernel target
    simpa [kernel, rowCoefficient,
      finiteEvenFourTorusZ2PerronPosteriorCanonicalEnvelopeRowCoefficient]
      using hMaximum
  have hEnvelopeNonneg : 0 ≤ envelopeMagnitude := by
    simpa [envelopeMagnitude,
      finiteEvenFourTorusZ2PerronPosteriorTargetMagnitudeFamily] using
      finiteEvenFourTorusZ2PerronPosteriorTargetTiltSourceAmplitude_nonneg
        β energyIdentity energyNontrivial hβ hEnergy
  have hColumn :=
    finiteInfluenceKernelObservableResponseEntry_columnSum_le
      kernel hCard rowCoefficient hRowNonneg hRowSum
      envelopeMagnitude hEnvelopeNonneg iterations source
  have hFinite :
      finiteInfluenceKernelBidirectionalFiniteResponseCoefficient
          (FiniteEvenFourTorusSpatialLink H)
          iterations rowCoefficient envelopeMagnitude 1 < 1 / 2 := by
    simpa [iterations, rowCoefficient, envelopeMagnitude] using
      finiteEvenFourTorusZ2GeometricDoobDirectResponseCoefficient_lt_half
        energyIdentity energyNontrivial hEnergy β hβ hβCutoff H
  have hColumn' :
      (∑ target : FiniteEvenFourTorusSpatialLink H,
        finiteEvenFourTorusZ2GeometricDoobDirectResponseInfluence
          energyIdentity energyNontrivial hEnergy β hβ hβCutoff
          H target source) ≤
        finiteInfluenceKernelBidirectionalFiniteResponseCoefficient
          (FiniteEvenFourTorusSpatialLink H)
          iterations rowCoefficient envelopeMagnitude 1 := by
    simpa [finiteEvenFourTorusZ2GeometricDoobDirectResponseInfluence,
      kernel, iterations, envelopeMagnitude,
      finiteEvenFourTorusZ2PerronPosteriorTargetMagnitudeFamily,
      finiteEvenFourTorusZ2PerronPosteriorTargetTiltSourceEnvelope_eq_singleton]
      using hColumn
  exact lt_of_le_of_lt hColumn' hFinite

end

end MathlibAnalytic
end MGAP4D
