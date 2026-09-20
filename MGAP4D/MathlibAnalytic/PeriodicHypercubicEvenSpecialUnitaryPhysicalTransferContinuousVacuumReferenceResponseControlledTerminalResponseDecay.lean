import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceResponseControlledSourceForcingResolvent
import Mathlib.Tactic

/-!
# Response-controlled terminal fixed-right response decay

The stationary response decomposition still contains an n-step terminal term.
This file replaces the old coarse tagged left-left propagation in that terminal
estimate by the response-controlled physical orbit.

For the literal fixed-right target-ratio observable,
  terminal_n <= 2 * sum_e v_n(e).

If the fixed-right response profile has target-centered weighted mass M and the
response-controlled weighted coefficient
  c_R = 18 * eta(beta) * s^2 + eta(beta) + exp(16 beta) * M
is strictly below one, then
  v_n(e) <= q_R^n * exp(16 beta) * W_T(e)
with q_R < 1.  At each fixed finite volume the finite weighted mass sum_e W_T(e)
is a harmless constant, so the terminal response tends to zero.

No volume-uniform terminal estimate is claimed or needed here.  The uniform
quantity retained for the later self-consistent closure is the source-forcing
resolvent proved in the preceding theorem unit.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory BigOperators Topology

noncomputable section

local instance responseControlledTerminalResponseDecaySpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance responseControlledTerminalResponseDecaySpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance responseControlledTerminalResponseDecaySpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance responseControlledTerminalResponseDecaySpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance responseControlledTerminalResponseDecaySpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance responseControlledTerminalResponseDecaySpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The n-step terminal fixed-right response is controlled by twice the total
response-controlled physical left-variation mass. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioNStepTerminalResponseAbs_le_two_mul_responseControlledVariationTotal
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (R :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hRNonneg : ∀ target source, 0 ≤ R target source)
    (hResponse :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioUniformResponseProfileBound
        H N hN beta hbeta R)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (g₁ g₂ h k : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioNStepTerminalResponseAbs
        H N hN beta hbeta B target source g₁ g₂ h k n ≤
      2 *
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledRandomScanVariationIterate
            H beta hbeta target R hRNonneg
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
              H beta target)
            n e := by
  classical
  let F :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ :=
    fun C =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta C B target g₁ /
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta C B target g₂
  let variation : PeriodicHypercubicEvenSpatialSliceLink H → ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
      H beta target
  let smoothed :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate
      H N hN beta hbeta B target source g₂ k F n
  let propagated : PeriodicHypercubicEvenSpatialSliceLink H → ℝ :=
    fun e =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledRandomScanVariationIterate
        H beta hbeta target R hRNonneg variation n e
  let μh :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
      H N hN beta hbeta
      (Function.update (Function.update B source h) target g₂)
  let μk :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
      H N hN beta hbeta
      (Function.update (Function.update B source k) target g₂)
  have hF : StronglyMeasurable F := by
    simpa [F] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatio_stronglyMeasurable
        H N beta B target g₁ g₂
  have hVariationNonneg : ∀ e, 0 ≤ variation e := by
    simpa [variation] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_nonneg
        H beta target
  have hVariation :
      ∀ (e : PeriodicHypercubicEvenSpatialSliceLink H)
        (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (u v : Matrix.specialUnitaryGroup (Fin N) ℂ),
        |F (Function.update C e u) - F (Function.update C e v)| ≤ variation e := by
    simpa [F, variation] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatio_variation_le
        H N hN beta hbeta B target g₁ g₂
  have hSmoothedMeas : StronglyMeasurable smoothed := by
    dsimp [smoothed]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_stronglyMeasurable
        H N hN beta hbeta B target source g₂ k F hF n
  have hPropagatedNonneg : ∀ e, 0 ≤ propagated e := by
    intro e
    dsimp [propagated, variation]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledRandomScanVariationIterate_nonneg
        H beta hbeta target R hRNonneg
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
          H beta target)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_nonneg
          H beta target)
        n e
  have hPropagatedVariation :
      ∀ (e : PeriodicHypercubicEvenSpatialSliceLink H)
        (C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (u v : Matrix.specialUnitaryGroup (Fin N) ℂ),
        |smoothed (Function.update C e u) -
          smoothed (Function.update C e v)| ≤ propagated e := by
    intro e C u v
    dsimp [smoothed, propagated]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberRestrictedRandomScanExpectationIterate_fiberVariation_le_responseControlled
        H N hN beta hbeta R hRNonneg hResponse
        B target source g₂ k F hF variation hVariationNonneg hVariation n e C u v
  have hμh : IsProbabilityMeasure μh := by
    dsimp [μh]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_isProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B source h) target g₂)
  have hμk : IsProbabilityMeasure μk := by
    dsimp [μk]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_isProbabilityMeasure
        H N hN beta hbeta
        (Function.update (Function.update B source k) target g₂)
  have hBound :=
    probabilityMeasure_integral_difference_abs_le_two_mul_updateVariationSum
      smoothed hSmoothedMeas propagated hPropagatedNonneg
      hPropagatedVariation μh μk hμh hμk B
  change
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioNStepTerminalResponseAbs
        H N hN beta hbeta B target source g₁ g₂ h k n ≤
      2 * ∑ e : PeriodicHypercubicEvenSpatialSliceLink H, propagated e
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioNStepTerminalResponseAbs,
    smoothed, μh, μk, F] using hBound

/-- The terminal response has an explicit finite-volume geometric envelope
generated by the response-controlled weighted rate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioNStepTerminalResponseAbs_le_responseControlledWeightedRatePow
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : ℝ)
    (hs : 1 ≤ s)
    (R :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hRNonneg : ∀ target source, 0 ≤ R target source)
    (hResponse :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioUniformResponseProfileBound
        H N hN beta hbeta R)
    (responseCoefficient : ℝ)
    (hResponseCoefficient : 0 ≤ responseCoefficient)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hResponseWeighted :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseExponentialWeightedColumnBound
        H s target R responseCoefficient)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g₁ g₂ h k : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (n : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioNStepTerminalResponseAbs
        H N hN beta hbeta B target source g₁ g₂ h k n ≤
      2 *
        ((finiteInfluenceKernelReciprocalRandomScanRate
          (PeriodicHypercubicEvenSpatialSliceLink H)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceResponseControlledExponentialWeightedColumnCoefficient
            beta s responseCoefficient)) ^ n *
          Real.exp (16 * beta) *
          ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
              H s target e) := by
  have hTerminal :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioNStepTerminalResponseAbs_le_two_mul_responseControlledVariationTotal
      H N hN beta hbeta R hRNonneg hResponse B target source g₁ g₂ h k n
  have hVariationNonneg :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_nonneg
      H beta target
  have hVariationBound :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_le_exp_sixteen_mul_weight
      H beta s hs target
  have hPointwise :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledRandomScanVariationIterate
            H beta hbeta target R hRNonneg
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
              H beta target)
            n e ≤
          (finiteInfluenceKernelReciprocalRandomScanRate
            (PeriodicHypercubicEvenSpatialSliceLink H)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceResponseControlledExponentialWeightedColumnCoefficient
              beta s responseCoefficient)) ^ n *
            Real.exp (16 * beta) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
              H s target e := by
    intro e
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledRandomScanVariationIterate_le_weightedRate_pow_mul
        H beta hbeta s hs target R hRNonneg
        responseCoefficient hResponseCoefficient hResponseWeighted
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
          H beta target)
        hVariationNonneg
        (Real.exp (16 * beta))
        (Real.exp_pos _).le
        hVariationBound n e
  calc
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioNStepTerminalResponseAbs
        H N hN beta hbeta B target source g₁ g₂ h k n ≤
      2 *
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledRandomScanVariationIterate
            H beta hbeta target R hRNonneg
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
              H beta target)
            n e := hTerminal
    _ ≤
      2 *
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          (finiteInfluenceKernelReciprocalRandomScanRate
            (PeriodicHypercubicEvenSpatialSliceLink H)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceResponseControlledExponentialWeightedColumnCoefficient
              beta s responseCoefficient)) ^ n *
            Real.exp (16 * beta) *
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
              H s target e := by
        gcongr with e
        exact hPointwise e
    _ =
      2 *
        ((finiteInfluenceKernelReciprocalRandomScanRate
          (PeriodicHypercubicEvenSpatialSliceLink H)
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceResponseControlledExponentialWeightedColumnCoefficient
            beta s responseCoefficient)) ^ n *
          Real.exp (16 * beta) *
          ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
              H s target e) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]
        ring

/-- At fixed finite volume, strict response-controlled weighted coefficient
forces the terminal fixed-right response to vanish as scan depth tends to
infinity. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioNStepTerminalResponseAbs_tendsto_zero
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : ℝ)
    (hs : 1 ≤ s)
    (R :
      PeriodicHypercubicEvenSpatialSliceLink H →
        PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hRNonneg : ∀ target source, 0 ≤ R target source)
    (hResponse :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioUniformResponseProfileBound
        H N hN beta hbeta R)
    (responseCoefficient : ℝ)
    (hResponseCoefficient : 0 ≤ responseCoefficient)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (hResponseWeighted :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseExponentialWeightedColumnBound
        H s target R responseCoefficient)
    (hCoefficientLtOne :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceResponseControlledExponentialWeightedColumnCoefficient
        beta s responseCoefficient < 1)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g₁ g₂ h k : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Tendsto
      (fun n : ℕ =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioNStepTerminalResponseAbs
          H N hN beta hbeta B target source g₁ g₂ h k n)
      atTop (nhds 0) := by
  let coefficient :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceResponseControlledExponentialWeightedColumnCoefficient
      beta s responseCoefficient
  let rate :=
    finiteInfluenceKernelReciprocalRandomScanRate
      (PeriodicHypercubicEvenSpatialSliceLink H) coefficient
  let amplitude :=
    2 *
      (Real.exp (16 * beta) *
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
            H s target e)
  have hCardNat :
      0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) :=
    Fintype.card_pos_iff.mpr ⟨target⟩
  have hCoefficientNonneg : 0 ≤ coefficient := by
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceResponseControlledExponentialWeightedColumnCoefficient_nonneg
        beta s responseCoefficient hbeta hResponseCoefficient
  have hRateNonneg : 0 ≤ rate :=
    finiteInfluenceKernelReciprocalRandomScanRate_nonneg
      hCardNat coefficient hCoefficientNonneg
  have hRateLtOne : rate < 1 :=
    finiteInfluenceKernelReciprocalRandomScanRate_lt_one
      hCardNat coefficient (by simpa [coefficient] using hCoefficientLtOne)
  have hPow : Tendsto (fun n : ℕ => rate ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hRateNonneg hRateLtOne
  have hEnvelope :
      Tendsto (fun n : ℕ => amplitude * rate ^ n) atTop (nhds 0) := by
    simpa [mul_comm] using tendsto_const_nhds.mul hPow
  have hLower :
      ∀ n : ℕ,
        0 ≤
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioNStepTerminalResponseAbs
            H N hN beta hbeta B target source g₁ g₂ h k n := by
    intro n
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioNStepTerminalResponseAbs
    exact abs_nonneg _
  have hUpper :
      ∀ n : ℕ,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioNStepTerminalResponseAbs
            H N hN beta hbeta B target source g₁ g₂ h k n ≤
          amplitude * rate ^ n := by
    intro n
    have h :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioNStepTerminalResponseAbs_le_responseControlledWeightedRatePow
        H N hN beta hbeta s hs R hRNonneg hResponse
        responseCoefficient hResponseCoefficient target source hResponseWeighted
        B g₁ g₂ h k n
    simpa [amplitude, rate, coefficient, mul_assoc, mul_left_comm, mul_comm] using h
  exact squeeze_zero'
    (Filter.Eventually.of_forall hLower)
    (Filter.Eventually.of_forall hUpper)
    hEnvelope

end

end MathlibAnalytic
end MGAP4D
