import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceResponseControlledTerminalResponseDecay
import Mathlib.Tactic

/-!
# Terminal-free response-controlled stationary fixed-right response

The finite-step stationary decomposition from the response-controlled route is

  literal response <= accumulated source discrepancy_n + terminal_n.

The preceding theorem units give, under a strict target-centered weighted
response-controlled coefficient,

  accumulated source discrepancy_n
    <= gamma(beta) * exp(16 beta) * W_target(source) * (1-c_R)^{-1}

uniformly in n, while the terminal term tends to zero at every fixed finite
volume.

This file removes the terminal term by an order limit.  No new response,
covariance, sweep-contraction, Poincare/coercivity, or mass-gap hypothesis is
introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory BigOperators Topology

noncomputable section

local instance responseControlledStationaryResolventResponseSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance responseControlledStationaryResolventResponseSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance responseControlledStationaryResolventResponseSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance responseControlledStationaryResolventResponseSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance responseControlledStationaryResolventResponseSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance responseControlledStationaryResolventResponseSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Once the response-controlled weighted coefficient is strict, the literal
remote fixed-right target-ratio response is bounded directly by the
volume-independent source-forcing resolvent; the finite-step terminal response
has disappeared. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_fixedRightTargetRatio_response_abs_le_responseControlledWeightedResolvent_of_remote
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
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    {target source : PeriodicHypercubicEvenSpatialSliceLink H}
    (hne : target ≠ source)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H target source)
    (hResponseWeighted :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseExponentialWeightedColumnBound
        H s target R responseCoefficient)
    (hCoefficientLtOne :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceResponseControlledExponentialWeightedColumnCoefficient
        beta s responseCoefficient < 1)
    (g₁ g₂ h k : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    |(∫ A,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
              H N beta A B target g₁ /
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
              H N beta A B target g₂
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta
          (Function.update (Function.update B source h) target g₂)) -
      (∫ A,
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
              H N beta A B target g₁ /
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
              H N beta A B target g₂
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
          H N hN beta hbeta
          (Function.update (Function.update B source k) target g₂))| ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
          beta source source *
        Real.exp (16 * beta) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s target source *
        (1 -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceResponseControlledExponentialWeightedColumnCoefficient
            beta s responseCoefficient)⁻¹ := by
  let K : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
        beta source source *
      Real.exp (16 * beta) *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
        H s target source *
      (1 -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceResponseControlledExponentialWeightedColumnCoefficient
          beta s responseCoefficient)⁻¹
  let terminal : ℕ → ℝ :=
    fun n =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioNStepTerminalResponseAbs
        H N hN beta hbeta B target source g₁ g₂ h k n
  have hTerminal :
      Tendsto terminal atTop (nhds 0) := by
    dsimp [terminal]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioNStepTerminalResponseAbs_tendsto_zero
        H N hN beta hbeta s hs R hRNonneg hResponse
        responseCoefficient hResponseCoefficient target source
        hResponseWeighted hCoefficientLtOne B g₁ g₂ h k
  have hRhs :
      Tendsto (fun n : ℕ => K + terminal n) atTop (nhds K) := by
    simpa using (tendsto_const_nhds.add hTerminal)
  have hFinite :
      ∀ n : ℕ,
        |(∫ A,
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                  H N beta A B target g₁ /
              periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                  H N beta A B target g₂
            ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
              H N hN beta hbeta
              (Function.update (Function.update B source h) target g₂)) -
          (∫ A,
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                  H N beta A B target g₁ /
              periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                  H N beta A B target g₂
            ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
              H N hN beta hbeta
              (Function.update (Function.update B source k) target g₂))| ≤
          K + terminal n := by
    intro n
    have hStationary :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_fixedRightTargetRatio_response_abs_le_responseControlledAccumulated_add_terminal_of_remote
        H N hN beta hbeta R hRNonneg hResponse B hne hNoShare g₁ g₂ h k n
    have hAccum :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioAccumulatedSourceDiscrepancy_le_weightedResolvent
        H beta hbeta s hs target source R hRNonneg
        responseCoefficient hResponseCoefficient hResponseWeighted
        hCoefficientLtOne n
    calc
      |(∫ A,
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                H N beta A B target g₁ /
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                H N beta A B target g₂
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta
            (Function.update (Function.update B source h) target g₂)) -
        (∫ A,
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                H N beta A B target g₁ /
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                H N beta A B target g₂
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta
            (Function.update (Function.update B source k) target g₂))| ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedTargetResponseControlledAccumulatedSourceDiscrepancy
          H beta hbeta target source R hRNonneg
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
            H beta target)
          n +
        terminal n := by
          simpa [terminal] using hStationary
      _ ≤ K + terminal n := by
        exact add_le_add
          (by simpa [K] using hAccum)
          (le_refl (terminal n))
  have hLimit :
      |(∫ A,
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                H N beta A B target g₁ /
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                H N beta A B target g₂
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta
            (Function.update (Function.update B source h) target g₂)) -
        (∫ A,
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                H N beta A B target g₁ /
            periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
                H N beta A B target g₂
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure
            H N hN beta hbeta
            (Function.update (Function.update B source k) target g₂))| ≤ K := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hRhs
    exact Filter.Eventually.of_forall hFinite
  simpa [K] using hLimit

/-- The terminal-free theorem in the repository's literal fixed-right response
notation. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs_le_responseControlledWeightedResolvent_of_remote
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
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    {target source : PeriodicHypercubicEvenSpatialSliceLink H}
    (hne : target ≠ source)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H target source)
    (hResponseWeighted :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseExponentialWeightedColumnBound
        H s target R responseCoefficient)
    (hCoefficientLtOne :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceResponseControlledExponentialWeightedColumnCoefficient
        beta s responseCoefficient < 1)
    (g₁ g₂ h k : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
        H N hN beta hbeta B target source g₁ g₂ h k ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
          beta source source *
        Real.exp (16 * beta) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s target source *
        (1 -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceResponseControlledExponentialWeightedColumnCoefficient
            beta s responseCoefficient)⁻¹ := by
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs] using
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_fixedRightTargetRatio_response_abs_le_responseControlledWeightedResolvent_of_remote
      H N hN beta hbeta s hs R hRNonneg hResponse
      responseCoefficient hResponseCoefficient B hne hNoShare
      hResponseWeighted hCoefficientLtOne g₁ g₂ h k

end

end MathlibAnalytic
end MGAP4D
