import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferencePinFreeResponseControlledStationaryTerminalResidual
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Pin-free asymptotic fixed-right response

The complete-block finite-step theorem leaves a fixed-volume Doeblin terminal
residual

  rho_H(beta)^n * exp(16 beta).

The existing complete-block Doeblin theory proves
`rho_H(beta)^n -> 0` for every fixed finite volume.  Therefore the terminal
term may be removed after the pin-free source-forcing resolvent has already
been established.

This file proves the resulting actual fixed-right target-ratio response bound:

  ResponseAbs(target, source)
    <= C_source(beta) * exp(16 beta) * W_target(source)
         / (1 - c_pf),

where

  c_pf = 18 * eta(beta) * s^2 + exp(16 beta) * M_R.

No distinguished-target pin is reintroduced.  The fixed-volume Doeblin
constant is used only to remove the terminal residual and does not enter the
final spatial coefficient.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal ProbabilityTheory BigOperators Topology

noncomputable section

local instance pinFreeResponseControlledAsymptoticResponseSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- After letting the complete-block depth tend to infinity, the literal
remote fixed-right target-ratio response is bounded purely by the pin-free
weighted source-forcing resolvent.  The fixed-volume Doeblin residual
disappears from the final coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs_le_pinFreeWeightedResolvent_of_remote
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
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
        beta s responseCoefficient < 1)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (hne : target ≠ source)
    (hNoShare :
      ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H target source)
    (g₁ g₂ h k : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
        H N hN beta hbeta B target source g₁ g₂ h k ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
          beta source source *
        Real.exp (16 * beta) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
          H s target source *
        (1 -
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
            beta s responseCoefficient)⁻¹ := by
  let bound : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant
        beta source source *
      Real.exp (16 * beta) *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftLocalHarnackBaseL1ExponentialWeight
        H s target source *
      (1 -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePinFreeResponseControlledExponentialWeightedColumnCoefficient
          beta s responseCoefficient)⁻¹
  let rho : ℝ :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMass
      H beta).toReal
  have hFinite :
      ∀ n : ℕ,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
            H N hN beta hbeta B target source g₁ g₂ h k ≤
          bound + rho ^ n * Real.exp (16 * beta) := by
    intro n
    have hNStep :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftKernelSectionContinuousProbabilityMeasure_fixedRightTargetRatio_response_abs_le_pinFreeWeightedResolvent_add_terminalBlockResidual_of_remote
        H N hN beta hbeta s hs R hRNonneg hResponse
        responseCoefficient hResponseCoefficient target source hResponseWeighted
        hCoefficientLtOne B hne hNoShare g₁ g₂ h k n
    simpa [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs,
      bound, rho] using hNStep
  have hPow :
      Tendsto (fun n : ℕ => rho ^ n) atTop (𝓝 0) := by
    dsimp [rho]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRestrictedRandomScanFullBlockResidualMass_toReal_pow_tendsto_zero
        H beta
  have hTail :
      Tendsto
        (fun n : ℕ => rho ^ n * Real.exp (16 * beta))
        atTop (𝓝 0) := by
    have h :=
      hPow.mul_const (Real.exp (16 * beta))
    simpa using h
  have hConst :
      Tendsto (fun _n : ℕ => bound) atTop (𝓝 bound) :=
    tendsto_const_nhds
  have hLimit :
      Tendsto
        (fun n : ℕ => bound + rho ^ n * Real.exp (16 * beta))
        atTop (𝓝 bound) := by
    simpa using hConst.add hTail
  have hFinal :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioResponseAbs
          H N hN beta hbeta B target source g₁ g₂ h k ≤
        bound :=
    le_of_tendsto hLimit (Filter.Eventually.of_forall hFinite)
  simpa [bound] using hFinal

end

end MathlibAnalytic
end MGAP4D
