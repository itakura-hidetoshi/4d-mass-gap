import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportEffectiveEnergySingleModeExactConcrete
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter
open scoped InnerProductSpace LinearPMap Topology BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

/-- Attainment of the asymptotic effective-energy limit at a prescribed finite
order is exactly the single-log-generator-mode locus. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_effectiveEnergyLimit_eq_finite_iff_logGeneratorMode
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) (hv : v ≠ 0) (n : ℕ) (lambda : ℝ)
    (hlambda : |lambda| <
      2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
        H N hN beta hbeta) :
    let q :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
        H N hN beta hbeta v
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_effectiveEnergyLimit
        H N hN beta hbeta v lambda =
      lambda + (iteratedDeriv (n + 1) q lambda /
        ((n + 1 : ℝ) * iteratedDeriv n q lambda))⁻¹ ↔
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportIsSingleLogGeneratorMode
        H N hN beta hbeta v := by
  dsimp only
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
      H N hN beta hbeta v
  constructor
  · intro heq
    by_contra hnot
    have hltRaw :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_effectiveEnergyLimit_lt_of_not_logGeneratorMode
        H N hN beta hbeta v hv lambda hlambda hnot
    have hlt := hltRaw n
    have hlt' :
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_effectiveEnergyLimit
            H N hN beta hbeta v lambda <
          lambda + (iteratedDeriv (n + 1) q lambda /
            ((n + 1 : ℝ) * iteratedDeriv n q lambda))⁻¹ := by
      simpa [q] using hlt
    rw [heq] at hlt'
    exact lt_irrefl _ hlt'
  · intro hmode
    rcases
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_singleLogGeneratorMode_exactEffectiveEnergy
        H N hN beta hbeta v hv hmode with ⟨rho, hall⟩
    have h := hall lambda hlambda
    dsimp only at h
    have hfinite :
        lambda + (iteratedDeriv (n + 1) q lambda /
          ((n + 1 : ℝ) * iteratedDeriv n q lambda))⁻¹ = rho := by
      simpa [q] using h.1 n
    calc
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_effectiveEnergyLimit
          H N hN beta hbeta v lambda = rho := h.2
      _ = lambda + (iteratedDeriv (n + 1) q lambda /
          ((n + 1 : ℝ) * iteratedDeriv n q lambda))⁻¹ := hfinite.symm

/-- Off the pure-mode locus the asymptotic limit is strictly below every
prescribed finite-order effective energy, and conversely any such strict gap
rules out a single log-generator mode. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_effectiveEnergyLimit_lt_finite_iff_not_logGeneratorMode
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) (hv : v ≠ 0) (n : ℕ) (lambda : ℝ)
    (hlambda : |lambda| <
      2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
        H N hN beta hbeta) :
    let q :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
        H N hN beta hbeta v
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_effectiveEnergyLimit
        H N hN beta hbeta v lambda <
      lambda + (iteratedDeriv (n + 1) q lambda /
        ((n + 1 : ℝ) * iteratedDeriv n q lambda))⁻¹ ↔
      ¬ periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportIsSingleLogGeneratorMode
        H N hN beta hbeta v := by
  dsimp only
  constructor
  · intro hlt hmode
    have heq :=
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_effectiveEnergyLimit_eq_finite_iff_logGeneratorMode
        H N hN beta hbeta v hv n lambda hlambda).2 hmode
    rw [heq] at hlt
    exact lt_irrefl _ hlt
  · intro hnot
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_effectiveEnergyLimit_lt_of_not_logGeneratorMode
        H N hN beta hbeta v hv lambda hlambda hnot n

end

end MathlibAnalytic
end MGAP4D
