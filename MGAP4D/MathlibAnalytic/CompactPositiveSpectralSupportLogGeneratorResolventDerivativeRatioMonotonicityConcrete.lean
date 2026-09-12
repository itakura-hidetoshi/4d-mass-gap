import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventDerivativeRatioMonotonicity
import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventTuranHierarchyConcrete
import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventStrictAbsoluteMonotonicityConcrete
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter
open scoped InnerProductSpace LinearPMap Topology BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

/-- On the actual one-step physical positive spectral support, the
factorial-normalized consecutive derivative ratio is nondecreasing in order
throughout the full symmetric finite-volume coercive gap. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_mono
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) (hv : v ≠ 0) (n : ℕ) (lambda : ℝ)
    (hlambda : |lambda| <
      2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
        H N hN beta hbeta) :
    let q :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
        H N hN beta hbeta v
    iteratedDeriv (n + 1) q lambda /
        ((n + 1 : ℝ) * iteratedDeriv n q lambda) ≤
      iteratedDeriv (n + 2) q lambda /
        ((n + 2 : ℝ) * iteratedDeriv (n + 1) q lambda) := by
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
      H N hN beta hbeta v
  change iteratedDeriv (n + 1) q lambda /
      ((n + 1 : ℝ) * iteratedDeriv n q lambda) ≤
    iteratedDeriv (n + 2) q lambda /
      ((n + 2 : ℝ) * iteratedDeriv (n + 1) q lambda)
  have hn : 0 < iteratedDeriv n q lambda := by
    simpa [q] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_iteratedDeriv_pos
        H N hN beta hbeta v hv n lambda hlambda)
  have hn1 : 0 < iteratedDeriv (n + 1) q lambda := by
    simpa [q] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_iteratedDeriv_pos
        H N hN beta hbeta v hv (n + 1) lambda hlambda)
  have hden0 : 0 < (n + 1 : ℝ) * iteratedDeriv n q lambda := by positivity
  have hden1 : 0 < (n + 2 : ℝ) * iteratedDeriv (n + 1) q lambda := by positivity
  rw [div_le_div_iff₀ hden0 hden1]
  have hturan :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_iteratedDeriv_turan
      H N hN beta hbeta v hv n lambda hlambda
  change
    iteratedDeriv (n + 1) q lambda *
        ((n + 2 : ℝ) * iteratedDeriv (n + 1) q lambda) ≤
      iteratedDeriv (n + 2) q lambda *
        ((n + 1 : ℝ) * iteratedDeriv n q lambda)
  dsimp [q] at hturan
  nlinarith

end

end MathlibAnalytic
end MGAP4D
