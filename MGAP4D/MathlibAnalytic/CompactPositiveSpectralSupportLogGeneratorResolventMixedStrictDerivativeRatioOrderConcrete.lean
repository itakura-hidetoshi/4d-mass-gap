import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventMixedStrictDerivativeRatioOrder
import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventDerivativeRatioParameterMonotonicityConcrete
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter
open scoped InnerProductSpace LinearPMap Topology BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

/-- On the actual one-step physical positive spectral support, the normalized
response scale at every derivative order is injective in the spectral parameter
throughout the full symmetric finite-volume coercive gap. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_injOn
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) (hv : v ≠ 0) (n : ℕ) :
    let c :=
      2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
        H N hN beta hbeta
    let q :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
        H N hN beta hbeta v
    Set.InjOn (fun lambda : ℝ =>
      iteratedDeriv (n + 1) q lambda /
        ((n + 1 : ℝ) * iteratedDeriv n q lambda)) (Set.Ioo (-c) c) := by
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_strictMonoOn
      H N hN beta hbeta v hv n).injOn

/-- Physical mixed strict comparison.  Derivative order may increase weakly,
but any strict rightward spectral-parameter move forces a strict increase in
the normalized response scale. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_lt_of_le_of_lt
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) (hv : v ≠ 0) {n m : ℕ} (hnm : n ≤ m)
    {lambda mu : ℝ}
    (hlambda : |lambda| <
      2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
        H N hN beta hbeta)
    (hmu : |mu| <
      2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
        H N hN beta hbeta) (hlm : lambda < mu) :
    let q :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
        H N hN beta hbeta v
    iteratedDeriv (n + 1) q lambda /
        ((n + 1 : ℝ) * iteratedDeriv n q lambda) <
      iteratedDeriv (m + 1) q mu /
        ((m + 1 : ℝ) * iteratedDeriv m q mu) := by
  dsimp only
  have hlambdaI : lambda ∈ Set.Ioo
      (-(2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
        H N hN beta hbeta))
      (2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
        H N hN beta hbeta) := abs_lt.mp hlambda
  have hmuI : mu ∈ Set.Ioo
      (-(2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
        H N hN beta hbeta))
      (2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
        H N hN beta hbeta) := abs_lt.mp hmu
  calc
    iteratedDeriv (n + 1)
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
            H N hN beta hbeta v) lambda /
        ((n + 1 : ℝ) * iteratedDeriv n
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
            H N hN beta hbeta v) lambda) ≤
      iteratedDeriv (m + 1)
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
            H N hN beta hbeta v) lambda /
        ((m + 1 : ℝ) * iteratedDeriv m
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
            H N hN beta hbeta v) lambda) :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_le_of_le
        H N hN beta hbeta v hv lambda hlambda hnm
    _ < iteratedDeriv (m + 1)
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
            H N hN beta hbeta v) mu /
        ((m + 1 : ℝ) * iteratedDeriv m
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
            H N hN beta hbeta v) mu) :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_strictMonoOn
        H N hN beta hbeta v hv m hlambdaI hmuI hlm

end

end MathlibAnalytic
end MGAP4D
