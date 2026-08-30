import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventDerivativeRatioParameterMonotonicity
import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventGlobalDerivativeRatioOrderConcrete
import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventTuranHierarchyConcrete
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter
open scoped InnerProductSpace LinearPMap Topology BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

/-- On the actual one-step physical positive spectral support, every normalized
consecutive derivative ratio has strictly positive spectral-parameter derivative
throughout the full symmetric finite-volume coercive gap. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_deriv_pos
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) (hv : v ≠ 0) (n : ℕ) (lambda : ℝ)
    (hlambda : |lambda| <
      2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
        H N hN beta hbeta) :
    let q :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
        H N hN beta hbeta v
    0 < deriv (fun t : ℝ =>
      iteratedDeriv (n + 1) q t /
        ((n + 1 : ℝ) * iteratedDeriv n q t)) lambda := by
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
      H N hN beta hbeta v
  change 0 < deriv (fun t : ℝ =>
    iteratedDeriv (n + 1) q t /
      ((n + 1 : ℝ) * iteratedDeriv n q t)) lambda
  have hn : 0 < iteratedDeriv n q lambda := by
    simpa [q] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_iteratedDeriv_pos
        H N hN beta hbeta v hv n lambda hlambda)
  have hn1 : 0 < iteratedDeriv (n + 1) q lambda := by
    simpa [q] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_iteratedDeriv_pos
        H N hN beta hbeta v hv (n + 1) lambda hlambda)
  have hn2 : 0 < iteratedDeriv (n + 2) q lambda := by
    simpa [q] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_iteratedDeriv_pos
        H N hN beta hbeta v hv (n + 2) lambda hlambda)
  have hdiffn : DifferentiableAt ℝ (iteratedDeriv n q) lambda := by
    apply differentiableAt_of_deriv_ne_zero
    simpa only [iteratedDeriv_succ] using hn1.ne'
  have hdiffn1 : DifferentiableAt ℝ (iteratedDeriv (n + 1) q) lambda := by
    apply differentiableAt_of_deriv_ne_zero
    simpa only [iteratedDeriv_succ] using hn2.ne'
  have hderivn : HasDerivAt (iteratedDeriv n q) (iteratedDeriv (n + 1) q lambda) lambda := by
    simpa only [iteratedDeriv_succ] using hdiffn.hasDerivAt
  have hderivn1 : HasDerivAt (iteratedDeriv (n + 1) q)
      (iteratedDeriv (n + 2) q lambda) lambda := by
    simpa only [iteratedDeriv_succ] using hdiffn1.hasDerivAt
  have hden_ne : (n + 1 : ℝ) * iteratedDeriv n q lambda ≠ 0 := by positivity
  have hratio := hderivn1.div (hderivn.const_mul (n + 1 : ℝ)) hden_ne
  change HasDerivAt (fun t : ℝ =>
      iteratedDeriv (n + 1) q t /
        ((n + 1 : ℝ) * iteratedDeriv n q t))
      ((iteratedDeriv (n + 2) q lambda * ((n + 1 : ℝ) * iteratedDeriv n q lambda) -
          iteratedDeriv (n + 1) q lambda *
            ((n + 1 : ℝ) * iteratedDeriv (n + 1) q lambda)) /
        ((n + 1 : ℝ) * iteratedDeriv n q lambda) ^ 2) lambda at hratio
  have hturan :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_iteratedDeriv_turan
      H N hN beta hbeta v hv n lambda hlambda
  change
    (n + 2 : ℝ) * (iteratedDeriv (n + 1) q lambda) ^ 2 ≤
      (n + 1 : ℝ) * iteratedDeriv n q lambda * iteratedDeriv (n + 2) q lambda at hturan
  have hnum :
      0 < iteratedDeriv (n + 2) q lambda *
          ((n + 1 : ℝ) * iteratedDeriv n q lambda) -
        iteratedDeriv (n + 1) q lambda *
          ((n + 1 : ℝ) * iteratedDeriv (n + 1) q lambda) := by
    nlinarith
  rw [hratio.deriv]
  exact div_pos hnum (sq_pos_of_pos (by positivity))

/-- At every derivative order on the actual physical positive spectral support,
the normalized response scale is strictly increasing in the spectral parameter. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_strictMonoOn
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) (hv : v ≠ 0) (n : ℕ) :
    let c :=
      2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
        H N hN beta hbeta
    let q :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
        H N hN beta hbeta v
    StrictMonoOn (fun lambda : ℝ =>
      iteratedDeriv (n + 1) q lambda /
        ((n + 1 : ℝ) * iteratedDeriv n q lambda)) (Set.Ioo (-c) c) := by
  let c :=
    2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
      H N hN beta hbeta
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
      H N hN beta hbeta v
  let R := fun lambda : ℝ =>
    iteratedDeriv (n + 1) q lambda /
      ((n + 1 : ℝ) * iteratedDeriv n q lambda)
  change StrictMonoOn R (Set.Ioo (-c) c)
  have hdpos : ∀ lambda ∈ Set.Ioo (-c) c, 0 < deriv R lambda := by
    intro lambda hlambda
    simpa [R, q, c] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_deriv_pos
        H N hN beta hbeta v hv n lambda (by simpa [c] using (abs_lt.mpr hlambda)))
  apply strictMonoOn_of_deriv_pos (convex_Ioo (-c) c)
  · intro lambda hlambda
    exact
      (differentiableAt_of_deriv_ne_zero (hdpos lambda hlambda).ne').continuousAt.continuousWithinAt
  · simpa only [interior_Ioo] using hdpos

/-- Mixed order/parameter comparison on the actual one-step physical positive
spectral support. Raising derivative order and moving the spectral parameter to
the right can only increase the normalized response scale. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_le_of_le_of_le
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) (hv : v ≠ 0) {n m : ℕ} (hnm : n ≤ m)
    {lambda mu : ℝ}
    (hlambda : lambda ∈ Set.Ioo
      (-(2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
        H N hN beta hbeta))
      (2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
        H N hN beta hbeta))
    (hmu : mu ∈ Set.Ioo
      (-(2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
        H N hN beta hbeta))
      (2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
        H N hN beta hbeta))
    (hlm : lambda ≤ mu) :
    let q :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
        H N hN beta hbeta v
    iteratedDeriv (n + 1) q lambda /
        ((n + 1 : ℝ) * iteratedDeriv n q lambda) ≤
      iteratedDeriv (m + 1) q mu /
        ((m + 1 : ℝ) * iteratedDeriv m q mu) := by
  dsimp only
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
        H N hN beta hbeta v hv lambda (abs_lt.mpr hlambda) hnm
    _ ≤ iteratedDeriv (m + 1)
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
            H N hN beta hbeta v) mu /
        ((m + 1 : ℝ) * iteratedDeriv m
          (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
            H N hN beta hbeta v) mu) :=
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_strictMonoOn
        H N hN beta hbeta v hv m).monotoneOn hlambda hmu hlm

end

end MathlibAnalytic
end MGAP4D
