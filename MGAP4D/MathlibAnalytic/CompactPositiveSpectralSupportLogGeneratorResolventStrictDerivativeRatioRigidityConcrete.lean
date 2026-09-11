import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventTuranEqualityGeneratorEigenmodeConcrete
import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventGlobalDerivativeRatioOrderConcrete
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter
open scoped InnerProductSpace LinearPMap Topology BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

/-- On the actual one-step positive physical spectral support, the normalized
response scale is strictly increasing from derivative order `n` to `n+1`
exactly when the state is not a single spectral mode of the original partially
defined support logarithmic generator. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_lt_succ_iff_not_logGeneratorMode
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) (hv : v ≠ 0) (n : ℕ) (lambda : ℝ)
    (hlambda :
      |lambda| <
        2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta) :
    let q :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
        H N hN beta hbeta v
    iteratedDeriv (n + 1) q lambda /
        ((n + 1 : ℝ) * iteratedDeriv n q lambda) <
      iteratedDeriv (n + 2) q lambda /
        ((n + 2 : ℝ) * iteratedDeriv (n + 1) q lambda) ↔
      ¬ periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportIsSingleLogGeneratorMode
        H N hN beta hbeta v := by
  dsimp only
  constructor
  · intro hlt hmode
    have heq :=
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_eq_succ_iff_logGeneratorMode
        H N hN beta hbeta v hv n lambda hlambda).2 hmode
    exact (ne_of_lt hlt) heq
  · intro hnot
    have hle :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_mono
        H N hN beta hbeta v hv n lambda hlambda
    have hne :
        iteratedDeriv (n + 1)
            (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
              H N hN beta hbeta v) lambda /
            ((n + 1 : ℝ) * iteratedDeriv n
              (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
                H N hN beta hbeta v) lambda) ≠
          iteratedDeriv (n + 2)
            (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
              H N hN beta hbeta v) lambda /
            ((n + 2 : ℝ) * iteratedDeriv (n + 1)
              (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
                H N hN beta hbeta v) lambda) := by
      intro heq
      exact hnot
        ((periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_eq_succ_iff_logGeneratorMode
          H N hN beta hbeta v hv n lambda hlambda).1 heq)
    exact lt_of_le_of_ne hle hne

/-- Failure of the single-generator-mode rigidity alternative is equivalent to
strict increase of the normalized derivative-ratio sequence at every order. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_strictMono_iff_not_logGeneratorMode
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) (hv : v ≠ 0) (lambda : ℝ)
    (hlambda :
      |lambda| <
        2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta) :
    let q :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
        H N hN beta hbeta v
    StrictMono (fun n : ℕ =>
      iteratedDeriv (n + 1) q lambda /
        ((n + 1 : ℝ) * iteratedDeriv n q lambda)) ↔
      ¬ periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportIsSingleLogGeneratorMode
        H N hN beta hbeta v := by
  dsimp only
  constructor
  · intro hstrict hmode
    have hlt := hstrict (Nat.lt_succ_self 0)
    have heq :=
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_eq_succ_iff_logGeneratorMode
        H N hN beta hbeta v hv 0 lambda hlambda).2 hmode
    apply (ne_of_lt hlt)
    convert heq using 1 <;> norm_num
  · intro hnot
    apply strictMono_nat_of_lt_succ
    intro n
    have h :=
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_lt_succ_iff_not_logGeneratorMode
        H N hN beta hbeta v hv n lambda hlambda).2 hnot
    convert h using 1 <;> norm_num <;> ring

/-- Strict increase in derivative order is an intrinsic state property: inside
the full coercive gap it is independent of the chosen resolvent parameter. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_strictMono_parameter_independent
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) (hv : v ≠ 0)
    (lambda mu : ℝ)
    (hlambda :
      |lambda| <
        2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta)
    (hmu :
      |mu| <
        2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta) :
    let q :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
        H N hN beta hbeta v
    StrictMono (fun n : ℕ =>
      iteratedDeriv (n + 1) q lambda /
        ((n + 1 : ℝ) * iteratedDeriv n q lambda)) ↔
    StrictMono (fun n : ℕ =>
      iteratedDeriv (n + 1) q mu /
        ((n + 1 : ℝ) * iteratedDeriv n q mu)) := by
  dsimp only
  have hl :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_strictMono_iff_not_logGeneratorMode
      H N hN beta hbeta v hv lambda hlambda
  have hm :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_strictMono_iff_not_logGeneratorMode
      H N hN beta hbeta v hv mu hmu
  exact hl.trans hm.symm

end

end MathlibAnalytic
end MGAP4D
