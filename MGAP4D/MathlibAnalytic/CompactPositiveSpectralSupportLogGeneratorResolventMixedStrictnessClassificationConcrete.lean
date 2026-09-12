import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventStrictDerivativeRatioRigidityConcrete
import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventMixedStrictDerivativeRatioOrderConcrete
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter
open scoped InnerProductSpace LinearPMap Topology BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

/-- A single logarithmic-generator mode makes the normalized derivative-ratio
sequence constant in derivative order at every admissible resolvent parameter. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_eq_of_logGeneratorMode
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) (hv : v ≠ 0)
    (hmode :
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportIsSingleLogGeneratorMode
        H N hN beta hbeta v)
    (n m : ℕ) (lambda : ℝ)
    (hlambda :
      |lambda| <
        2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta) :
    let q :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
        H N hN beta hbeta v
    iteratedDeriv (n + 1) q lambda /
        ((n + 1 : ℝ) * iteratedDeriv n q lambda) =
      iteratedDeriv (m + 1) q lambda /
        ((m + 1 : ℝ) * iteratedDeriv m q lambda) := by
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
      H N hN beta hbeta v
  let R : ℕ → ℝ := fun k =>
    iteratedDeriv (k + 1) q lambda /
      ((k + 1 : ℝ) * iteratedDeriv k q lambda)
  change R n = R m
  have hadj : ∀ k : ℕ, R k = R (k + 1) := by
    intro k
    have h :=
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_eq_succ_iff_logGeneratorMode
        H N hN beta hbeta v hv k lambda hlambda).2 hmode
    change R k = R (k + 1)
    convert h using 1 <;> simp [R, q] <;> ring
  have hzero : ∀ k : ℕ, R k = R 0 := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        calc
          R (Nat.succ k) = R k := by
            simpa [Nat.succ_eq_add_one] using (hadj k).symm
          _ = R 0 := ih
  exact (hzero n).trans (hzero m).symm

/-- At a fixed admissible parameter, every strict comparison between two
different derivative orders is equivalent to failure of the single-generator-
mode rigidity alternative. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_lt_of_lt_iff_not_logGeneratorMode
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) (hv : v ≠ 0)
    {n m : ℕ} (hnm : n < m) (lambda : ℝ)
    (hlambda :
      |lambda| <
        2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta) :
    let q :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
        H N hN beta hbeta v
    iteratedDeriv (n + 1) q lambda /
        ((n + 1 : ℝ) * iteratedDeriv n q lambda) <
      iteratedDeriv (m + 1) q lambda /
        ((m + 1 : ℝ) * iteratedDeriv m q lambda) ↔
      ¬ periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportIsSingleLogGeneratorMode
        H N hN beta hbeta v := by
  dsimp only
  constructor
  · intro hlt hmode
    have heq :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_eq_of_logGeneratorMode
        H N hN beta hbeta v hv hmode n m lambda hlambda
    exact (ne_of_lt hlt) heq
  · intro hnot
    have hstrict :=
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_strictMono_iff_not_logGeneratorMode
        H N hN beta hbeta v hv lambda hlambda).2 hnot
    exact hstrict hnm

/-- Complete strictness classification for the two ordered variables
`(derivative order, resolvent parameter)`.  Under weak increase in both
coordinates, the normalized physical response is strict exactly when either
the parameter moves strictly to the right, or the derivative order moves
strictly and the state is not a single logarithmic-generator mode. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_lt_iff_parameter_lt_or_degree_lt_not_logGeneratorMode
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (v : periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupport
      H N hN beta hbeta) (hv : v ≠ 0)
    {n m : ℕ} (hnm : n ≤ m)
    {lambda mu : ℝ}
    (hlambda :
      |lambda| <
        2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta)
    (hmu :
      |mu| <
        2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
          H N hN beta hbeta)
    (hlm : lambda ≤ mu) :
    let q :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
        H N hN beta hbeta v
    iteratedDeriv (n + 1) q lambda /
        ((n + 1 : ℝ) * iteratedDeriv n q lambda) <
      iteratedDeriv (m + 1) q mu /
        ((m + 1 : ℝ) * iteratedDeriv m q mu) ↔
      lambda < mu ∨
        (n < m ∧
          ¬ periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportIsSingleLogGeneratorMode
            H N hN beta hbeta v) := by
  dsimp only
  constructor
  · intro hlt
    by_cases hlstrict : lambda < mu
    · exact Or.inl hlstrict
    · right
      have hlEq : lambda = mu := le_antisymm hlm (not_lt.mp hlstrict)
      subst mu
      have hne_nm : n ≠ m := by
        intro hEq
        subst m
        simpa using hlt
      have hnm_strict : n < m := lt_of_le_of_ne hnm hne_nm
      have hlt_same := hlt
      have hnot :=
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_lt_of_lt_iff_not_logGeneratorMode
          H N hN beta hbeta v hv hnm_strict lambda hlambda).1 hlt_same
      exact ⟨hnm_strict, hnot⟩
  · intro hcase
    rcases hcase with hlstrict | ⟨hnm_strict, hnot⟩
    · exact
        periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_lt_of_le_of_lt
          H N hN beta hbeta v hv hnm hlambda hmu hlstrict
    · have hdeg :=
        (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_lt_of_lt_iff_not_logGeneratorMode
          H N hN beta hbeta v hv hnm_strict lambda hlambda).2 hnot
      have hparam :
          iteratedDeriv (m + 1)
              (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
                H N hN beta hbeta v) lambda /
              ((m + 1 : ℝ) * iteratedDeriv m
                (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
                  H N hN beta hbeta v) lambda) ≤
            iteratedDeriv (m + 1)
              (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
                H N hN beta hbeta v) mu /
              ((m + 1 : ℝ) * iteratedDeriv m
                (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
                  H N hN beta hbeta v) mu) := by
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_le_of_le_of_le
            H N hN beta hbeta v hv (n := m) (m := m) (le_refl m)
              (abs_lt.mp hlambda) (abs_lt.mp hmu) hlm
      exact lt_of_lt_of_le hdeg hparam

end

end MathlibAnalytic
end MGAP4D
