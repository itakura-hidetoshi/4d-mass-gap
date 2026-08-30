import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportDerivativeRatioEffectiveEnergyGapConcrete
import MGAP4D.MathlibAnalytic.CompactPositiveSpectralSupportLogGeneratorResolventStrictDerivativeRatioRigidityConcrete
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Module End Filter
open scoped InnerProductSpace LinearPMap Topology BigOperators

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000

/-- At fixed admissible resolvent parameter, the effective logarithmic energies
reconstructed from the factorial-normalized derivative ratios are antitone in
derivative order.

Writing `R_n(lambda)` for the normalized derivative ratio and
`rho_n(lambda) = lambda + R_n(lambda)⁻¹`, the previously proved monotonicity of
`R_n` reverses under inversion because every `R_n` is strictly positive. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_effectiveEnergy_antitone
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
    Antitone (fun n : ℕ =>
      lambda +
        (iteratedDeriv (n + 1) q lambda /
          ((n + 1 : ℝ) * iteratedDeriv n q lambda))⁻¹) := by
  dsimp only
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
      H N hN beta hbeta v
  let R := fun n : ℕ =>
    iteratedDeriv (n + 1) q lambda /
      ((n + 1 : ℝ) * iteratedDeriv n q lambda)
  change Antitone (fun n : ℕ => lambda + (R n)⁻¹)
  intro n m hnm
  have hn :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_quantitativeEffectiveEnergyGap
      H N hN beta hbeta v hv n lambda hlambda
  have hm :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_quantitativeEffectiveEnergyGap
      H N hN beta hbeta v hv m lambda hlambda
  dsimp only at hn hm
  have hRnPos : 0 < R n := by
    simpa [R, q] using hn.1
  have hRmPos : 0 < R m := by
    simpa [R, q] using hm.1
  have hRatio :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_le_of_le
      H N hN beta hbeta v hv lambda hlambda hnm
  have hRatio' : R n ≤ R m := by
    simpa [R, q] using hRatio
  have hInv : (R m)⁻¹ ≤ (R n)⁻¹ := by
    have hOne : 1 / R m ≤ 1 / R n :=
      one_div_le_one_div_of_le hRnPos hRatio'
    simpa [one_div] using hOne
  exact add_le_add_left hInv lambda

/-- Every effective energy in the derivative hierarchy remains above the
finite-volume coercive gap, uniformly in derivative order. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_effectiveEnergy_gapLowerBound
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
    let c :=
      2 * periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceFiniteVolumeDecayRate
        H N hN beta hbeta
    ∀ n : ℕ,
      c ≤ lambda +
        (iteratedDeriv (n + 1) q lambda /
          ((n + 1 : ℝ) * iteratedDeriv n q lambda))⁻¹ := by
  dsimp only
  intro n
  have h :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_quantitativeEffectiveEnergyGap
      H N hN beta hbeta v hv n lambda hlambda
  dsimp only at h
  exact h.2.2.1

/-- Strict decrease of two adjacent effective energies is exactly failure of
the single-log-generator-mode rigidity locus. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_effectiveEnergy_succ_lt_iff_not_logGeneratorMode
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
    lambda +
        (iteratedDeriv (n + 2) q lambda /
          ((n + 2 : ℝ) * iteratedDeriv (n + 1) q lambda))⁻¹ <
      lambda +
        (iteratedDeriv (n + 1) q lambda /
          ((n + 1 : ℝ) * iteratedDeriv n q lambda))⁻¹ ↔
      ¬ periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportIsSingleLogGeneratorMode
        H N hN beta hbeta v := by
  dsimp only
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
      H N hN beta hbeta v
  let Rn := iteratedDeriv (n + 1) q lambda /
    ((n + 1 : ℝ) * iteratedDeriv n q lambda)
  let Rn1 := iteratedDeriv (n + 2) q lambda /
    ((n + 2 : ℝ) * iteratedDeriv (n + 1) q lambda)
  have hn :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_quantitativeEffectiveEnergyGap
      H N hN beta hbeta v hv n lambda hlambda
  have hn1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_quantitativeEffectiveEnergyGap
      H N hN beta hbeta v hv (n + 1) lambda hlambda
  dsimp only at hn hn1
  have hRnPos : 0 < Rn := by
    simpa [Rn, q] using hn.1
  have hRn1Pos : 0 < Rn1 := by
    simpa [Rn1, q] using hn1.1
  have hRatioIff :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_lt_succ_iff_not_logGeneratorMode
      H N hN beta hbeta v hv n lambda hlambda
  change lambda + Rn1⁻¹ < lambda + Rn⁻¹ ↔
    ¬ periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportIsSingleLogGeneratorMode
      H N hN beta hbeta v
  constructor
  · intro hEnergy
    have hInv : Rn1⁻¹ < Rn⁻¹ := by linarith
    have hle :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_mono
        H N hN beta hbeta v hv n lambda hlambda
    have hle' : Rn ≤ Rn1 := by
      simpa [Rn, Rn1, q] using hle
    have hne : Rn ≠ Rn1 := by
      intro heq
      rw [heq] at hInv
      exact (lt_irrefl _ hInv)
    have hlt : Rn < Rn1 := lt_of_le_of_ne hle' hne
    exact hRatioIff.1 (by simpa [Rn, Rn1, q] using hlt)
  · intro hnot
    have hltRaw := hRatioIff.2 hnot
    have hlt : Rn < Rn1 := by
      simpa [Rn, Rn1, q] using hltRaw
    have hOne : 1 / Rn1 < 1 / Rn :=
      one_div_lt_one_div_of_lt hRnPos hlt
    have hInv : Rn1⁻¹ < Rn⁻¹ := by
      simpa [one_div] using hOne
    linarith

/-- The whole effective-energy hierarchy is strictly decreasing exactly off the
single logarithmic-generator-mode locus. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_effectiveEnergy_strictAnti_iff_not_logGeneratorMode
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
    StrictAnti (fun n : ℕ =>
      lambda +
        (iteratedDeriv (n + 1) q lambda /
          ((n + 1 : ℝ) * iteratedDeriv n q lambda))⁻¹) ↔
      ¬ periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportIsSingleLogGeneratorMode
        H N hN beta hbeta v := by
  dsimp only
  let q :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude
      H N hN beta hbeta v
  let rho := fun n : ℕ =>
    lambda +
      (iteratedDeriv (n + 1) q lambda /
        ((n + 1 : ℝ) * iteratedDeriv n q lambda))⁻¹
  change StrictAnti rho ↔
    ¬ periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportIsSingleLogGeneratorMode
      H N hN beta hbeta v
  constructor
  · intro hanti
    have h01 := hanti (Nat.lt_succ_self 0)
    have hiff :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_effectiveEnergy_succ_lt_iff_not_logGeneratorMode
        H N hN beta hbeta v hv 0 lambda hlambda
    exact hiff.1 (by simpa [rho, q] using h01)
  · intro hnot
    have hRatioStrict :=
      (periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_strictMono_iff_not_logGeneratorMode
        H N hN beta hbeta v hv lambda hlambda).2 hnot
    intro n m hnm
    let Rn := iteratedDeriv (n + 1) q lambda /
      ((n + 1 : ℝ) * iteratedDeriv n q lambda)
    let Rm := iteratedDeriv (m + 1) q lambda /
      ((m + 1 : ℝ) * iteratedDeriv m q lambda)
    have hn :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_quantitativeEffectiveEnergyGap
        H N hN beta hbeta v hv n lambda hlambda
    have hm :=
      periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_derivativeRatio_quantitativeEffectiveEnergyGap
        H N hN beta hbeta v hv m lambda hlambda
    dsimp only at hn hm
    have hRnPos : 0 < Rn := by
      simpa [Rn, q] using hn.1
    have hRmPos : 0 < Rm := by
      simpa [Rm, q] using hm.1
    have hltRaw := hRatioStrict hnm
    have hlt : Rn < Rm := by
      simpa [Rn, Rm, q] using hltRaw
    have hOne : 1 / Rm < 1 / Rn :=
      one_div_lt_one_div_of_lt hRnPos hlt
    have hInv : Rm⁻¹ < Rn⁻¹ := by
      simpa [one_div] using hOne
    change rho m < rho n
    dsimp [rho, Rn, Rm]
    simpa [q] using (add_lt_add_left hInv lambda)

/-- Strict effective-energy decrease is intrinsic to the state and therefore
independent of which resolvent parameter in the coercive gap is used. -/
theorem periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_effectiveEnergy_strictAnti_parameter_independent
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
    StrictAnti (fun n : ℕ =>
      lambda +
        (iteratedDeriv (n + 1) q lambda /
          ((n + 1 : ℝ) * iteratedDeriv n q lambda))⁻¹) ↔
    StrictAnti (fun n : ℕ =>
      mu +
        (iteratedDeriv (n + 1) q mu /
          ((n + 1 : ℝ) * iteratedDeriv n q mu))⁻¹) := by
  dsimp only
  have hl :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_effectiveEnergy_strictAnti_iff_not_logGeneratorMode
      H N hN beta hbeta v hv lambda hlambda
  have hm :=
    periodicHypercubicEvenSpecialUnitaryPhysicalExcitationPairHilbertSectorTransferOneSpectralSupportResolventQuadraticAmplitude_effectiveEnergy_strictAnti_iff_not_logGeneratorMode
      H N hN beta hbeta v hv mu hmu
  exact hl.trans hm.symm

end

end MathlibAnalytic
end MGAP4D