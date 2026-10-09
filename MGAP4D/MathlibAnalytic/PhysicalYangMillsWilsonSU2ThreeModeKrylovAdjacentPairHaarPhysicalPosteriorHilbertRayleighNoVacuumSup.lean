import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPhysicalMeanOriginalPosteriorL2Energy
import Mathlib.Tactic

/-!
# P4-Q2-C: authentic uncentered right-Krylov Gram posterior-Hilbert Rayleigh

PR #5333 proves actual original Wilson one-link resampling energy of the
SIGNED normalized physical mean M_f is at most
  (lambda_beta^(-1) * (exp(8 beta)^2 - 1) * ||f||_HaarL2)^2,
without the inverse-vacuum SUP norm.

The original right receiver is the TRUE product W_beta * M_f.
The preexisting physical posterior Leibniz inequality and the verified
physical half-density Harnack estimate therefore yield

 E_e(W*M_f)
   <= 2 ||W||_sup^2 (lambda^-1 D ||f||_2)^2
      + 2 ||M_f||_sup^2 ((exp(8 beta)-1) ||W||_sup)^2.

Specialize to the ORIGINAL uncentered signed fine-right Krylov source
sum_j a_j R_{n,j}, evolved at beta(n+1), received at frozen beta(n).
Finally use the exact original Gram/resampling Rayleigh equality from
PR #5324 to obtain a concrete physical Hilbert Rayleigh envelope.

The inverse-vacuum SUP has been eliminated from the mean *posterior*
energy term; finite-volume dependence of W, M, lambda, and link count
remains explicit. Q2-C/D volume uniformity and continuum mass gap
are NOT proved. No replacement posterior, Dobrushin or novel axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

local instance p4PostHilbertTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4PostHilbertCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4PostHilbertSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4PostHilbertMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4PostHilbertBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4PostHilbertLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Exact physical receiver two-factor bound on TRUE original Wilson
posterior resampling energy, with the signed physical mean controlled
via the genuine joint-L² vacuum cancellation, not inverse-vacuum sup. -/
theorem normalizedPhysicalOneSlabJointReceiverProductBCF_posteriorEnergy_le_signedHilbert_noVacuumSup
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    let W := normalizedPhysicalOneSlabJointHalfDensityWeightBCF H N hN beta hbeta
    let M := normalizedPhysicalOneSlabVacuumMeanJointBCF H N hN beta hbeta f
    posteriorResamplingEnergy H N hN beta hbeta e
      (normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f) ≤
      (2 * ‖W‖ ^ 2) *
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖⁻¹ *
          ((Real.exp (8 * beta)) ^ 2 - 1) * ‖f‖) ^ 2 +
      (2 * ‖M‖ ^ 2) *
        ((Real.exp (8 * beta) - 1) * ‖W‖) ^ 2 := by
  let W := normalizedPhysicalOneSlabJointHalfDensityWeightBCF H N hN beta hbeta
  let M := normalizedPhysicalOneSlabVacuumMeanJointBCF H N hN beta hbeta f
  let c : ℝ := (Real.exp (8 * beta) - 1) * ‖W‖
  have hMean :=
    normalizedPhysicalOneSlabVacuumMeanJointBCF_posteriorResamplingEnergy_le_signedHilbert_noVacuumSup
      H N hN beta hbeta f e
  have hWeight :
      posteriorResamplingEnergy H N hN beta hbeta e W ≤ c ^ 2 := by
    apply originalWilsonPosteriorResamplingEnergy_le_constantLinkOscillation
      H N hN beta hbeta e W c
    intro z g
    exact normalizedPhysicalOneSlabJointHalfDensityWeightBCF_rightLinkDifference_abs_le
      H N hN beta hbeta e z g
  have hSplit :=
    normalizedPhysicalOneSlabJointReceiverProductBCF_resamplingEnergy_le
      H N hN beta hbeta f e
  have hWNonneg : 0 ≤ 2 * ‖W‖ ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg _)
  have hMNonneg : 0 ≤ 2 * ‖M‖ ^ 2 :=
    mul_nonneg (by norm_num) (sq_nonneg _)
  change
    posteriorResamplingEnergy H N hN beta hbeta e
      (normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f) ≤
    (2 * ‖W‖ ^ 2) *
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖⁻¹ *
        ((Real.exp (8 * beta)) ^ 2 - 1) * ‖f‖) ^ 2 +
    (2 * ‖M‖ ^ 2) * c ^ 2
  exact hSplit.trans (add_le_add
    (mul_le_mul_of_nonneg_left hMean hWNonneg)
    (mul_le_mul_of_nonneg_left hWeight hMNonneg))

/-- The genuine original fine-right Krylov source is used in exactly
the same frozen physical transfer as in PR #5324. The resulting link
bound is NOT an abstract fitted right-link oscillation coefficient. -/
noncomputable def fineRightKrylovOriginalPhysicalPosteriorHilbertEnergyEnvelope
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ) : ℝ :=
  let H := halfExtent (n + 1)
  let W := normalizedPhysicalOneSlabJointHalfDensityWeightBCF
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  let M := fineRightKrylovOriginalVacuumMeanJointBCF
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  let F := fineRightKrylovOriginalSignedPhysicalSource
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  (2 * ‖W‖ ^ 2) *
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)‖⁻¹ *
        ((Real.exp (8 * beta n)) ^ 2 - 1) * ‖F‖) ^ 2 +
    (2 * ‖M‖ ^ 2) *
      ((Real.exp (8 * beta n) - 1) * ‖W‖) ^ 2

theorem fineRightKrylovOriginalPhysicalJointObservable_posteriorEnergy_le_signedHilbertEnvelope
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ)
    (e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1))) :
    posteriorResamplingEnergy (halfExtent (n + 1)) 2
      specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) e
      (fineRightKrylovOriginalPhysicalJointObservable
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a) ≤
      fineRightKrylovOriginalPhysicalPosteriorHilbertEnergyEnvelope
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a := by
  simpa only [fineRightKrylovOriginalPhysicalPosteriorHilbertEnergyEnvelope,
    fineRightKrylovOriginalPhysicalJointObservable,
    fineRightKrylovOriginalVacuumMeanJointBCF,
    fineRightKrylovOriginalSignedPhysicalSource] using
    (normalizedPhysicalOneSlabJointReceiverProductBCF_posteriorEnergy_le_signedHilbert_noVacuumSup
      (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
      (beta n) (hbeta n)
      (∑ j : Fin (r + 1), a j •
        physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n (j : ℕ)) e)

/-- TRUE uncentered original fine-right Gram Rayleigh estimate via
exact signed resampling polarization. No inverse-vacuum sup in the
physical mean's posterior energy term, and no artificial source
locality or original-Wilson posterior replacement. -/
theorem fineRightKrylovPairHaarResidualGram_rayleigh_le_physicalPosteriorHilbert_noVacuumSup
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ) :
    star a ⬝ᵥ (Matrix.mulVec
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a) ≤
      (1 / 2 : ℝ) *
        ∑ _e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)),
          fineRightKrylovOriginalPhysicalPosteriorHilbertEnergyEnvelope
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r a := by
  let H := halfExtent (n + 1)
  let O := fineRightKrylovOriginalPhysicalJointObservable
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r a
  have hRay :
      star a ⬝ᵥ (Matrix.mulVec
        (fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) a) =
      (1 / 2 : ℝ) *
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          posteriorResamplingEnergy H 2 specialUnitaryTwoWilsonRankPositive
            (beta n) (hbeta n) e O := by
    simpa only [H, O, fineRightKrylovOriginalPhysicalJointObservable] using
      (fineRightKrylovPairHaarResidualGram_rayleigh_eq_half_originalResamplingEnergy
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r a)
  have hOne (e : PeriodicHypercubicEvenSpatialSliceLink H) :
      posteriorResamplingEnergy H 2 specialUnitaryTwoWilsonRankPositive
        (beta n) (hbeta n) e O ≤
      fineRightKrylovOriginalPhysicalPosteriorHilbertEnergyEnvelope
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a :=
    fineRightKrylovOriginalPhysicalJointObservable_posteriorEnergy_le_signedHilbertEnvelope
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a e
  calc
    star a ⬝ᵥ (Matrix.mulVec
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a) =
      (1 / 2 : ℝ) *
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          posteriorResamplingEnergy H 2 specialUnitaryTwoWilsonRankPositive
            (beta n) (hbeta n) e O := hRay
    _ ≤ (1 / 2 : ℝ) *
        ∑ _e : PeriodicHypercubicEvenSpatialSliceLink H,
          fineRightKrylovOriginalPhysicalPosteriorHilbertEnergyEnvelope
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r a := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro e _he
        exact hOne e
      · norm_num

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
