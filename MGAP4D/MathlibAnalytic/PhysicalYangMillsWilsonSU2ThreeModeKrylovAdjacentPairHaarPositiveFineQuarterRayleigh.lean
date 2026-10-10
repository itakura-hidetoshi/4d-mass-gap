import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarQuantitativeFineRayleighHalfDepth
import Mathlib.Tactic

/-!
# P4-Q2-R: a certified quarter-energy lower bound at genuinely positive fine beta

At fixed finite H, Krylov depth r, and positive frozen Wilson coupling,
the ORIGINAL positive-fine physical normalized transfer admits a small
open window with the authentic one-link innovation error

  sqrt(gamma) * (r * B_H(beta_fine)) < ‖I_e(u_H)‖.

The triangular r/2 bound formalized in P4-Q2-Q therefore leaves a
strict margin GREATER THAN ‖I_e(u_H)‖ / 2. On that same window,

  normalized_ones_Rayleigh > (r+1) * ‖I_e(u_H)‖² / 4 > 0.

We prove (i) the inequality for every schedule satisfying the physical
budget, (ii) an open fine-coupling interval for arbitrary actual
nonnegative schedules with positive frozen beta, and (iii) a fully
constructed nonnegative schedule with positive frozen and fine betas.

This is an exact finite-volume/finite-depth result only: no
uniformity in H or r, no full-coefficient coercivity, no continuum
mass gap, no surrogate posterior/transfer, and no new axioms.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

local instance p4QuarterGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4QuarterCompact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4QuarterSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4QuarterMeasurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4QuarterBorel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4QuarterSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The genuinely physical fine-step budget from P4-Q2-O forces a
STRICT quantitative Rayleigh floor, not just nonvanishing. The
r/2 innovation-sum coefficient makes the square margin > a²/4. -/
theorem fineRightKrylovPairHaarResidualGram_ones_normalizedRayleigh_gt_quarterEnergy
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ k, 0 ≤ beta k}
    (n r : ℕ)
    (e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)))
    (hSmall :
      let H := halfExtent (n + 1)
      let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
      Real.sqrt (originalWilsonPhysicalSignedInnovationHilbertCoefficient
        H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)) *
        ((r : ℝ) *
          physicalOriginalNormalizedTransferConstantStepBetaBudget
            H (beta (n + 1))) <
        ‖physicalOriginalReceiverPosteriorInnovation
          H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) e u‖) :
    let H := halfExtent (n + 1)
    let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
    (((r + 1 : ℕ) : ℝ)) *
      (‖physicalOriginalReceiverPosteriorInnovation
        H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) e u‖ ^ 2 / 4) <
      (star (fun _ : Fin (r + 1) => (1 : ℝ)) ⬝ᵥ
        (Matrix.mulVec
          (fineRightKrylovPairHaarResidualGram
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r)
          (fun _ : Fin (r + 1) => (1 : ℝ)))) /
        (∑ j : Fin (r + 1),
          ((fun _ : Fin (r + 1) => (1 : ℝ)) j) ^ 2) := by
  classical
  let H := halfExtent (n + 1)
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let I := physicalOriginalReceiverPosteriorInnovation
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  let gamma := originalWilsonPhysicalSignedInnovationHilbertCoefficient
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  let B := physicalOriginalNormalizedTransferConstantStepBetaBudget
    H (beta (n + 1))
  let x : ℝ := ‖I e u‖
  let y : ℝ := ((r : ℝ) / 2) * (Real.sqrt gamma * B)
  have hPhysical : Real.sqrt gamma * ((r : ℝ) * B) < x := hSmall
  have hy : y = (Real.sqrt gamma * ((r : ℝ) * B)) / 2 := by
    dsimp [y]
    ring
  have hHalfMargin : x / 2 < x - y := by
    rw [hy]
    linarith
  have hNorm : 0 ≤ x := norm_nonneg _
  have hMargin : 0 ≤ x - y := by linarith
  have hLower :
      (((r + 1 : ℕ) : ℝ)) * (x - y) ^ 2 ≤
        (star (fun _ : Fin (r + 1) => (1 : ℝ)) ⬝ᵥ
          (Matrix.mulVec
            (fineRightKrylovPairHaarResidualGram
              (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
              n r)
            (fun _ : Fin (r + 1) => (1 : ℝ)))) /
          (∑ j : Fin (r + 1),
            ((fun _ : Fin (r + 1) => (1 : ℝ)) j) ^ 2) :=
    fineRightKrylovPairHaarResidualGram_ones_normalizedRayleigh_ge_halfDepth
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e hMargin
  have hPositiveFactor :
      0 < ((x - y) - x / 2) * ((x - y) + x / 2) := by
    apply mul_pos
    · linarith
    · linarith
  have hSquare : x ^ 2 / 4 < (x - y) ^ 2 := by
    nlinarith [hPositiveFactor]
  have hN : 0 < (((r + 1 : ℕ) : ℝ)) := by positivity
  change (((r + 1 : ℕ) : ℝ)) * (x ^ 2 / 4) < _
  exact (mul_lt_mul_of_pos_left hSquare hN).trans hLower

/-- The quarter-energy bound holds throughout a truly open,
nonempty fine-coupling interval for ANY actual nonnegative Wilson
schedule with positive frozen beta. The witness e and the interval
may depend on H, r and the frozen physical coupling, but not on
the fine schedule outside the selected adjacent scales. -/
theorem fineRightKrylovPairHaarResidualGram_exists_quarterEnergy_fineWindow
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ k, 0 ≤ beta k}
    (n r : ℕ) (hFrozen : 0 < beta n) :
    ∃ (e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)))
      (delta : ℝ), 0 < delta ∧
        0 < ‖physicalOriginalReceiverPosteriorInnovation
          (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
          (beta n) (hbeta n) e
          (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector
            (halfExtent (n + 1)) 2)‖ ∧
        (beta (n + 1) < delta →
          (((r + 1 : ℕ) : ℝ)) *
            (‖physicalOriginalReceiverPosteriorInnovation
              (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
              (beta n) (hbeta n) e
              (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector
                (halfExtent (n + 1)) 2)‖ ^ 2 / 4) <
            (star (fun _ : Fin (r + 1) => (1 : ℝ)) ⬝ᵥ
              (Matrix.mulVec
                (fineRightKrylovPairHaarResidualGram
                  (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
                  n r)
                (fun _ : Fin (r + 1) => (1 : ℝ)))) /
              (∑ j : Fin (r + 1),
                ((fun _ : Fin (r + 1) => (1 : ℝ)) j) ^ 2)) := by
  let H := halfExtent (n + 1)
  obtain ⟨e, he⟩ :=
    physicalOriginalUnitReceiver_exists_positive_link_norm_SU2
      H (beta n) hFrozen
  have hPos :
      0 < ‖physicalOriginalReceiverPosteriorInnovation
        H 2 specialUnitaryTwoWilsonRankPositive
        (beta n) (hbeta n) e
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)‖ := he
  obtain ⟨delta, hdelta, hwindow⟩ :=
    physicalOriginalNormalizedTransferConstantStepBetaBudget_exists_window
      H r
      (Real.sqrt (originalWilsonPhysicalSignedInnovationHilbertCoefficient
        H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)))
      (‖physicalOriginalReceiverPosteriorInnovation
        H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) e
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)‖)
      hPos
  refine ⟨e, delta, hdelta, hPos, ?_⟩
  intro hFine
  apply fineRightKrylovPairHaarResidualGram_ones_normalizedRayleigh_gt_quarterEnergy
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r e
  exact hwindow (beta (n + 1)) (hbeta (n + 1)) hFine

/-- Fully construct a nonnegative Wilson coupling schedule, with
frozen beta n = b > 0 and genuinely positive beta (n+1) = delta/2,
and a genuine original frozen-link witness for the strict
quarter-energy normalized Rayleigh floor. All other betas are zero. -/
theorem fineRightKrylovPairHaarResidualGram_exists_positiveFine_quarterEnergy_schedule
    (halfExtent : ℕ → ℕ) (n r : ℕ)
    (frozen : ℝ) (hFrozen : 0 < frozen) :
    ∃ (beta : ℕ → ℝ) (hbeta : ∀ k, 0 ≤ beta k)
      (e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1))),
        beta n = frozen ∧ 0 < beta (n + 1) ∧
        (∀ k, k ≠ n → k ≠ n + 1 → beta k = 0) ∧
        0 < ‖physicalOriginalReceiverPosteriorInnovation
          (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
          (beta n) (hbeta n) e
          (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector
            (halfExtent (n + 1)) 2)‖ ∧
        (((r + 1 : ℕ) : ℝ)) *
          (‖physicalOriginalReceiverPosteriorInnovation
            (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
            (beta n) (hbeta n) e
            (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector
              (halfExtent (n + 1)) 2)‖ ^ 2 / 4) <
          (star (fun _ : Fin (r + 1) => (1 : ℝ)) ⬝ᵥ
            (Matrix.mulVec
              (fineRightKrylovPairHaarResidualGram
                (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
                n r)
              (fun _ : Fin (r + 1) => (1 : ℝ)))) /
            (∑ j : Fin (r + 1),
              ((fun _ : Fin (r + 1) => (1 : ℝ)) j) ^ 2) := by
  classical
  let H := halfExtent (n + 1)
  obtain ⟨e, he⟩ :=
    physicalOriginalUnitReceiver_exists_positive_link_norm_SU2
      H frozen hFrozen
  obtain ⟨delta, hdelta, hwindow⟩ :=
    physicalOriginalNormalizedTransferConstantStepBetaBudget_exists_window
      H r
      (Real.sqrt (originalWilsonPhysicalSignedInnovationHilbertCoefficient
        H 2 specialUnitaryTwoWilsonRankPositive frozen (le_of_lt hFrozen)))
      (‖physicalOriginalReceiverPosteriorInnovation
        H 2 specialUnitaryTwoWilsonRankPositive frozen (le_of_lt hFrozen) e
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)‖)
      he
  let fine : ℝ := delta / 2
  have hFinePos : 0 < fine := by
    dsimp [fine]
    linarith
  have hFineSmall : fine < delta := by
    dsimp [fine]
    linarith
  let beta : ℕ → ℝ := fun k =>
    if k = n then frozen else if k = n + 1 then fine else 0
  have hbeta : ∀ k : ℕ, 0 ≤ beta k := by
    intro k
    by_cases hk : k = n
    · simp [beta, hk, le_of_lt hFrozen]
    · by_cases hk' : k = n + 1
      · change 0 ≤ if k = n then frozen else if k = n + 1 then fine else 0
        rw [if_neg hk, if_pos hk']
        exact le_of_lt hFinePos
      · simp [beta, hk, hk']
  have hFrozenAt : beta n = frozen := by simp [beta]
  have hFineAt : beta (n + 1) = fine := by simp [beta]
  have hAway : ∀ k, k ≠ n → k ≠ n + 1 → beta k = 0 := by
    intro k hk hk'
    simp [beta, hk, hk']
  have hPosAt :
      0 < ‖physicalOriginalReceiverPosteriorInnovation
        H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) e
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)‖ := by
    simpa only [hFrozenAt] using he
  have hSmall :
      Real.sqrt (originalWilsonPhysicalSignedInnovationHilbertCoefficient
        H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)) *
        ((r : ℝ) *
          physicalOriginalNormalizedTransferConstantStepBetaBudget
            H (beta (n + 1))) <
        ‖physicalOriginalReceiverPosteriorInnovation
          H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) e
          (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)‖ := by
    simpa only [hFrozenAt, hFineAt] using
      (hwindow fine hFinePos.le hFineSmall)
  have hQuant :
      (((r + 1 : ℕ) : ℝ)) *
        (‖physicalOriginalReceiverPosteriorInnovation
          H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) e
          (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)‖ ^ 2 / 4) <
        (star (fun _ : Fin (r + 1) => (1 : ℝ)) ⬝ᵥ
          (Matrix.mulVec
            (fineRightKrylovPairHaarResidualGram
              (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
              n r)
            (fun _ : Fin (r + 1) => (1 : ℝ)))) /
          (∑ j : Fin (r + 1),
            ((fun _ : Fin (r + 1) => (1 : ℝ)) j) ^ 2) :=
    fineRightKrylovPairHaarResidualGram_ones_normalizedRayleigh_gt_quarterEnergy
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e hSmall
  exact ⟨beta, hbeta, e, hFrozenAt, by simpa only [hFineAt] using hFinePos,
    hAway, hPosAt, hQuant⟩

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
