import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPositiveFineOpenWindow
import Mathlib.Tactic

/-!
# P4-Q2-P: construct an actual positive-fine, positive-frozen Wilson beta profile

P4-Q2-O produces a genuinely positive fine-coupling interval at
each fixed finite Wilson spatial extent H and finite Krylov depth r,
using physical normalized-transfer continuity and a genuine frozen
Wilson spatial-link innovation.

This file makes the parameter choice concrete. Given any positive
frozen Wilson coupling b and any adjacent depth n, choose t=delta/2,
and define the ENTIRE nonnegative coupling schedule beta(k) to equal
b at k=n, to equal positive t at k=n+1, and to equal zero elsewhere.
Both couplings are therefore distinct and explicitly identified.

The genuine ORIGINAL Wilson right posterior Gram of this physical
schedule has strictly positive all-one Rayleigh and strictly positive
normalized all-one Rayleigh at the selected finite depth. These are
existence results for a finite-dimensional physical schedule, not
a volume-uniform or depth-uniform estimate or a continuum mass-gap claim.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

namespace GroundStatePosteriorJoint

/-- A fully constructed nonnegative beta schedule with arbitrary
positive frozen coupling and strictly positive fine coupling has
strictly positive ALL-ONE Rayleigh for the ACTUAL Wilson posterior
right Gram at every prescribed finite depth. -/
theorem fineRightKrylovPairHaarResidualGram_exists_positiveFine_schedule
    (halfExtent : ℕ → ℕ) (n r : ℕ)
    (frozen : ℝ) (hFrozen : 0 < frozen) :
    ∃ (beta : ℕ → ℝ) (hbeta : ∀ k, 0 ≤ beta k),
      beta n = frozen ∧ 0 < beta (n + 1) ∧
        0 < star (fun _ : Fin (r + 1) => (1 : ℝ)) ⬝ᵥ
          (Matrix.mulVec
            (fineRightKrylovPairHaarResidualGram
              (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
              n r)
            (fun _ : Fin (r + 1) => (1 : ℝ))) := by
  classical
  let H := halfExtent (n + 1)
  obtain ⟨e, delta, hdelta, hwindow⟩ :=
    physicalOriginalUnitReceiver_exists_positiveFineWindow
      H r frozen hFrozen
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
  have hFrozenAt : beta n = frozen := by
    simp [beta]
  have hFineAt : beta (n + 1) = fine := by
    simp [beta]
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
  have hRayleigh :
      0 < star (fun _ : Fin (r + 1) => (1 : ℝ)) ⬝ᵥ
        (Matrix.mulVec
          (fineRightKrylovPairHaarResidualGram
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r)
          (fun _ : Fin (r + 1) => (1 : ℝ))) :=
    fineRightKrylovPairHaarResidualGram_ones_rayleigh_pos_of_fineBudget_small
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e hSmall
  refine ⟨beta, hbeta, hFrozenAt, ?_, hRayleigh⟩
  simpa only [hFineAt] using hFinePos

/-- The same genuinely positive-fine Wilson coupling profile also
has STRICTLY POSITIVE normalized all-one Rayleigh quotient; the
denominator is the exact nonzero coefficient norm r+1. -/
theorem fineRightKrylovPairHaarResidualGram_exists_positiveFine_normalizedRayleigh
    (halfExtent : ℕ → ℕ) (n r : ℕ)
    (frozen : ℝ) (hFrozen : 0 < frozen) :
    ∃ (beta : ℕ → ℝ) (hbeta : ∀ k, 0 ≤ beta k),
      beta n = frozen ∧ 0 < beta (n + 1) ∧
        0 <
          (star (fun _ : Fin (r + 1) => (1 : ℝ)) ⬝ᵥ
            (Matrix.mulVec
              (fineRightKrylovPairHaarResidualGram
                (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
                n r)
              (fun _ : Fin (r + 1) => (1 : ℝ)))) /
            (∑ j : Fin (r + 1),
              ((fun _ : Fin (r + 1) => (1 : ℝ)) j) ^ 2) := by
  obtain ⟨beta, hbeta, hFrozenAt, hFinePos, hRayleigh⟩ :=
    fineRightKrylovPairHaarResidualGram_exists_positiveFine_schedule
      halfExtent n r frozen hFrozen
  refine ⟨beta, hbeta, hFrozenAt, hFinePos, ?_⟩
  rw [fineRightKrylov_ones_coeff_sq_norm_eq]
  exact div_pos hRayleigh (by positivity)

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
