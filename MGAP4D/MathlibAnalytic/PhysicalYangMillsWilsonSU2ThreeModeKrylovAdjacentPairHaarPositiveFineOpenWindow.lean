import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPositiveFineOneRayleighStability
import Mathlib.Tactic

/-!
# P4-Q2-O: a genuine positive-fine-coupling window at each finite depth

The certified original finite-volume Wilson normalized-transfer
constant-step budget is

  B_H(t) = 2 * exp(t * A_H) * A_H * t,

with the genuine finite-H action budget A_H. Its defining kernel
minorization is always positive; thus the exact physical B_H
is continuous, and B_H(0)=0.

At fixed finite H, r and positive frozen coupling, P4-Q2-M supplies
a genuine original Wilson spatial-link innovation of positive norm.
The continuous physical fine-step budget is therefore sufficiently
small throughout a positive half-interval (0, delta). The P4-Q2-N
finite-depth Hilbert noncancellation theorem then yields strictly
positive all-one Rayleigh of the ORIGINAL posterior right Krylov Gram
whenever the fine beta lies in that interval.

This does not assert all-depth, volume-uniform, or continuum control.
No Dobrushin, substitute joint law, or new axiom is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

/-- Continuity of the already-defined ORIGINAL normalized Wilson
constant-step beta budget, not continuity of a surrogate transfer. -/
theorem physicalOriginalNormalizedTransferConstantStepBetaBudget_continuous
    (H : ℕ) :
    Continuous (fun t : ℝ =>
      GroundStatePosteriorJoint.physicalOriginalNormalizedTransferConstantStepBetaBudget H t) := by
  unfold GroundStatePosteriorJoint.physicalOriginalNormalizedTransferConstantStepBetaBudget
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
  fun_prop

/-- Genuine physical fine-step budget is continuous at zero and has
zero value there. -/
theorem physicalOriginalNormalizedTransferConstantStepBetaBudget_tendsto_zero
    (H : ℕ) :
    Tendsto (fun t : ℝ =>
      GroundStatePosteriorJoint.physicalOriginalNormalizedTransferConstantStepBetaBudget H t)
      (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  have h := (physicalOriginalNormalizedTransferConstantStepBetaBudget_continuous H).continuousAt
  simpa only [GroundStatePosteriorJoint.physicalOriginalNormalizedTransferConstantStepBetaBudget_zero] using
    h.tendsto

/-- A general exact finite-volume small-step window follows from
continuity, without presupposing a volume-independent floor. The
constant K may be any real scalar; the radius is strictly positive. -/
theorem physicalOriginalNormalizedTransferConstantStepBetaBudget_exists_window
    (H r : ℕ) (K radius : ℝ) (hRadius : 0 < radius) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ t : ℝ, 0 ≤ t → t < delta →
        K * ((r : ℝ) *
          GroundStatePosteriorJoint.physicalOriginalNormalizedTransferConstantStepBetaBudget H t) <
          radius := by
  let f : ℝ → ℝ := fun t =>
    K * ((r : ℝ) *
      GroundStatePosteriorJoint.physicalOriginalNormalizedTransferConstantStepBetaBudget H t)
  have hf : Continuous f := by
    dsimp [f]
    exact continuous_const.mul
      (continuous_const.mul
        (physicalOriginalNormalizedTransferConstantStepBetaBudget_continuous H))
  have hf0 : f 0 = 0 := by
    simp [f]
  obtain ⟨delta, hDelta, hnear⟩ :=
    (Metric.continuousAt_iff.mp hf.continuousAt) radius hRadius
  refine ⟨delta, hDelta, ?_⟩
  intro t ht hlt
  have hdist : dist t (0 : ℝ) < delta := by
    simpa [Real.dist_eq, abs_of_nonneg ht] using hlt
  have herror := hnear hdist
  rw [hf0] at herror
  have habs : |f t| < radius := by
    simpa [Real.dist_eq] using herror
  exact lt_of_le_of_lt (le_abs_self (f t)) habs

local instance p4FineOpenGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4FineOpenCompact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4FineOpenSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4FineOpenMeasurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4FineOpenBorel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4FineOpenLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Every positive frozen physical Wilson coupling supplies a
strictly positive open one-sided fine-coupling radius in which
the ORIGINAL finite-depth Hilbert innovation bound is valid. -/
theorem physicalOriginalUnitReceiver_exists_positiveFineWindow
    (H r : ℕ) (frozen : ℝ) (hFrozen : 0 < frozen) :
    ∃ (e : PeriodicHypercubicEvenSpatialSliceLink H)
      (delta : ℝ), 0 < delta ∧
      ∀ t : ℝ, 0 ≤ t → t < delta →
        Real.sqrt (originalWilsonPhysicalSignedInnovationHilbertCoefficient
          H 2 specialUnitaryTwoWilsonRankPositive frozen (le_of_lt hFrozen)) *
          ((r : ℝ) *
            physicalOriginalNormalizedTransferConstantStepBetaBudget H t) <
          ‖physicalOriginalReceiverPosteriorInnovation H 2
            specialUnitaryTwoWilsonRankPositive frozen (le_of_lt hFrozen) e
            (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)‖ := by
  obtain ⟨e, he⟩ :=
    physicalOriginalUnitReceiver_exists_positive_link_norm_SU2 H frozen hFrozen
  obtain ⟨delta, hdelta, hsmall⟩ :=
    physicalOriginalNormalizedTransferConstantStepBetaBudget_exists_window
      H r
      (Real.sqrt (originalWilsonPhysicalSignedInnovationHilbertCoefficient
        H 2 specialUnitaryTwoWilsonRankPositive frozen (le_of_lt hFrozen)))
      (‖physicalOriginalReceiverPosteriorInnovation H 2
        specialUnitaryTwoWilsonRankPositive frozen (le_of_lt hFrozen) e
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)‖)
      he
  exact ⟨e, delta, hdelta, hsmall⟩

/-- The open fine interval really contains a STRICTLY POSITIVE
fine coupling, for any finite volume and positive frozen coupling. -/
theorem physicalOriginalUnitReceiver_exists_strictPositiveFineBeta_in_window
    (H r : ℕ) (frozen : ℝ) (hFrozen : 0 < frozen) :
    ∃ (e : PeriodicHypercubicEvenSpatialSliceLink H) (t : ℝ),
      0 < t ∧
      Real.sqrt (originalWilsonPhysicalSignedInnovationHilbertCoefficient
        H 2 specialUnitaryTwoWilsonRankPositive frozen (le_of_lt hFrozen)) *
        ((r : ℝ) * physicalOriginalNormalizedTransferConstantStepBetaBudget H t) <
        ‖physicalOriginalReceiverPosteriorInnovation H 2
          specialUnitaryTwoWilsonRankPositive frozen (le_of_lt hFrozen) e
          (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)‖ := by
  obtain ⟨e, delta, hdelta, hwindow⟩ :=
    physicalOriginalUnitReceiver_exists_positiveFineWindow H r frozen hFrozen
  refine ⟨e, delta / 2, by linarith, ?_⟩
  exact hwindow (delta / 2) (by linarith) (by linarith)

/-- For ANY actual nonnegative physical beta schedule with positive
frozen beta, an explicitly nonempty fine-coupling interval exists
such that the genuine all-one finite-depth Wilson posterior Rayleigh
is positive whenever its fine beta belongs to that interval. -/
theorem fineRightKrylovPairHaarResidualGram_ones_pos_of_fine_in_open_window
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (hFrozen : 0 < beta n) :
    ∃ delta : ℝ, 0 < delta ∧
      (beta (n + 1) < delta →
        0 < star (fun _ : Fin (r + 1) => (1 : ℝ)) ⬝ᵥ
          (Matrix.mulVec
            (fineRightKrylovPairHaarResidualGram
              (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
              n r)
            (fun _ : Fin (r + 1) => (1 : ℝ)))) := by
  obtain ⟨e, delta, hdelta, hwindow⟩ :=
    physicalOriginalUnitReceiver_exists_positiveFineWindow
      (halfExtent (n + 1)) r (beta n) hFrozen
  refine ⟨delta, hdelta, ?_⟩
  intro hFine
  apply fineRightKrylovPairHaarResidualGram_ones_rayleigh_pos_of_fineBudget_small
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r e
  exact hwindow (beta (n + 1)) (hbeta (n + 1)) hFine

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
