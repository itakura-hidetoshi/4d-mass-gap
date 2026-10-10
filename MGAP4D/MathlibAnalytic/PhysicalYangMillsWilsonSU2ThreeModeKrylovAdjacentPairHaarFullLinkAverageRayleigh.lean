import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPositiveFineQuarterRayleigh
import Mathlib.Tactic

/-!
# P4-Q2-S: true full-link Wilson energy controls positive-fine all-one Rayleigh

At fixed genuine finite Wilson volume H and positive frozen coupling b,
the physical unit receiver energy is the sum over the original spatial
links of squared Hilbert innovations. The maximum link contributes at
least the average E_unit(b,H)/L_H, where

  L_H = Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) > 0.

Using the exact r/2 sum-of-errors bound and strict quarter-link floor
from P4-Q2-Q/R, a sufficiently small positive fine coupling satisfies

  normalized_ones_Rayleigh
    > (r+1) * E_unit(b,H) / (4 * L_H) > 0.

We prove this using the original Wilson posterior energy and the actual
physical normalized-transfer budget: no proxy Gram, no surrogate law,
no Dobrushin and no new axioms. The estimate is finite-volume and
finite-Krylov-depth only; L_H is not replaced by a universal constant.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

/-- A nonempty finite index set admits an index whose value controls
the entire finite sum by its cardinality. This is just the genuine
maximum-image principle of mathlib, not a probabilistic substitute. -/
theorem p4Q2_finite_sum_le_card_mul_some
    {ι : Type*} [Fintype ι]
    (f : ι → ℝ)
    (hNonempty : (Finset.univ : Finset ι).Nonempty) :
    ∃ i : ι, (∑ j : ι, f j) ≤ (Fintype.card ι : ℝ) * f i := by
  classical
  obtain ⟨i, _hi, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset ι) f hNonempty
  refine ⟨i, ?_⟩
  calc
    (∑ j : ι, f j) ≤ ∑ _j : ι, f i := by
      exact Finset.sum_le_sum (fun j hj => hmax j hj)
    _ = (Fintype.card ι : ℝ) * f i := by simp

local instance p4FullLinkAverageGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4FullLinkAverageCompact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4FullLinkAverageSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4FullLinkAverageMeasurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4FullLinkAverageBorel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4FullLinkAverageSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- A genuine Wilson spatial link has positive innovation norm and
squared innovation at least E_unit/L_H, in the cross-multiplied
version that makes positivity of the finite link count transparent. -/
theorem physicalOriginalUnitReceiver_exists_link_ge_fullEnergy_average_SU2
    (H : ℕ) (frozen : ℝ) (hFrozen : 0 < frozen) :
    ∃ e : PeriodicHypercubicEvenSpatialSliceLink H,
      0 < ‖physicalOriginalReceiverPosteriorInnovation
        H 2 specialUnitaryTwoWilsonRankPositive frozen (le_of_lt hFrozen) e
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)‖ ∧
      physicalOriginalUnitReceiverFullLinkEnergy
        H 2 specialUnitaryTwoWilsonRankPositive frozen (le_of_lt hFrozen) ≤
        (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
          ‖physicalOriginalReceiverPosteriorInnovation
            H 2 specialUnitaryTwoWilsonRankPositive frozen (le_of_lt hFrozen) e
            (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)‖ ^ 2 := by
  classical
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let I := physicalOriginalReceiverPosteriorInnovation
    H 2 specialUnitaryTwoWilsonRankPositive frozen (le_of_lt hFrozen)
  let q : PeriodicHypercubicEvenSpatialSliceLink H → ℝ :=
    fun t => ‖I t u‖ ^ 2
  obtain ⟨e₀, _h₀⟩ :=
    physicalOriginalUnitReceiver_exists_positive_link_norm_SU2 H frozen hFrozen
  obtain ⟨e, hMax⟩ :=
    p4Q2_finite_sum_le_card_mul_some q
      (⟨e₀, Finset.mem_univ e₀⟩ :
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)).Nonempty)
  have hAverage :
      physicalOriginalUnitReceiverFullLinkEnergy
        H 2 specialUnitaryTwoWilsonRankPositive frozen (le_of_lt hFrozen) ≤
        (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
          ‖I e u‖ ^ 2 := by
    change (∑ t : PeriodicHypercubicEvenSpatialSliceLink H, q t) ≤
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) * q e
    exact hMax
  have hEnergy :
      0 < physicalOriginalUnitReceiverFullLinkEnergy
        H 2 specialUnitaryTwoWilsonRankPositive frozen (le_of_lt hFrozen) :=
    physicalOriginalUnitReceiverFullLinkEnergy_pos_of_beta_pos_SU2 H frozen hFrozen
  have hProduct :
      0 < (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
        ‖I e u‖ ^ 2 := lt_of_lt_of_le hEnergy hAverage
  have hSelected : 0 < ‖I e u‖ := by
    by_contra hn
    have hZero : ‖I e u‖ = 0 :=
      le_antisymm (le_of_not_gt hn) (norm_nonneg _)
    simp [hZero] at hProduct
  exact ⟨e, hSelected, hAverage⟩

/-- The positive-fine physical budget at a maximum-energy original
Wilson link implies a strict lower bound in terms of the FULL original
unit receiver energy, divided by the actual finite number of links. -/
theorem fineRightKrylovPairHaarResidualGram_ones_normalizedRayleigh_gt_fullEnergy_quarterAverage
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ k, 0 ≤ beta k}
    (n r : ℕ)
    (e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)))
    (hAverage :
      physicalOriginalUnitReceiverFullLinkEnergy
        (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
        (beta n) (hbeta n) ≤
        (Fintype.card
          (PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1))) : ℝ) *
          ‖physicalOriginalReceiverPosteriorInnovation
            (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
            (beta n) (hbeta n) e
            (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector
              (halfExtent (n + 1)) 2)‖ ^ 2)
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
    ((r + 1 : ℕ) : ℝ) *
      (physicalOriginalUnitReceiverFullLinkEnergy
        H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) /
        (4 * (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ))) <
      (star (fun _ : Fin (r + 1) => (1 : ℝ)) ⬝ᵥ
        (Matrix.mulVec
          (fineRightKrylovPairHaarResidualGram
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r)
          (fun _ : Fin (r + 1) => (1 : ℝ)))) /
        (∑ j : Fin (r + 1),
          ((fun _ : Fin (r + 1) => (1 : ℝ)) j) ^ 2) := by
  let H := halfExtent (n + 1)
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let I := physicalOriginalReceiverPosteriorInnovation
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  let L : ℝ := (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)
  let E : ℝ := physicalOriginalUnitReceiverFullLinkEnergy
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  have hNonempty :
      (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)).Nonempty :=
    ⟨e, Finset.mem_univ e⟩
  have hCardNat :
      0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) := by
    simpa using (Finset.card_pos.mpr hNonempty)
  have hCard : 0 < L := by
    dsimp [L]
    exact Nat.cast_pos.mpr hCardNat
  have hFraction : E / (4 * L) ≤ ‖I e u‖ ^ 2 / 4 := by
    apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) hCard)).mpr
    calc
      E ≤ L * ‖I e u‖ ^ 2 := hAverage
      _ = (‖I e u‖ ^ 2 / 4) * (4 * L) := by ring
  have hQuarter :
      ((r + 1 : ℕ) : ℝ) * (‖I e u‖ ^ 2 / 4) <
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
  change ((r + 1 : ℕ) : ℝ) * (E / (4 * L)) < _
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left hFraction (by positivity)) hQuarter

/-- For ANY genuine nonnegative Wilson beta schedule with positive
frozen coupling, a nonempty fine interval has the uniform-in-fine
(but NOT uniform-in-H/r) lower bound by full physical unit energy. -/
theorem fineRightKrylovPairHaarResidualGram_exists_fullEnergy_quarterAverage_fineWindow
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ k, 0 ≤ beta k}
    (n r : ℕ) (hFrozen : 0 < beta n) :
    ∃ delta : ℝ, 0 < delta ∧
      (beta (n + 1) < delta →
        ((r + 1 : ℕ) : ℝ) *
          (physicalOriginalUnitReceiverFullLinkEnergy
            (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
            (beta n) (hbeta n) /
            (4 * (Fintype.card
              (PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1))) : ℝ))) <
          (star (fun _ : Fin (r + 1) => (1 : ℝ)) ⬝ᵥ
            (Matrix.mulVec
              (fineRightKrylovPairHaarResidualGram
                (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
                n r)
              (fun _ : Fin (r + 1) => (1 : ℝ)))) /
            (∑ j : Fin (r + 1),
              ((fun _ : Fin (r + 1) => (1 : ℝ)) j) ^ 2)) := by
  let H := halfExtent (n + 1)
  obtain ⟨e, hPos, hAverage⟩ :=
    physicalOriginalUnitReceiver_exists_link_ge_fullEnergy_average_SU2
      H (beta n) hFrozen
  obtain ⟨delta, hdelta, hwindow⟩ :=
    physicalOriginalNormalizedTransferConstantStepBetaBudget_exists_window
      H r
      (Real.sqrt (originalWilsonPhysicalSignedInnovationHilbertCoefficient
        H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)))
      (‖physicalOriginalReceiverPosteriorInnovation
        H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) e
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)‖)
      hPos
  refine ⟨delta, hdelta, ?_⟩
  intro hFine
  apply fineRightKrylovPairHaarResidualGram_ones_normalizedRayleigh_gt_fullEnergy_quarterAverage
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r e hAverage
  exact hwindow (beta (n + 1)) (hbeta (n + 1)) hFine

/-- An ACTUAL nonnegative adjacent beta profile (positive frozen and
positive fine, zero elsewhere) has a strictly positive and explicit
FULL-LINK averaged energy lower bound for the ORIGINAL Gram Rayleigh. -/
theorem fineRightKrylovPairHaarResidualGram_exists_positiveFine_fullEnergy_quarterAverage_schedule
    (halfExtent : ℕ → ℕ) (n r : ℕ)
    (frozen : ℝ) (hFrozen : 0 < frozen) :
    ∃ (beta : ℕ → ℝ) (hbeta : ∀ k, 0 ≤ beta k),
      beta n = frozen ∧ 0 < beta (n + 1) ∧
        (∀ k, k ≠ n → k ≠ n + 1 → beta k = 0) ∧
        0 < ((r + 1 : ℕ) : ℝ) *
          (physicalOriginalUnitReceiverFullLinkEnergy
            (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
            (beta n) (hbeta n) /
            (4 * (Fintype.card
              (PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1))) : ℝ))) ∧
        ((r + 1 : ℕ) : ℝ) *
          (physicalOriginalUnitReceiverFullLinkEnergy
            (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
            (beta n) (hbeta n) /
            (4 * (Fintype.card
              (PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1))) : ℝ))) <
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
  obtain ⟨e, hPos, hAverage⟩ :=
    physicalOriginalUnitReceiver_exists_link_ge_fullEnergy_average_SU2
      H frozen hFrozen
  obtain ⟨delta, hdelta, hwindow⟩ :=
    physicalOriginalNormalizedTransferConstantStepBetaBudget_exists_window
      H r
      (Real.sqrt (originalWilsonPhysicalSignedInnovationHilbertCoefficient
        H 2 specialUnitaryTwoWilsonRankPositive frozen (le_of_lt hFrozen)))
      (‖physicalOriginalReceiverPosteriorInnovation
        H 2 specialUnitaryTwoWilsonRankPositive frozen (le_of_lt hFrozen) e
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)‖)
      hPos
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
  have hAverageAt :
      physicalOriginalUnitReceiverFullLinkEnergy
        H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) ≤
        (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
          ‖physicalOriginalReceiverPosteriorInnovation
            H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) e
            (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2)‖ ^ 2 := by
    simpa only [hFrozenAt] using hAverage
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
  have hCardNat :
      0 < Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) := by
    have hn :
        (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H)).Nonempty :=
      ⟨e, Finset.mem_univ e⟩
    simpa using (Finset.card_pos.mpr hn)
  have hCard : (0 : ℝ) <
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) :=
    Nat.cast_pos.mpr hCardNat
  have hEnergy :
      0 < physicalOriginalUnitReceiverFullLinkEnergy
        H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) := by
    simpa only [hFrozenAt] using
      (physicalOriginalUnitReceiverFullLinkEnergy_pos_of_beta_pos_SU2 H frozen hFrozen)
  have hFloor :
      0 < ((r + 1 : ℕ) : ℝ) *
        (physicalOriginalUnitReceiverFullLinkEnergy
          H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) /
          (4 * (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ))) :=
    mul_pos (by positivity) (div_pos hEnergy (mul_pos (by norm_num) hCard))
  have hRayleigh :
      ((r + 1 : ℕ) : ℝ) *
        (physicalOriginalUnitReceiverFullLinkEnergy
          H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) /
          (4 * (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ))) <
        (star (fun _ : Fin (r + 1) => (1 : ℝ)) ⬝ᵥ
          (Matrix.mulVec
            (fineRightKrylovPairHaarResidualGram
              (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
              n r)
            (fun _ : Fin (r + 1) => (1 : ℝ)))) /
          (∑ j : Fin (r + 1),
            ((fun _ : Fin (r + 1) => (1 : ℝ)) j) ^ 2) :=
    fineRightKrylovPairHaarResidualGram_ones_normalizedRayleigh_gt_fullEnergy_quarterAverage
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e hAverageAt hSmall
  exact ⟨beta, hbeta, hFrozenAt, by simpa only [hFineAt] using hFinePos,
    hAway, hFloor, hRayleigh⟩

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
