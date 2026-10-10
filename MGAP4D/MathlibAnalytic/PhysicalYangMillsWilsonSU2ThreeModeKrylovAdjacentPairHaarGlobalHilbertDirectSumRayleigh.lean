import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarFullLinkAverageRayleigh
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# P4-Q2-T: global original Wilson link Hilbert direct sum, without 1/L_H loss

The frozen Wilson original-link signed posterior innovations are placed
in their genuine finite `PiLp 2` Hilbert direct sum across spatial links.
The physical per-link bound
    ‖I_e(R_j) - I_e(u)‖ ≤ j sqrt(gamma) B_H(t)
implies the global direct-sum estimate
    ‖(I_e(R_j)-I_e(u))_e‖_(ℓ²) ≤ j sqrt(L_H) sqrt(gamma) B_H(t).

The original Gram all-ones Rayleigh is EXACTLY the square of the
Hilbert direct-sum norm of the sum of these genuine signed innovations.
Consequently, if
    sqrt(L_H) sqrt(gamma) r B_H(t) < sqrt(E_unit),
then its normalized Rayleigh exceeds
    (r+1) E_unit / 4.
The 1/L_H loss of the single-link maximum construction disappears.
Only the smallness threshold retains its volume dependence.

No surrogate Gram/law/transfer, Dobrushin, new axioms, or continuum gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

/-- Uniform per-coordinate norm control gives an exact sqrt(card)
bound on the genuine finite ℓ² direct-sum error. -/
theorem p4Q2_finite_piLp2_error_le_sqrt_card
    {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E]
    (j : ℕ) (u v : PiLp 2 (fun _ : ι => E)) (C : ℝ)
    (hC : 0 ≤ C)
    (hCoordinate : ∀ i : ι, ‖v i - u i‖ ≤ (j : ℝ) * C) :
    ‖v - u‖ ≤ ((j : ℝ) * C) *
      Real.sqrt (Fintype.card ι : ℝ) := by
  classical
  let L : ℝ := (Fintype.card ι : ℝ)
  let M : ℝ := (j : ℝ) * C
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  have hSquareEach (i : ι) :
      ‖(v - u) i‖ ^ 2 ≤ M ^ 2 := by
    have hi : ‖(v - u) i‖ ≤ M := by
      simpa only [M, PiLp.sub_apply] using hCoordinate i
    have hn : 0 ≤ ‖(v - u) i‖ := norm_nonneg _
    have hProd :
        0 ≤ (M - ‖(v - u) i‖) * (M + ‖(v - u) i‖) :=
      mul_nonneg (sub_nonneg.mpr hi) (add_nonneg hM hn)
    nlinarith
  have hSquare :
      ‖v - u‖ ^ 2 ≤ L * M ^ 2 := by
    calc
      ‖v - u‖ ^ 2 = ∑ i : ι, ‖(v - u) i‖ ^ 2 :=
        PiLp.norm_sq_eq_of_L2 (fun _ : ι => E) (v - u)
      _ ≤ ∑ _i : ι, M ^ 2 :=
        Finset.sum_le_sum (fun i _ => hSquareEach i)
      _ = L * M ^ 2 := by simp [L]
  have hSqrt : (Real.sqrt L) ^ 2 = L :=
    Real.sq_sqrt (by dsimp [L]; positivity)
  have hBoundNonneg : 0 ≤ M * Real.sqrt L :=
    mul_nonneg hM (Real.sqrt_nonneg _)
  have hBoundSquare : (M * Real.sqrt L) ^ 2 = L * M ^ 2 := by
    rw [mul_pow, hSqrt]
    ring
  change ‖v - u‖ ≤ M * Real.sqrt L
  nlinarith [norm_nonneg (v - u)]

local instance p4DirectSumGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4DirectSumCompact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4DirectSumSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4DirectSumMeasurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4DirectSumBorel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4DirectSumSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The original normalized Wilson posterior right-Gram Rayleigh,
for the all-one Krylov coefficients and the actual physical transfer,
has a strict FULL-LINK quarter-energy lower bound (no 1/L_H)
under a genuine sqrt(link count)-scaled fine-beta budget. -/
theorem fineRightKrylovPairHaarResidualGram_ones_normalizedRayleigh_gt_globalQuarterEnergy
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ k, 0 ≤ beta k}
    (n r : ℕ)
    (hSmall :
      let H := halfExtent (n + 1)
      let L : ℝ := (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)
      Real.sqrt L *
        Real.sqrt (originalWilsonPhysicalSignedInnovationHilbertCoefficient
          H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)) *
        ((r : ℝ) * physicalOriginalNormalizedTransferConstantStepBetaBudget
          H (beta (n + 1))) <
        Real.sqrt (physicalOriginalUnitReceiverFullLinkEnergy
          H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n))) :
    let H := halfExtent (n + 1)
    (((r + 1 : ℕ) : ℝ)) *
      (physicalOriginalUnitReceiverFullLinkEnergy
        H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) / 4) <
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
  let B := physicalOriginalNormalizedTransferConstantStepBetaBudget H (beta (n + 1))
  let Eunit := physicalOriginalUnitReceiverFullLinkEnergy
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  let Link := PeriodicHypercubicEvenSpatialSliceLink H
  let L : ℝ := (Fintype.card Link : ℝ)
  let R : Fin (r + 1) →
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2 :=
    fun j => physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n (j : ℕ)
  let U := WithLp.toLp 2 (fun e : Link => I e u)
  let V (j : Fin (r + 1)) := WithLp.toLp 2 (fun e : Link => I e (R j))
  let D : ℝ := Real.sqrt L * (Real.sqrt gamma * B)
  have hEnergy :
      ‖U‖ ^ 2 = Eunit := by
    rw [PiLp.norm_sq_eq_of_L2]
    rfl
  have hNormU : ‖U‖ = Real.sqrt Eunit := by
    calc
      ‖U‖ = Real.sqrt (‖U‖ ^ 2) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg U)]
      _ = Real.sqrt Eunit := by rw [hEnergy]
  have hBudget :
      (r : ℝ) * D < ‖U‖ := by
    rw [hNormU]
    calc
      (r : ℝ) * D =
          Real.sqrt L * Real.sqrt gamma * ((r : ℝ) * B) := by
        dsimp [D]
        ring
      _ < Real.sqrt Eunit := hSmall
  have hCNonneg : 0 ≤ Real.sqrt gamma * B := by
    exact mul_nonneg (Real.sqrt_nonneg _)
      (physicalOriginalNormalizedTransferConstantStepBetaBudget_nonneg
        H (beta (n + 1)) (hbeta (n + 1)))
  have hNear : ∀ j : Fin (r + 1),
      ‖V j - U‖ ≤ ((j : ℕ) : ℝ) * D := by
    intro j
    have hCoord : ∀ e : Link,
        ‖(V j) e - U e‖ ≤ (((j : ℕ) : ℝ) * (Real.sqrt gamma * B)) := by
      intro e
      have hh := fineRightKrylov_linkInnovation_sub_unit_norm_le_fineBudget
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n (j : ℕ) e
      change ‖I e (R j) - I e u‖ ≤
        (((j : ℕ) : ℝ) * (Real.sqrt gamma * B))
      calc
        ‖I e (R j) - I e u‖ ≤
            Real.sqrt gamma * (((j : ℕ) : ℝ) * B) := hh
        _ = _ := by ring
    have hDirect :=
      p4Q2_finite_piLp2_error_le_sqrt_card
        (j : ℕ) U (V j) (Real.sqrt gamma * B) hCNonneg hCoord
    calc
      ‖V j - U‖ ≤
          (((j : ℕ) : ℝ) * (Real.sqrt gamma * B)) * Real.sqrt L := hDirect
      _ = ((j : ℕ) : ℝ) * D := by dsimp [D]; ring
  have hHalf : ‖U‖ / 2 < ‖U‖ - ((r : ℝ) / 2) * D := by
    linarith [hBudget]
  have hMargin : 0 ≤ ‖U‖ - ((r : ℝ) / 2) * D := by
    linarith [norm_nonneg U]
  have hDirectSumBound :
      (((r + 1 : ℕ) : ℝ) ^ 2) *
        (‖U‖ - ((r : ℝ) / 2) * D) ^ 2 ≤
        ‖∑ j : Fin (r + 1), V j‖ ^ 2 :=
    p4Q2_finite_sum_norm_sq_ge_halfDepth
      r U V D hNear hMargin
  have hCoordSumFinset (s : Finset (Fin (r + 1))) (e : Link) :
      (∑ j ∈ s, V j) e = ∑ j ∈ s, I e (R j) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih =>
        simp only [Finset.sum_insert hj, PiLp.add_apply]
        rw [ih]
  have hCoordSum (e : Link) :
      (∑ j : Fin (r + 1), V j) e =
        ∑ j : Fin (r + 1), I e (R j) := by
    exact hCoordSumFinset Finset.univ e
  have hDirectSumIdentity :
      ‖∑ j : Fin (r + 1), V j‖ ^ 2 =
        ∑ e : Link, ‖∑ j : Fin (r + 1), I e (R j)‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [hCoordSum]
  have hGramIdentity :
      star (fun _ : Fin (r + 1) => (1 : ℝ)) ⬝ᵥ
        (Matrix.mulVec
          (fineRightKrylovPairHaarResidualGram
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r)
          (fun _ : Fin (r + 1) => (1 : ℝ))) =
        ‖∑ j : Fin (r + 1), V j‖ ^ 2 := by
    rw [hDirectSumIdentity]
    simpa only [one_smul, I, R,
      physicalOriginalReceiverPosteriorInnovation] using
      (fineRightKrylovPairHaarResidualGram_rayleigh
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r (fun _ : Fin (r + 1) => (1 : ℝ)))
  have hRaw :
      (((r + 1 : ℕ) : ℝ) ^ 2) *
        (‖U‖ - ((r : ℝ) / 2) * D) ^ 2 ≤
      star (fun _ : Fin (r + 1) => (1 : ℝ)) ⬝ᵥ
        (Matrix.mulVec
          (fineRightKrylovPairHaarResidualGram
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r)
          (fun _ : Fin (r + 1) => (1 : ℝ))) :=
    hDirectSumBound.trans_eq hGramIdentity.symm
  have hN : 0 < (((r + 1 : ℕ) : ℝ)) := by positivity
  have hNormalized :
      (((r + 1 : ℕ) : ℝ)) *
        (‖U‖ - ((r : ℝ) / 2) * D) ^ 2 ≤
        (star (fun _ : Fin (r + 1) => (1 : ℝ)) ⬝ᵥ
          (Matrix.mulVec
            (fineRightKrylovPairHaarResidualGram
              (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
              n r)
            (fun _ : Fin (r + 1) => (1 : ℝ)))) /
          (∑ j : Fin (r + 1),
            ((fun _ : Fin (r + 1) => (1 : ℝ)) j) ^ 2) := by
    rw [fineRightKrylov_ones_coeff_sq_norm_eq, le_div_iff₀ hN]
    calc
      (((r + 1 : ℕ) : ℝ)) *
        (‖U‖ - ((r : ℝ) / 2) * D) ^ 2 * (((r + 1 : ℕ) : ℝ)) =
          (((r + 1 : ℕ) : ℝ) ^ 2) *
            (‖U‖ - ((r : ℝ) / 2) * D) ^ 2 := by ring
      _ ≤ _ := hRaw
  have hFactor :
      0 < ((‖U‖ - ((r : ℝ) / 2) * D) - ‖U‖ / 2) *
        ((‖U‖ - ((r : ℝ) / 2) * D) + ‖U‖ / 2) := by
    apply mul_pos
    · linarith
    · linarith [norm_nonneg U]
  have hSquare :
      ‖U‖ ^ 2 / 4 < (‖U‖ - ((r : ℝ) / 2) * D) ^ 2 := by
    nlinarith [hFactor]
  change (((r + 1 : ℕ) : ℝ)) * (Eunit / 4) < _
  rw [← hEnergy]
  exact lt_of_lt_of_le (mul_lt_mul_of_pos_left hSquare hN) hNormalized

/-- Every actual Wilson nonnegative coupling profile with positive
frozen beta has a positive fine-coupling window in which the
all-one normalized ORIGINAL Gram exceeds (r+1)*E_unit/4.
The RADIUS depends on H and r; the lower-bound formula has no 1/L_H. -/
theorem fineRightKrylovPairHaarResidualGram_exists_globalQuarterEnergy_fineWindow
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ k, 0 ≤ beta k}
    (n r : ℕ) (hFrozen : 0 < beta n) :
    ∃ delta : ℝ, 0 < delta ∧
      (beta (n + 1) < delta →
        (((r + 1 : ℕ) : ℝ)) *
          (physicalOriginalUnitReceiverFullLinkEnergy
            (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
            (beta n) (hbeta n) / 4) <
          (star (fun _ : Fin (r + 1) => (1 : ℝ)) ⬝ᵥ
            (Matrix.mulVec
              (fineRightKrylovPairHaarResidualGram
                (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
                n r)
              (fun _ : Fin (r + 1) => (1 : ℝ)))) /
            (∑ j : Fin (r + 1),
              ((fun _ : Fin (r + 1) => (1 : ℝ)) j) ^ 2)) := by
  let H := halfExtent (n + 1)
  let L : ℝ := (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)
  let Eunit := physicalOriginalUnitReceiverFullLinkEnergy
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  have hEnergy : 0 < Eunit :=
    physicalOriginalUnitReceiverFullLinkEnergy_pos_of_beta_pos_SU2
      H (beta n) hFrozen
  obtain ⟨delta, hDelta, hwindow⟩ :=
    physicalOriginalNormalizedTransferConstantStepBetaBudget_exists_window
      H r
      (Real.sqrt L *
        Real.sqrt (originalWilsonPhysicalSignedInnovationHilbertCoefficient
          H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)))
      (Real.sqrt Eunit)
      (Real.sqrt_pos.mpr hEnergy)
  refine ⟨delta, hDelta, ?_⟩
  intro hFine
  apply fineRightKrylovPairHaarResidualGram_ones_normalizedRayleigh_gt_globalQuarterEnergy
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r
  exact hwindow (beta (n + 1)) (hbeta (n + 1)) hFine

/-- A concrete positive-frozen and positive-fine Wilson beta profile,
zero at all other scales, has the genuine FULL energy lower bound.
No factor of 1/(number of spatial links) remains in the Rayleigh floor. -/
theorem fineRightKrylovPairHaarResidualGram_exists_positiveFine_globalQuarterEnergy_schedule
    (halfExtent : ℕ → ℕ) (n r : ℕ)
    (frozen : ℝ) (hFrozen : 0 < frozen) :
    ∃ (beta : ℕ → ℝ) (hbeta : ∀ k, 0 ≤ beta k),
      beta n = frozen ∧ 0 < beta (n + 1) ∧
        (∀ k, k ≠ n → k ≠ n + 1 → beta k = 0) ∧
        0 < (((r + 1 : ℕ) : ℝ)) *
          (physicalOriginalUnitReceiverFullLinkEnergy
            (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
            (beta n) (hbeta n) / 4) ∧
        (((r + 1 : ℕ) : ℝ)) *
          (physicalOriginalUnitReceiverFullLinkEnergy
            (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
            (beta n) (hbeta n) / 4) <
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
  let L : ℝ := (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)
  let Eunit := physicalOriginalUnitReceiverFullLinkEnergy
    H 2 specialUnitaryTwoWilsonRankPositive frozen (le_of_lt hFrozen)
  have hEnergy : 0 < Eunit :=
    physicalOriginalUnitReceiverFullLinkEnergy_pos_of_beta_pos_SU2 H frozen hFrozen
  obtain ⟨delta, hdelta, hwindow⟩ :=
    physicalOriginalNormalizedTransferConstantStepBetaBudget_exists_window
      H r
      (Real.sqrt L *
        Real.sqrt (originalWilsonPhysicalSignedInnovationHilbertCoefficient
          H 2 specialUnitaryTwoWilsonRankPositive frozen (le_of_lt hFrozen)))
      (Real.sqrt Eunit) (Real.sqrt_pos.mpr hEnergy)
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
  have hPhysical :
      Real.sqrt L *
        Real.sqrt (originalWilsonPhysicalSignedInnovationHilbertCoefficient
          H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)) *
        ((r : ℝ) *
          physicalOriginalNormalizedTransferConstantStepBetaBudget
            H (beta (n + 1))) <
        Real.sqrt (physicalOriginalUnitReceiverFullLinkEnergy
          H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)) := by
    simpa only [hFrozenAt, hFineAt] using
      (hwindow fine hFinePos.le hFineSmall)
  have hEnergyAt :
      0 < physicalOriginalUnitReceiverFullLinkEnergy
        H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) := by
    simpa only [hFrozenAt] using hEnergy
  have hFloor :
      0 < (((r + 1 : ℕ) : ℝ)) *
        (physicalOriginalUnitReceiverFullLinkEnergy
          H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) / 4) :=
    mul_pos (by positivity) (div_pos hEnergyAt (by norm_num))
  have hRayleigh :
      (((r + 1 : ℕ) : ℝ)) *
        (physicalOriginalUnitReceiverFullLinkEnergy
          H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) / 4) <
        (star (fun _ : Fin (r + 1) => (1 : ℝ)) ⬝ᵥ
          (Matrix.mulVec
            (fineRightKrylovPairHaarResidualGram
              (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
              n r)
            (fun _ : Fin (r + 1) => (1 : ℝ)))) /
          (∑ j : Fin (r + 1),
            ((fun _ : Fin (r + 1) => (1 : ℝ)) j) ^ 2) :=
    fineRightKrylovPairHaarResidualGram_ones_normalizedRayleigh_gt_globalQuarterEnergy
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hPhysical
  exact ⟨beta, hbeta, hFrozenAt, by simpa only [hFineAt] using hFinePos,
    hAway, hFloor, hRayleigh⟩

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
