import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarTopProjectionPositiveFineWindow
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarSpectralKrylovDecay
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# P4-Q2-AA: original Wilson full-link top spectral Krylov depth Rayleigh

For the ACTUAL normalized physical fine Wilson transfer S, its FULL
top spectral projection P, the ORIGINAL frozen signed innovation I,
and the original ALL spatial links PiLp 2 receiver V_j = (I_e(S^j u_H))_e,
prove geometrically summable signed innovation errors:
  ‖V_j - U‖ <= C_H,beta q^j,  U = (I_e(P u_H))_e,
  0 <= q = ‖S-P‖ < 1,
  C = sqrt(gamma) sqrt(linkCount) (1 + B_H(beta_fine)).

In particular, independent of Krylov depth r,
  ‖sum_{j=0}^r V_j - (r+1) U‖ <= C/(1-q).
This replaces the previous O(r)-growing telescoping bound by a
finite-volume depth-UNIFORM cumulative error budget.

Transfer and posterior are the original physical Wilson operators;
frozen and fine couplings are distinct. No proxy, Dobrushin, new
axiom, sorry/admit, volume-uniform constant or continuum-gap claim.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 850000

/-- Exact geometric sum telescoping, including q=0. -/
theorem p4Q2AA_geom_sum_mul_one_sub (q : ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n, q ^ j) * (1 - q) = 1 - q ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, add_mul, ih, pow_succ]
      ring

/-- Every finite geometric sum is bounded by the FULL infinite
geometric budget 1/(1-q), provided 0<=q<1. -/
theorem p4Q2AA_geom_sum_le_inv_gap
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    (∑ j ∈ Finset.range n, q ^ j) ≤ (1 - q)⁻¹ := by
  have hGap : 0 < 1 - q := sub_pos.mpr hq1
  have hMul :
      (∑ j ∈ Finset.range n, q ^ j) * (1 - q) ≤ 1 := by
    rw [p4Q2AA_geom_sum_mul_one_sub]
    exact sub_le_self _ (pow_nonneg hq0 _)
  have hInv : (∑ j ∈ Finset.range n, q ^ j) ≤ 1 / (1 - q) :=
    (le_div_iff₀ hGap).2 hMul
  simpa only [one_div] using hInv

/-- Generic finite real-normed vector error: geometric per-mode errors
give a depth-INDEPENDENT bound for the deviation of the whole sum from
N times its shared top component. -/
theorem p4Q2AA_finite_geometric_sum_error_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℕ) (u : E) (v : Fin (r + 1) → E)
    (q C : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hC : 0 ≤ C)
    (hNear : ∀ j : Fin (r + 1), ‖v j - u‖ ≤ C * q ^ (j : ℕ)) :
    ‖(∑ j : Fin (r + 1), v j) - (((r + 1 : ℕ) : ℝ) • u)‖ ≤
      C / (1 - q) := by
  classical
  have hRel :
      (∑ j : Fin (r + 1), v j) -
          (((r + 1 : ℕ) : ℝ) • u) =
        ∑ j : Fin (r + 1), (v j - u) := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_fin, Nat.cast_smul_eq_nsmul]
  have hFinGeom :
      (∑ j : Fin (r + 1), q ^ (j : ℕ)) ≤ (1 - q)⁻¹ := by
    rw [Fin.sum_univ_eq_sum_range]
    exact p4Q2AA_geom_sum_le_inv_gap q hq0 hq1 (r + 1)
  calc
    ‖(∑ j : Fin (r + 1), v j) - (((r + 1 : ℕ) : ℝ) • u)‖ =
        ‖∑ j : Fin (r + 1), (v j - u)‖ := congrArg norm hRel
    _ ≤ ∑ j : Fin (r + 1), C * q ^ (j : ℕ) :=
      norm_sum_le_of_le Finset.univ (by
        intro j _hj
        exact hNear j)
    _ = C * (∑ j : Fin (r + 1), q ^ (j : ℕ)) := by
      rw [Finset.mul_sum]
    _ ≤ C * (1 - q)⁻¹ := mul_le_mul_of_nonneg_left hFinGeom hC
    _ = C / (1 - q) := by rw [div_eq_mul_inv]

/-- Quantitative depth-linear signal with depth-uniform geometric
error. No positivity of the margin is needed until squaring. -/
theorem p4Q2AA_finite_geometric_sum_norm_lower
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℕ) (u : E) (v : Fin (r + 1) → E)
    (q C : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hC : 0 ≤ C)
    (hNear : ∀ j : Fin (r + 1), ‖v j - u‖ ≤ C * q ^ (j : ℕ)) :
    (((r + 1 : ℕ) : ℝ) * ‖u‖) - C / (1 - q) ≤
      ‖∑ j : Fin (r + 1), v j‖ := by
  have hError :=
    p4Q2AA_finite_geometric_sum_error_le r u v q C hq0 hq1 hC hNear
  have hRel :
      (∑ j : Fin (r + 1), v j) -
          ((∑ j : Fin (r + 1), v j) -
            (((r + 1 : ℕ) : ℝ) • u)) =
        (((r + 1 : ℕ) : ℝ) • u) := by
    abel
  have hTriangle := norm_sub_le
    (∑ j : Fin (r + 1), v j)
    ((∑ j : Fin (r + 1), v j) -
      (((r + 1 : ℕ) : ℝ) • u))
  rw [hRel] at hTriangle
  have hN : 0 ≤ (((r + 1 : ℕ) : ℝ)) := by positivity
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hN] at hTriangle
  linarith

local instance p4AATopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4AACompact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4AASecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4AAMeasurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4AABorel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4AALinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4AARealHilbertComplete (H : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H 2).completeSpace_coe

namespace GroundStatePosteriorJoint

/-- Coordinatewise ORIGINAL frozen Wilson innovation Lipschitz bound,
assembled in the authentic all-link PiLp 2 Hilbert direct sum. -/
theorem physicalOriginalFrozenPosteriorFullLink_sub_norm_le
    (H : ℕ) (frozen : ℝ) (hFrozen : 0 ≤ frozen)
    (v w : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :
    let I := physicalOriginalReceiverPosteriorInnovation
      H 2 specialUnitaryTwoWilsonRankPositive frozen hFrozen
    let gamma := originalWilsonPhysicalSignedInnovationHilbertCoefficient
      H 2 specialUnitaryTwoWilsonRankPositive frozen hFrozen
    ‖WithLp.toLp 2 (fun e : PeriodicHypercubicEvenSpatialSliceLink H => I e v) -
      WithLp.toLp 2 (fun e : PeriodicHypercubicEvenSpatialSliceLink H => I e w)‖ ≤
        (Real.sqrt gamma * ‖v-w‖) *
          Real.sqrt (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) := by
  let I := physicalOriginalReceiverPosteriorInnovation
    H 2 specialUnitaryTwoWilsonRankPositive frozen hFrozen
  let gamma := originalWilsonPhysicalSignedInnovationHilbertCoefficient
    H 2 specialUnitaryTwoWilsonRankPositive frozen hFrozen
  let U := WithLp.toLp 2 (fun e : PeriodicHypercubicEvenSpatialSliceLink H => I e w)
  let V := WithLp.toLp 2 (fun e : PeriodicHypercubicEvenSpatialSliceLink H => I e v)
  let C : ℝ := Real.sqrt gamma * ‖v-w‖
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hCoord :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ‖V e - U e‖ ≤ ((1 : ℕ) : ℝ) * C := by
    intro e
    have hLip :=
      physicalOriginalReceiverPosteriorInnovation_norm_le_sqrt_signedHilbert
        H 2 specialUnitaryTwoWilsonRankPositive frozen hFrozen e (v - w)
    change ‖I e (v - w)‖ ≤ Real.sqrt gamma * ‖v - w‖ at hLip
    change ‖I e v - I e w‖ ≤ ((1 : ℕ) : ℝ) * C
    calc
      ‖I e v - I e w‖ = ‖I e (v-w)‖ := by
        exact (congrArg norm
          (physicalOriginalReceiverPosteriorInnovation_sub
            H 2 specialUnitaryTwoWilsonRankPositive
            frozen hFrozen e v w)).symm
      _ ≤ Real.sqrt gamma * ‖v-w‖ := hLip
      _ = ((1 : ℕ) : ℝ) * C := by simp [C]
  have hFull := p4Q2_finite_piLp2_error_le_sqrt_card 1 U V C hC hCoord
  simpa only [Nat.cast_one, one_mul] using hFull

/-- The physical all-link ORIGINAL posterior innovation converges to
its genuine top spectral component at rate q^j for EVERY j>=0,
including the true zero-depth mode. The coefficient adds the actual
positive fine beta budget B_H to handle j=0, not an O(r) loss. -/
theorem fineRightKrylov_originalPosteriorFullLink_sub_topProjection_norm_le_geometric_allDepth
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ k, 0 ≤ beta k}
    (n j : ℕ) :
    let H := halfExtent (n + 1)
    let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
      H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
    let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
    let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
    let I := physicalOriginalReceiverPosteriorInnovation
      H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
    let gamma := originalWilsonPhysicalSignedInnovationHilbertCoefficient
      H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
    let B := physicalOriginalNormalizedTransferConstantStepBetaBudget H (beta (n+1))
    let L : ℝ := (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)
    let C0 := (Real.sqrt gamma * B) * Real.sqrt L
    let C1 := Real.sqrt gamma * Real.sqrt L
    ‖WithLp.toLp 2 (fun e : PeriodicHypercubicEvenSpatialSliceLink H =>
        I e (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n j)) -
      WithLp.toLp 2 (fun e : PeriodicHypercubicEvenSpatialSliceLink H => I e (P u))‖ ≤
      (C0+C1) * ‖S-P‖ ^ j := by
  let H := halfExtent (n + 1)
  let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
    H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let I := physicalOriginalReceiverPosteriorInnovation
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  let gamma := originalWilsonPhysicalSignedInnovationHilbertCoefficient
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  let B := physicalOriginalNormalizedTransferConstantStepBetaBudget H (beta (n+1))
  let L : ℝ := (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)
  let C0 := (Real.sqrt gamma * B) * Real.sqrt L
  let C1 := Real.sqrt gamma * Real.sqrt L
  let R (j : ℕ) := physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n j
  let U := WithLp.toLp 2 (fun e : PeriodicHypercubicEvenSpatialSliceLink H => I e (P u))
  let V (j : ℕ) := WithLp.toLp 2 (fun e : PeriodicHypercubicEvenSpatialSliceLink H => I e (R j))
  have hB : 0 ≤ B :=
    physicalOriginalNormalizedTransferConstantStepBetaBudget_nonneg
      H (beta (n + 1)) (hbeta (n + 1))
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  have hC1 : 0 ≤ C1 := by dsimp [C1]; positivity
  have hu : ‖u‖ = 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_norm H 2
  have hq0 : 0 ≤ ‖S-P‖ := norm_nonneg (S-P)
  change ‖V j-U‖ ≤ (C0+C1) * ‖S-P‖ ^ j
  cases j with
  | zero =>
      have hR0 : R 0 = u :=
        fineRightFactor_zeroDepth_eq_constantUnit_anyFineBeta
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n
      have hProj : ‖u-P u‖ ≤ B := by
        simpa only [norm_sub_rev] using
          (physicalOriginalFineTopProjection_constantUnit_norm_sub_le_betaBudget
            H (beta (n+1)) (hbeta (n+1)))
      have hRaw :
          ‖V 0-U‖ ≤ (Real.sqrt gamma * ‖R 0-P u‖) * Real.sqrt L := by
        exact physicalOriginalFrozenPosteriorFullLink_sub_norm_le
          H (beta n) (hbeta n) (R 0) (P u)
      have hBound : ‖V 0-U‖ ≤ C0 := by
        calc
          ‖V 0-U‖ ≤ (Real.sqrt gamma * ‖R 0-P u‖) * Real.sqrt L := hRaw
          _ ≤ (Real.sqrt gamma * B) * Real.sqrt L := by
            rw [hR0]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hProj (Real.sqrt_nonneg _))
              (Real.sqrt_nonneg _)
          _ = C0 := rfl
      simpa only [pow_zero, mul_one] using
        hBound.trans (le_add_of_nonneg_right hC1)
  | succ k =>
      have hDecay :
          ‖V (k+1)-U‖ ≤
            (Real.sqrt gamma * (‖S-P‖ ^ (k+1) * ‖u‖)) * Real.sqrt L :=
        fineRightKrylov_originalPosteriorFullLink_sub_topProjection_norm_le_geometric
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n k
      have hGeom : ‖V (k+1)-U‖ ≤ C1 * ‖S-P‖ ^ (k+1) := by
        calc
          ‖V (k+1)-U‖ ≤
            (Real.sqrt gamma * (‖S-P‖ ^ (k+1) * ‖u‖)) * Real.sqrt L := hDecay
          _ = C1 * ‖S-P‖ ^ (k+1) := by rw [hu]; dsimp [C1]; ring
      exact hGeom.trans (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_left hC0) (pow_nonneg hq0 _))

/-- Depth-independent geometric error in the genuine full-link ORIGINAL
Wilson signed posterior sum, and the corresponding depth-linear lower
signal bound. The actual finite-H q is strictly below one. -/
theorem fineRightKrylov_originalPosteriorFullLink_sum_norm_lower_geometric
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ k, 0 ≤ beta k}
    (n r : ℕ) :
    let H := halfExtent (n+1)
    let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
      H 2 specialUnitaryTwoWilsonRankPositive (beta (n+1)) (hbeta (n+1))
    let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H 2 specialUnitaryTwoWilsonRankPositive (beta (n+1)) (hbeta (n+1))
    let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
    let I := physicalOriginalReceiverPosteriorInnovation
      H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
    let gamma := originalWilsonPhysicalSignedInnovationHilbertCoefficient
      H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
    let B := physicalOriginalNormalizedTransferConstantStepBetaBudget H (beta (n+1))
    let L : ℝ := (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)
    let C := (Real.sqrt gamma * B) * Real.sqrt L + Real.sqrt gamma * Real.sqrt L
    let U := WithLp.toLp 2 (fun e : PeriodicHypercubicEvenSpatialSliceLink H => I e (P u))
    let V (j : ℕ) := WithLp.toLp 2 (fun e : PeriodicHypercubicEvenSpatialSliceLink H =>
      I e (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n j))
    (((r+1:ℕ):ℝ) * ‖U‖) - C/(1-‖S-P‖) ≤
      ‖∑ j : Fin (r+1), V (j:ℕ)‖ := by
  let H := halfExtent (n+1)
  let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
    H 2 specialUnitaryTwoWilsonRankPositive (beta (n+1)) (hbeta (n+1))
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive (beta (n+1)) (hbeta (n+1))
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let I := physicalOriginalReceiverPosteriorInnovation
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  let gamma := originalWilsonPhysicalSignedInnovationHilbertCoefficient
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  let B := physicalOriginalNormalizedTransferConstantStepBetaBudget H (beta (n+1))
  let L : ℝ := (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)
  let C := (Real.sqrt gamma * B) * Real.sqrt L + Real.sqrt gamma * Real.sqrt L
  let U := WithLp.toLp 2 (fun e : PeriodicHypercubicEvenSpatialSliceLink H => I e (P u))
  let V (j : ℕ) := WithLp.toLp 2 (fun e : PeriodicHypercubicEvenSpatialSliceLink H =>
      I e (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n j))
  have hq : ‖S-P‖ < 1 :=
    physicalOriginalNormalizedFineTransfer_sub_topSpectralProjection_norm_lt_one
      H (beta (n+1)) (hbeta (n+1))
  have hC : 0 ≤ C := by dsimp[C]; positivity
  have hNear : ∀ j : Fin (r+1), ‖V (j:ℕ)-U‖ ≤ C*‖S-P‖^(j:ℕ) := by
    intro j
    exact fineRightKrylov_originalPosteriorFullLink_sub_topProjection_norm_le_geometric_allDepth
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n (j:ℕ)
  exact p4Q2AA_finite_geometric_sum_norm_lower r U
    (fun j : Fin (r+1) => V (j:ℕ)) ‖S-P‖ C (norm_nonneg _) hq hC hNear

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
