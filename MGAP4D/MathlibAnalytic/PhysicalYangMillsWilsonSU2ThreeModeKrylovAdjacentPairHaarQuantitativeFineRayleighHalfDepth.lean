import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarConstructivePositiveFineProfile
import Mathlib.Tactic

/-!
# P4-Q2-Q: quantitative positive-fine original Wilson right Gram Rayleigh

For the genuine physical fine-right Krylov orbit R_j and the actual
frozen Wilson posterior link innovation I_e, the proved error bound
is ‖I_e(R_j) - I_e(u)‖ ≤ j sqrt(gamma) B_H(beta_fine).

Summing the true j-dependent errors (rather than replacing every j by
the maximum r) yields the exact triangular coefficient r/2. For a
nonnegative margin, the ORIGINAL Wilson right Gram satisfies

  onesᵀ G_r ones ≥ (r+1)² (‖I_e(u)‖ - (r/2) sqrt(gamma) B)².

The corresponding normalized Rayleigh is ≥ (r+1) times the squared
margin. No surrogate posterior/transfer, depth/volume uniformity,
or continuum gap is assumed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

/-- Exact finite-depth triangular error budget over Fin (r+1).
The factor one-half is genuine and avoids the coarser uniform r-bound. -/
theorem p4Q2_fin_linear_error_sum_eq_halfDepth
    (r : ℕ) (C : ℝ) :
    (∑ j : Fin (r + 1), (((j : ℕ) : ℝ) * C)) =
      (((r + 1 : ℕ) : ℝ) * (((r : ℝ) / 2) * C)) := by
  classical
  have hNat :
      (∑ k ∈ Finset.range (r + 1), k) * 2 = (r + 1) * r := by
    simpa using Finset.sum_range_id_mul_two (r + 1)
  have hReal :
      (∑ k ∈ Finset.range (r + 1), (k : ℝ)) * 2 =
        (((r + 1 : ℕ) : ℝ) * (r : ℝ)) := by
    exact_mod_cast hNat
  have hFin :
      (∑ j : Fin (r + 1), ((j : ℕ) : ℝ)) =
        (((r + 1 : ℕ) : ℝ) * (r : ℝ)) / 2 := by
    rw [Fin.sum_univ_eq_sum_range]
    linarith
  calc
    (∑ j : Fin (r + 1), (((j : ℕ) : ℝ) * C)) =
        (∑ j : Fin (r + 1), ((j : ℕ) : ℝ)) * C := by
          rw [Finset.sum_mul]
    _ = (((r + 1 : ℕ) : ℝ) * (((r : ℝ) / 2) * C)) := by
      rw [hFin]
      ring

/-- Quantitative reverse-triangle estimate for a finite real-normed
Krylov-like family whose jth deviation is bounded by j C. No
orthogonality or unjustified pairwise positivity is required. -/
theorem p4Q2_finite_sum_norm_sq_ge_halfDepth
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℕ) (u : E) (v : Fin (r + 1) → E) (C : ℝ)
    (hNear : ∀ j : Fin (r + 1), ‖v j - u‖ ≤ ((j : ℕ) : ℝ) * C)
    (hMargin : 0 ≤ ‖u‖ - ((r : ℝ) / 2) * C) :
    (((r + 1 : ℕ) : ℝ) ^ 2) *
        (‖u‖ - ((r : ℝ) / 2) * C) ^ 2 ≤
      ‖∑ j : Fin (r + 1), v j‖ ^ 2 := by
  classical
  let N : ℝ := ((r + 1 : ℕ) : ℝ)
  let margin : ℝ := ‖u‖ - ((r : ℝ) / 2) * C
  have hN : 0 ≤ N := by
    dsimp [N]
    positivity
  have hError :
      ‖∑ j : Fin (r + 1), (v j - u)‖ ≤
        N * (((r : ℝ) / 2) * C) := by
    calc
      ‖∑ j : Fin (r + 1), (v j - u)‖ ≤
          ∑ j : Fin (r + 1), (((j : ℕ) : ℝ) * C) :=
            norm_sum_le_of_le Finset.univ (by
              intro j _hj
              exact hNear j)
      _ = N * (((r : ℝ) / 2) * C) := by
        simpa only [N] using p4Q2_fin_linear_error_sum_eq_halfDepth r C
  have hRelation :
      N • u = (∑ j : Fin (r + 1), v j) -
        (∑ j : Fin (r + 1), (v j - u)) := by
    dsimp [N]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_fin, Nat.cast_smul_eq_nsmul]
    abel
  have hReference :
      N * ‖u‖ ≤ ‖∑ j : Fin (r + 1), v j‖ +
        ‖∑ j : Fin (r + 1), (v j - u)‖ := by
    have h := norm_sub_le
      (∑ j : Fin (r + 1), v j)
      (∑ j : Fin (r + 1), (v j - u))
    rw [← hRelation] at h
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hN] using h
  have hLower :
      N * margin ≤ ‖∑ j : Fin (r + 1), v j‖ := by
    dsimp [margin]
    nlinarith [hReference, hError]
  have hNonneg : 0 ≤ N * margin :=
    mul_nonneg hN (by simpa only [margin] using hMargin)
  have hSquared :
      (N * margin) ^ 2 ≤ ‖∑ j : Fin (r + 1), v j‖ ^ 2 := by
    have hProduct :
        0 ≤ (‖∑ j : Fin (r + 1), v j‖ - N * margin) *
          (‖∑ j : Fin (r + 1), v j‖ + N * margin) :=
      mul_nonneg (sub_nonneg.mpr hLower)
        (add_nonneg (norm_nonneg _) hNonneg)
    nlinarith
  simpa only [N, margin, mul_pow] using hSquared

local instance p4QuantGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4QuantCompact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4QuantSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4QuantMeasurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4QuantBorel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4QuantSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Exact quantitative half-depth lower bound for the ORIGINAL
positive-fine Wilson posterior right-Gram, witnessed by one genuine
frozen Wilson spatial link. The margin must be nonnegative before
squaring the reverse-triangle estimate. -/
theorem fineRightKrylovPairHaarResidualGram_ones_rayleigh_ge_halfDepth
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ)
    (e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)))
    (hMargin :
      let H := halfExtent (n + 1)
      let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
      let gamma := originalWilsonPhysicalSignedInnovationHilbertCoefficient
        H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
      let B := physicalOriginalNormalizedTransferConstantStepBetaBudget
        H (beta (n + 1))
      0 ≤ ‖physicalOriginalReceiverPosteriorInnovation
        H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) e u‖ -
        ((r : ℝ) / 2) * (Real.sqrt gamma * B)) :
    let H := halfExtent (n + 1)
    let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
    let gamma := originalWilsonPhysicalSignedInnovationHilbertCoefficient
      H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
    let B := physicalOriginalNormalizedTransferConstantStepBetaBudget
      H (beta (n + 1))
    (((r + 1 : ℕ) : ℝ) ^ 2) *
      (‖physicalOriginalReceiverPosteriorInnovation
        H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) e u‖ -
        ((r : ℝ) / 2) * (Real.sqrt gamma * B)) ^ 2 ≤
      star (fun _ : Fin (r + 1) => (1 : ℝ)) ⬝ᵥ
        (Matrix.mulVec
          (fineRightKrylovPairHaarResidualGram
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r)
          (fun _ : Fin (r + 1) => (1 : ℝ))) := by
  classical
  let H := halfExtent (n + 1)
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let I := physicalOriginalReceiverPosteriorInnovation
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  let gamma := originalWilsonPhysicalSignedInnovationHilbertCoefficient
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  let B := physicalOriginalNormalizedTransferConstantStepBetaBudget H (beta (n + 1))
  let R : Fin (r + 1) →
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2 :=
    fun j => physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n (j : ℕ)
  let q : PeriodicHypercubicEvenSpatialSliceLink H → ℝ :=
    fun t => ‖∑ j : Fin (r + 1), I t (R j)‖ ^ 2
  have hNear : ∀ j : Fin (r + 1),
      ‖I e (R j) - I e u‖ ≤ ((j : ℕ) : ℝ) * (Real.sqrt gamma * B) := by
    intro j
    have hStep :
        ‖I e (R j) - I e u‖ ≤
          Real.sqrt gamma * (((j : ℕ) : ℝ) * B) :=
      fineRightKrylov_linkInnovation_sub_unit_norm_le_fineBudget
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n (j : ℕ) e
    calc
      ‖I e (R j) - I e u‖ ≤
          Real.sqrt gamma * (((j : ℕ) : ℝ) * B) := hStep
      _ = ((j : ℕ) : ℝ) * (Real.sqrt gamma * B) := by ring
  have hLink :
      (((r + 1 : ℕ) : ℝ) ^ 2) *
        (‖I e u‖ - ((r : ℝ) / 2) * (Real.sqrt gamma * B)) ^ 2 ≤
        ‖∑ j : Fin (r + 1), I e (R j)‖ ^ 2 :=
    p4Q2_finite_sum_norm_sq_ge_halfDepth
      r (I e u) (fun j : Fin (r + 1) => I e (R j))
      (Real.sqrt gamma * B) hNear hMargin
  have hWhole :
      ‖∑ j : Fin (r + 1), I e (R j)‖ ^ 2 ≤
        ∑ t : PeriodicHypercubicEvenSpatialSliceLink H, q t := by
    exact Finset.single_le_sum
      (fun t _ht => sq_nonneg _) (Finset.mem_univ e)
  have hRayleigh :
      star (fun _ : Fin (r + 1) => (1 : ℝ)) ⬝ᵥ
        (Matrix.mulVec
          (fineRightKrylovPairHaarResidualGram
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r)
          (fun _ : Fin (r + 1) => (1 : ℝ))) =
      ∑ t : PeriodicHypercubicEvenSpatialSliceLink H, q t := by
    simpa only [one_smul, q, I, R,
      physicalOriginalReceiverPosteriorInnovation] using
      (fineRightKrylovPairHaarResidualGram_rayleigh
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r (fun _ : Fin (r + 1) => (1 : ℝ)))
  change (((r + 1 : ℕ) : ℝ) ^ 2) *
    (‖I e u‖ - ((r : ℝ) / 2) * (Real.sqrt gamma * B)) ^ 2 ≤
      star (fun _ : Fin (r + 1) => (1 : ℝ)) ⬝ᵥ
        (Matrix.mulVec
          (fineRightKrylovPairHaarResidualGram
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r)
          (fun _ : Fin (r + 1) => (1 : ℝ)))
  exact (hLink.trans hWhole).trans_eq hRayleigh.symm

/-- The normalized original Wilson all-one Rayleigh is at least
(r+1) times the square of the true one-link margin. -/
theorem fineRightKrylovPairHaarResidualGram_ones_normalizedRayleigh_ge_halfDepth
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ)
    (e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)))
    (hMargin :
      let H := halfExtent (n + 1)
      let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
      let gamma := originalWilsonPhysicalSignedInnovationHilbertCoefficient
        H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
      let B := physicalOriginalNormalizedTransferConstantStepBetaBudget
        H (beta (n + 1))
      0 ≤ ‖physicalOriginalReceiverPosteriorInnovation
        H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) e u‖ -
        ((r : ℝ) / 2) * (Real.sqrt gamma * B)) :
    let H := halfExtent (n + 1)
    let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
    let gamma := originalWilsonPhysicalSignedInnovationHilbertCoefficient
      H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
    let B := physicalOriginalNormalizedTransferConstantStepBetaBudget
      H (beta (n + 1))
    (((r + 1 : ℕ) : ℝ)) *
      (‖physicalOriginalReceiverPosteriorInnovation
        H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) e u‖ -
        ((r : ℝ) / 2) * (Real.sqrt gamma * B)) ^ 2 ≤
      (star (fun _ : Fin (r + 1) => (1 : ℝ)) ⬝ᵥ
        (Matrix.mulVec
          (fineRightKrylovPairHaarResidualGram
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r)
          (fun _ : Fin (r + 1) => (1 : ℝ)))) /
        (∑ j : Fin (r + 1),
          ((fun _ : Fin (r + 1) => (1 : ℝ)) j) ^ 2) := by
  have hRaw :=
    fineRightKrylovPairHaarResidualGram_ones_rayleigh_ge_halfDepth
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e hMargin
  rw [fineRightKrylov_ones_coeff_sq_norm_eq]
  have hCard : 0 < (((r + 1 : ℕ) : ℝ)) := by positivity
  rw [le_div_iff₀ hCard]
  calc
    (((r + 1 : ℕ) : ℝ)) *
        (‖physicalOriginalReceiverPosteriorInnovation
          (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
          (beta n) (hbeta n) e
          (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector
            (halfExtent (n + 1)) 2)‖ -
          ((r : ℝ) / 2) *
            (Real.sqrt (originalWilsonPhysicalSignedInnovationHilbertCoefficient
              (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
              (beta n) (hbeta n)) *
              physicalOriginalNormalizedTransferConstantStepBetaBudget
                (halfExtent (n + 1)) (beta (n + 1)))) ^ 2 *
        (((r + 1 : ℕ) : ℝ)) =
      (((r + 1 : ℕ) : ℝ) ^ 2) *
        (‖physicalOriginalReceiverPosteriorInnovation
          (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
          (beta n) (hbeta n) e
          (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector
            (halfExtent (n + 1)) 2)‖ -
          ((r : ℝ) / 2) *
            (Real.sqrt (originalWilsonPhysicalSignedInnovationHilbertCoefficient
              (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
              (beta n) (hbeta n)) *
              physicalOriginalNormalizedTransferConstantStepBetaBudget
                (halfExtent (n + 1)) (beta (n + 1)))) ^ 2 := by ring
    _ ≤ _ := hRaw

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
