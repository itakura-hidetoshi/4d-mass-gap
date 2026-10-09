import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarAnyFineZeroModePositive
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarFineRightExplicitTwoCouplingBeta
import Mathlib.Tactic

/-!
# P4-Q2-N: real physical finite-depth all-one Rayleigh stability at small fine beta

P4-Q2-J/M supplies a positive original frozen Wilson posterior
innovation at one genuine link for positive frozen beta. For the
ACTUAL fine normalized Wilson transfer, its jth Krylov image of
the constant unit differs in physical Haar L2 norm by at most
j times the already proved finite-H fine beta step budget.

Combining the genuine signed one-link innovation Hilbert bound with
a normed-space finite-sum ball argument gives a finite-depth
small-fine-coupling condition under which the entire all-one
coefficient Rayleigh of the ORIGINAL posterior Gram is strictly
positive. The frozen beta(n) and fine beta(n+1) remain independent.

This theorem has an explicit r, H, frozen-beta-dependent smallness
condition, NOT a depth-uniform statement, not a positive mass gap,
and it introduces no surrogate joint law, Dobrushin hypothesis,
sorry/admit or new axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

/-- A finite collection lying within distance b < ‖u‖ of a common
nonzero reference u cannot sum to zero. The proof keeps the genuine
norm of the finite sum; it assumes neither orthogonality nor positive
pairwise inner products. -/
theorem p4Q2_finite_sum_ne_zero_of_uniform_norm_sub_lt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℕ) (u : E) (v : Fin (r + 1) → E) (b : ℝ)
    (hsmall : b < ‖u‖)
    (hnear : ∀ j : Fin (r + 1), ‖v j - u‖ ≤ b) :
    (∑ j : Fin (r + 1), v j) ≠ 0 := by
  classical
  have hBound :
      ‖∑ j : Fin (r + 1), (v j - u)‖ ≤ ((r + 1 : ℕ) : ℝ) * b := by
    calc
      ‖∑ j : Fin (r + 1), (v j - u)‖ ≤
          ∑ _j : Fin (r + 1), b := by
        exact norm_sum_le_of_le Finset.univ (by
          intro j _hj
          exact hnear j)
      _ = ((r + 1 : ℕ) : ℝ) * b := by simp
  intro hzero
  have hRef :
      (∑ j : Fin (r + 1), (v j - u)) =
        -(((r + 1 : ℕ) : ℝ) • u) := by
    rw [Finset.sum_sub_distrib, hzero]
    simp [nsmul_eq_smul_cast]
  have hCard : (0 : ℝ) < ((r + 1 : ℕ) : ℝ) := by positivity
  have hLe : ((r + 1 : ℕ) : ℝ) * ‖u‖ ≤ ((r + 1 : ℕ) : ℝ) * b := by
    calc
      ((r + 1 : ℕ) : ℝ) * ‖u‖ =
          ‖-(((r + 1 : ℕ) : ℝ) • u)‖ := by
            simp [norm_smul, Real.norm_eq_abs, abs_of_pos hCard]
      _ = ‖∑ j : Fin (r + 1), (v j - u)‖ :=
        congrArg norm hRef.symm
      _ ≤ ((r + 1 : ℕ) : ℝ) * b := hBound
  exact (not_le_of_gt (mul_lt_mul_of_pos_left hsmall hCard)) hLe

local instance p4FineStabilityTopologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4FineStabilityCompactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4FineStabilitySecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4FineStabilityMeasurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4FineStabilityBorelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4FineStabilitySpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Every genuine fine-right Krylov mode's signed FROZEN link
innovation differs from the constant-unit innovation by an
explicit finite-H O(j beta_fine) bound. The original posterior
projection and physical transfer normalization are unchanged. -/
theorem fineRightKrylov_linkInnovation_sub_unit_norm_le_fineBudget
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (n j : ℕ)
    (e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1))) :
    let H := halfExtent (n + 1)
    let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
    let I := physicalOriginalReceiverPosteriorInnovation
      H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
    let gamma := originalWilsonPhysicalSignedInnovationHilbertCoefficient
      H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
    let B := physicalOriginalNormalizedTransferConstantStepBetaBudget
      H (beta (n + 1))
    ‖I e (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n j) - I e u‖ ≤ Real.sqrt gamma * ((j : ℝ) * B) := by
  let H := halfExtent (n + 1)
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let I := physicalOriginalReceiverPosteriorInnovation
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  let gamma := originalWilsonPhysicalSignedInnovationHilbertCoefficient
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  let B := physicalOriginalNormalizedTransferConstantStepBetaBudget
    H (beta (n + 1))
  let R := physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n j
  have hStep :=
    normalizedPhysicalOneSlabTransfer_constantUnit_stepDefect_le_beta
      H 2 specialUnitaryTwoWilsonRankPositive (beta (n + 1)) (hbeta (n + 1))
  have hDepth :=
    fineRightFactor_norm_sub_constant_le_depth_stepDefect
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n j
  have hInput : ‖R - u‖ ≤ (j : ℝ) * B := by
    exact hDepth.trans (mul_le_mul_of_nonneg_left hStep (Nat.cast_nonneg j))
  have hHilbert :=
    physicalOriginalReceiverPosteriorInnovation_norm_le_sqrt_signedHilbert
      H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) e (R - u)
  have hSq : 0 ≤ Real.sqrt gamma := Real.sqrt_nonneg _
  change ‖I e R - I e u‖ ≤ Real.sqrt gamma * ((j : ℝ) * B)
  calc
    ‖I e R - I e u‖ = ‖I e (R - u)‖ := by
      rw [physicalOriginalReceiverPosteriorInnovation_sub]
    _ ≤ Real.sqrt gamma * ‖R - u‖ := hHilbert
    _ ≤ Real.sqrt gamma * ((j : ℝ) * B) :=
      mul_le_mul_of_nonneg_left hInput hSq

/-- The genuine all-one original Wilson right Gram Rayleigh is
strictly positive at positive fine beta whenever the EXPLICIT
original finite-volume fine-step budget is below the selected
physical frozen-link innovation radius.

No beta_fine=0 assumption appears. No sign cancellation of
the physically signed Krylov inputs is silently suppressed. -/
theorem fineRightKrylovPairHaarResidualGram_ones_rayleigh_pos_of_fineBudget_small
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
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
    0 < star (fun _ : Fin (r + 1) => (1 : ℝ)) ⬝ᵥ
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
  let B := physicalOriginalNormalizedTransferConstantStepBetaBudget
    H (beta (n + 1))
  let R : Fin (r + 1) →
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2 :=
    fun j => physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n (j : ℕ)
  let q : PeriodicHypercubicEvenSpatialSliceLink H → ℝ :=
    fun t => ‖∑ j : Fin (r + 1), I t (R j)‖ ^ 2
  have hB : 0 ≤ B :=
    physicalOriginalNormalizedTransferConstantStepBetaBudget_nonneg
      H (beta (n + 1)) (hbeta (n + 1))
  have hNear : ∀ j : Fin (r + 1),
      ‖I e (R j) - I e u‖ ≤ Real.sqrt gamma * ((r : ℝ) * B) := by
    intro j
    have hStep :=
      fineRightKrylov_linkInnovation_sub_unit_norm_le_fineBudget
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n (j : ℕ) e
    have hj : ((j : ℕ) : ℝ) ≤ (r : ℝ) := by
      exact_mod_cast (Nat.lt_succ_iff.mp j.isLt)
    have hmul : ((j : ℕ) : ℝ) * B ≤ (r : ℝ) * B :=
      mul_le_mul_of_nonneg_right hj hB
    exact hStep.trans
      (mul_le_mul_of_nonneg_left hmul (Real.sqrt_nonneg _))
  have hSumNe : (∑ j : Fin (r + 1), I e (R j)) ≠ 0 :=
    p4Q2_finite_sum_ne_zero_of_uniform_norm_sub_lt
      r (I e u) (fun j : Fin (r + 1) => I e (R j))
      (Real.sqrt gamma * ((r : ℝ) * B)) hSmall hNear
  have hSumEq :
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
  have hNonneg : 0 ≤ ∑ t : PeriodicHypercubicEvenSpatialSliceLink H, q t :=
    Finset.sum_nonneg (fun t _ht => sq_nonneg _)
  have hNe : (∑ t : PeriodicHypercubicEvenSpatialSliceLink H, q t) ≠ 0 := by
    intro hzero
    have ht : q e = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (s := Finset.univ) (f := q)
        (by intro t _ht; exact sq_nonneg _)).mp hzero e (Finset.mem_univ e)
    have hn : ‖∑ j : Fin (r + 1), I e (R j)‖ = 0 := by
      change ‖∑ j : Fin (r + 1), I e (R j)‖ ^ 2 = 0 at ht
      nlinarith [norm_nonneg (∑ j : Fin (r + 1), I e (R j))]
    exact hSumNe (norm_eq_zero.mp hn)
  rw [hSumEq]
  exact lt_of_le_of_ne hNonneg (Ne.symm hNe)

/-- Every positive frozen coupling supplies a strictly positive
finite-depth stability threshold, constructed from a genuine
physical Wilson spatial-link innovation and not from a Wilson
vacuum surrogate. The small fine-step budget remains a separate
explicit inequality, not an assumed uniform-in-depth convergence. -/
theorem fineRightKrylovPairHaarResidualGram_ones_rayleigh_exists_fineBudget_threshold
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (hFrozen : 0 < beta n) :
    ∃ (e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)))
      (delta : ℝ), 0 < delta ∧
        (Real.sqrt (originalWilsonPhysicalSignedInnovationHilbertCoefficient
          (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
          (beta n) (hbeta n)) *
          ((r : ℝ) *
            physicalOriginalNormalizedTransferConstantStepBetaBudget
              (halfExtent (n + 1)) (beta (n + 1))) < delta →
        0 < star (fun _ : Fin (r + 1) => (1 : ℝ)) ⬝ᵥ
          (Matrix.mulVec
            (fineRightKrylovPairHaarResidualGram
              (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
              n r)
            (fun _ : Fin (r + 1) => (1 : ℝ)))) := by
  obtain ⟨e, he⟩ :=
    physicalOriginalUnitReceiver_exists_positive_link_norm_SU2
      (halfExtent (n + 1)) (beta n) hFrozen
  refine ⟨e, ‖physicalOriginalReceiverPosteriorInnovation
    (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
    (beta n) (hbeta n) e
    (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector
      (halfExtent (n + 1)) 2)‖, he, ?_⟩
  intro hsmall
  exact fineRightKrylovPairHaarResidualGram_ones_rayleigh_pos_of_fineBudget_small
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r e hsmall

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
