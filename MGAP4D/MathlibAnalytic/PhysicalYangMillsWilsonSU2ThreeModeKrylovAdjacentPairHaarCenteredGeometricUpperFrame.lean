import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGramTopNormalizedNoUniformFrame
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarResidualGramLinearCombination
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# P4-Q2-AB: genuine Wilson centered-coefficient geometric upper frame

The ORIGINAL positive-fine normalized Wilson Krylov family has the
full-link frozen posterior signed innovations V_j and full top signal U:
  ‖V_j - U‖ <= C q^j,   0 <= q < 1.

For real coefficient vectors with sum a_j = 0, the common uncentered
top component CANCELS exactly:
  sum_j a_j V_j = sum_j a_j (V_j-U).

The pointwise coefficient inequality |a_j| <= sqrt(sum_i a_i²)
and the genuine finite geometric series bound show
  ‖sum_j a_j V_j‖ <= (C/(1-q)) sqrt(sum_j a_j²).

Thus the ORIGINAL Wilson full-link posterior right Gram obeys the
Krylov-depth UNIFORM UPPER bound on the centered coefficient hyperplane:
  aᵀ G_original(n,r) a <= (C/(1-q))² sum_j a_j².

C and q depend on the actual finite volume and both physical Wilson
couplings. This is NOT an uncentered upper frame, a uniform-in-volume
estimate, an all-coefficient lower coercive frame, or continuum mass gap.
No proxy receiver, altered posterior law, new axiom, sorry or admit.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 850000

/-- A single finite coefficient absolute value is bounded by the
actual coefficient Euclidean norm, without requiring a maximal index. -/
theorem p4Q2AB_abs_coefficient_le_sqrt_sum_sq
    (r : ℕ) (a : Fin (r + 1) → ℝ) (j : Fin (r + 1)) :
    |a j| ≤ Real.sqrt (∑ i : Fin (r + 1), (a i) ^ 2) := by
  have hSingle : (a j) ^ 2 ≤ ∑ i : Fin (r + 1), (a i) ^ 2 :=
    Finset.single_le_sum
      (fun i _hi => sq_nonneg (a i)) (Finset.mem_univ j)
  have hRoot := Real.sqrt_le_sqrt hSingle
  rw [Real.sqrt_sq_eq_abs] at hRoot
  exact hRoot

/-- Generic centered scalar coefficients cancel a common top vector.
Any normed real vector space is enough: no positivity or orthogonality
of the original posterior link innovations is introduced. -/
theorem p4Q2AB_centered_geometric_sum_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℕ) (u : E) (v : Fin (r + 1) → E)
    (a : Fin (r + 1) → ℝ)
    (q C : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hC : 0 ≤ C)
    (hCenter : (∑ j : Fin (r + 1), a j) = 0)
    (hNear : ∀ j : Fin (r + 1), ‖v j-u‖ ≤ C*q ^ (j : ℕ)) :
    ‖∑ j : Fin (r + 1), a j • v j‖ ≤
      Real.sqrt (∑ j : Fin (r + 1), (a j) ^ 2) * (C / (1-q)) := by
  classical
  let A : ℝ := Real.sqrt (∑ j : Fin (r + 1), (a j) ^ 2)
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hNearWeighted (j : Fin (r + 1)) :
      ‖a j • (v j-u)‖ ≤ (A*C)*q ^ (j : ℕ) := by
    have hAbs : |a j| ≤ A :=
      p4Q2AB_abs_coefficient_le_sqrt_sum_sq r a j
    calc
      ‖a j • (v j-u)‖ = |a j| * ‖v j-u‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      _ ≤ |a j| * (C*q ^ (j : ℕ)) :=
        mul_le_mul_of_nonneg_left (hNear j) (abs_nonneg _)
      _ ≤ A*(C*q ^ (j : ℕ)) :=
        mul_le_mul_of_nonneg_right hAbs
          (mul_nonneg hC (pow_nonneg hq0 _))
      _ = (A*C)*q ^ (j : ℕ) := by ring
  have hCancel : (∑ j : Fin (r + 1), a j • u) = 0 := by
    rw [← Finset.sum_smul, hCenter, zero_smul]
  have hRel :
      (∑ j : Fin (r + 1), a j • (v j-u)) =
      (∑ j : Fin (r + 1), a j • v j) := by
    calc
      (∑ j : Fin (r + 1), a j • (v j-u)) =
          (∑ j : Fin (r + 1), a j • v j) -
            (∑ j : Fin (r + 1), a j • u) := by
        simp only [smul_sub, Finset.sum_sub_distrib]
      _ = (∑ j : Fin (r + 1), a j • v j) := by
        rw [hCancel, sub_zero]
  have hWeightedNear :
      ∀ j : Fin (r + 1),
        ‖a j • (v j-u) - (0 : E)‖ ≤ (A*C)*q ^ (j : ℕ) := by
    intro j
    simpa only [sub_zero] using hNearWeighted j
  have hWeighted :
      ‖∑ j : Fin (r + 1), a j • (v j-u)‖ ≤
        (A*C)/(1-q) := by
    have h :=
      p4Q2AA_finite_geometric_sum_error_le
        r (0 : E) (fun j : Fin (r+1) => a j • (v j-u))
        q (A*C) hq0 hq1 (mul_nonneg hA hC) hWeightedNear
    simpa only [smul_zero, sub_zero] using h
  calc
    ‖∑ j : Fin (r + 1), a j • v j‖ =
        ‖∑ j : Fin (r + 1), a j • (v j-u)‖ := by
      rw [hRel]
    _ ≤ (A*C)/(1-q) := hWeighted
    _ = A*(C/(1-q)) := by ring

/-- The generic centered finite-family upper FRAME (squared-norm)
bound is independent of the number r+1 of Krylov coefficients. -/
theorem p4Q2AB_centered_geometric_sum_norm_sq_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℕ) (u : E) (v : Fin (r + 1) → E)
    (a : Fin (r + 1) → ℝ)
    (q C : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hC : 0 ≤ C)
    (hCenter : (∑ j : Fin (r + 1), a j) = 0)
    (hNear : ∀ j : Fin (r + 1), ‖v j-u‖ ≤ C*q ^ (j : ℕ)) :
    ‖∑ j : Fin (r + 1), a j • v j‖ ^ 2 ≤
      (C/(1-q)) ^ 2 *
        (∑ j : Fin (r + 1), (a j) ^ 2) := by
  let A : ℝ := Real.sqrt (∑ j : Fin (r + 1), (a j) ^ 2)
  let M : ℝ := C/(1-q)
  have hSquares : 0 ≤ ∑ j : Fin (r + 1), (a j) ^ 2 :=
    Finset.sum_nonneg (fun j _ => sq_nonneg (a j))
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hM : 0 ≤ M := div_nonneg hC (le_of_lt (sub_pos.mpr hq1))
  have hBound : ‖∑ j : Fin (r + 1), a j • v j‖ ≤ A*M :=
    p4Q2AB_centered_geometric_sum_norm_le
      r u v a q C hq0 hq1 hC hCenter hNear
  have hFactor :
      0 ≤ (A*M - ‖∑ j : Fin (r+1), a j • v j‖) *
           (A*M + ‖∑ j : Fin (r+1), a j • v j‖) :=
    mul_nonneg (sub_nonneg.mpr hBound)
      (add_nonneg (mul_nonneg hA hM) (norm_nonneg _))
  have hSquare :
      ‖∑ j : Fin (r+1), a j • v j‖ ^ 2 ≤ (A*M)^2 := by
    nlinarith [hFactor]
  have hRoot :
      A ^ 2 = ∑ j : Fin (r + 1), (a j) ^ 2 := by
    dsimp [A]
    exact Real.sq_sqrt hSquares
  calc
    ‖∑ j : Fin (r+1), a j • v j‖ ^ 2 ≤ (A*M)^2 := hSquare
    _ = M^2 * A^2 := by ring
    _ = (C/(1-q))^2 * (∑ j : Fin (r+1), (a j)^2) := by
      rw [hRoot]

local instance p4ABGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4ABCompact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4ABSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4ABMeasurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4ABBorel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4ABLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _
local instance p4ABComplete (H : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    H 2).completeSpace_coe

namespace GroundStatePosteriorJoint

/-- Exact ORIGINAL Wilson frozen posterior right Gram Rayleigh identity
for EVERY finite REAL coefficient vector, assembled in the genuine
all-spatial-link PiLp 2 direct sum. It extends AA2's all-one identity. -/
theorem fineRightKrylovPairHaarResidualGram_rayleigh_eq_fullLinkWeightedSum_sq
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ k, 0 ≤ beta k}
    (n r : ℕ) (a : Fin (r+1) → ℝ) :
    let H := halfExtent (n+1)
    let I := physicalOriginalReceiverPosteriorInnovation
      H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
    let V (j : Fin (r+1)) := WithLp.toLp 2
      (fun e : PeriodicHypercubicEvenSpatialSliceLink H =>
        I e (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n (j : ℕ)))
    star a ⬝ᵥ (Matrix.mulVec
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a) =
      ‖∑ j : Fin (r+1), a j • V j‖ ^ 2 := by
  classical
  let H := halfExtent (n+1)
  let Link := PeriodicHypercubicEvenSpatialSliceLink H
  let I := physicalOriginalReceiverPosteriorInnovation
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  let R (j : Fin (r+1)) :=
    physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n (j : ℕ)
  let V (j : Fin (r+1)) := WithLp.toLp 2 (fun e : Link => I e (R j))
  have hCoordSumFinset (s : Finset (Fin (r+1))) (e : Link) :
      (∑ j ∈ s, a j • V j) e =
        ∑ j ∈ s, a j • I e (R j) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih =>
        simp only [Finset.sum_insert hj, PiLp.add_apply]
        change a j • I e (R j) + (∑ k ∈ s, a k • V k) e =
          a j • I e (R j) + ∑ k ∈ s, a k • I e (R k)
        rw [ih]
  have hCoordSum (e : Link) :
      (∑ j : Fin (r+1), a j • V j) e =
        ∑ j : Fin (r+1), a j • I e (R j) :=
    hCoordSumFinset Finset.univ e
  have hDirectSum :
      ‖∑ j : Fin (r+1), a j • V j‖ ^ 2 =
        ∑ e : Link, ‖∑ j : Fin (r+1), a j • I e (R j)‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [hCoordSum]
  change star a ⬝ᵥ (Matrix.mulVec
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a) = ‖∑ j : Fin (r+1), a j • V j‖ ^ 2
  rw [hDirectSum]
  simpa only [I, R, physicalOriginalReceiverPosteriorInnovation] using
    (fineRightKrylovPairHaarResidualGram_rayleigh
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a)

/-- Authentic Wilson positive-fine ORIGINAL frozen posterior Gram has
a Krylov-depth UNIFORM upper Rayleigh bound on the centered coefficient
hyperplane sum_j a_j=0. The physical coefficient depends on finite
volume and frozen/fine beta, but NOT the Krylov depth r. -/
theorem fineRightKrylovPairHaarResidualGram_centered_upperRayleigh_geometric
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ k, 0 ≤ beta k}
    (n r : ℕ) (a : Fin (r+1) → ℝ)
    (hCenter : (∑ j : Fin (r+1), a j) = 0) :
    let H := halfExtent (n+1)
    let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H 2 specialUnitaryTwoWilsonRankPositive (beta (n+1)) (hbeta (n+1))
    let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
      H 2 specialUnitaryTwoWilsonRankPositive (beta (n+1)) (hbeta (n+1))
    let gamma := originalWilsonPhysicalSignedInnovationHilbertCoefficient
      H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
    let B := physicalOriginalNormalizedTransferConstantStepBetaBudget H (beta (n+1))
    let L : ℝ := (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ)
    let C := (Real.sqrt gamma*B)*Real.sqrt L+Real.sqrt gamma*Real.sqrt L
    star a ⬝ᵥ (Matrix.mulVec
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a) ≤
      (C/(1-‖S-P‖))^2 * (∑ j : Fin (r+1), (a j)^2) := by
  let H := halfExtent (n+1)
  let Link := PeriodicHypercubicEvenSpatialSliceLink H
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive (beta (n+1)) (hbeta (n+1))
  let P := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopSpectralProjection
    H 2 specialUnitaryTwoWilsonRankPositive (beta (n+1)) (hbeta (n+1))
  let I := physicalOriginalReceiverPosteriorInnovation
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let gamma := originalWilsonPhysicalSignedInnovationHilbertCoefficient
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  let B := physicalOriginalNormalizedTransferConstantStepBetaBudget H (beta (n+1))
  let L : ℝ := (Fintype.card Link : ℝ)
  let C : ℝ := (Real.sqrt gamma*B)*Real.sqrt L + Real.sqrt gamma*Real.sqrt L
  let U := WithLp.toLp 2 (fun e : Link => I e (P u))
  let V (j : Fin (r+1)) := WithLp.toLp 2
    (fun e : Link => I e (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n (j : ℕ)))
  have hq : ‖S-P‖ < 1 :=
    physicalOriginalNormalizedFineTransfer_sub_topSpectralProjection_norm_lt_one
      H (beta (n+1)) (hbeta (n+1))
  have hB : 0 ≤ B :=
    physicalOriginalNormalizedTransferConstantStepBetaBudget_nonneg
      H (beta (n+1)) (hbeta (n+1))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hNear :
      ∀ j : Fin (r+1), ‖V j-U‖ ≤ C*‖S-P‖ ^ (j : ℕ) := by
    intro j
    exact fineRightKrylov_originalPosteriorFullLink_sub_topProjection_norm_le_geometric_allDepth
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n (j : ℕ)
  have hBound :
      ‖∑ j : Fin (r+1), a j • V j‖ ^ 2 ≤
        (C/(1-‖S-P‖))^2 * (∑ j : Fin (r+1), (a j)^2) :=
    p4Q2AB_centered_geometric_sum_norm_sq_le
      r U V a ‖S-P‖ C (norm_nonneg (S-P)) hq hC hCenter hNear
  have hGram :=
    fineRightKrylovPairHaarResidualGram_rayleigh_eq_fullLinkWeightedSum_sq
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  change star a ⬝ᵥ (Matrix.mulVec
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r) a) ≤
      (C/(1-‖S-P‖))^2 * (∑ j : Fin (r+1), (a j)^2)
  rw [hGram]
  exact hBound

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
