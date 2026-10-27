import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalPhysicalTransverseFineTangentV5_PZ37ZT
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ZU — genuine rank-one Wilson top norm versus physical vacuum

At the actual finite-volume SU(2) Wilson fine-zero endpoint,
Raw_0 is exactly the physical Haar rank-one projection P=|U><U|.

First prove a generic real-Hilbert top-eigenvector lemma. If
R omega = ||R|| omega, ||omega||=||u||=1, and
epsilon = ||R-rankOne(u,u)|| <= 1/4, then
  0 <= ||R|| - <R u,u> <= 8 epsilon^2.
No eigenvector smoothness, differentiability of an operator norm,
or extra spectral assumption is required; the actual Wilson top
eigenvector exists by its previously proved positivity and compactness.

For the ORIGINAL physical raw Wilson R_t, the proved action-budget
Lipschitz bound ||R_t-R_0||<=B_H*t yields, on B_H*t<=1/4,
  0 <= ||R_t||-<R_t U,U> <= 8 (B_H*t)^2.

This is strictly finite-H, for the real original Haar/Gauss-law source.
It retains the exact Wilson transfer; no new axioms/sorry/admit/
native_decide, no fake source/posterior, no volume-uniform coercivity,
H1-H4 or 4D continuum Yang--Mills gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Elementary rank-one top-eigenvalue perturbation estimate for a
real Hilbert source. The norm gap is second order, with no derivative
of the spectral norm. -/
theorem p4Q2PZ37ZU_rankOne_topEigen_norm_gap_quadratic
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (R : E →L[ℝ] E) (u omega : E)
    (hu : ‖u‖ = 1) (homega : ‖omega‖ = 1)
    (hEig : R omega = ‖R‖ • omega)
    (hsmall : ‖R - InnerProductSpace.rankOne ℝ u u‖ ≤ (1 / 4 : ℝ)) :
    0 ≤ ‖R‖ - inner ℝ (R u) u ∧
      ‖R‖ - inner ℝ (R u) u ≤
        8 * ‖R - InnerProductSpace.rankOne ℝ u u‖^2 := by
  let P : E →L[ℝ] E := InnerProductSpace.rankOne ℝ u u
  let D : E →L[ℝ] E := R - P
  let eps : ℝ := ‖D‖
  let lam : ℝ := ‖R‖
  let c : ℝ := inner ℝ u omega
  let y : E := omega - c • u
  let r : ℝ := inner ℝ (R u) u
  have heps : 0 ≤ eps := norm_nonneg D
  have hepssmall : eps ≤ 1 / 4 := hsmall
  have hPnorm : ‖P‖ = (1 : ℝ) := by
    dsimp [P]
    rw [InnerProductSpace.norm_rankOne, hu]
    norm_num
  have hR : R = D + P := by
    dsimp [D]
    abel
  have hOpp : P - R = -D := by
    dsimp [D]
    abel
  have hDiffNorm : ‖P - R‖ = eps := by
    rw [hOpp, norm_neg]
  have hLamHigh : lam ≤ 1 + eps := by
    calc
      lam = ‖D + P‖ := by
        change ‖R‖ = ‖D + P‖
        rw [hR]
      _ ≤ ‖D‖ + ‖P‖ := norm_add_le D P
      _ = 1 + eps := by rw [hPnorm]; dsimp [eps]; ring
  have hLamLow : 1 - eps ≤ lam := by
    have hPbound : (1 : ℝ) ≤ eps + lam := by
      calc
        (1 : ℝ) = ‖P‖ := hPnorm.symm
        _ = ‖(P - R) + R‖ := by congr 1; abel
        _ ≤ ‖P - R‖ + ‖R‖ := norm_add_le (P - R) R
        _ = eps + lam := by rw [hDiffNorm]
    linarith
  have hLamHalf : (1 / 2 : ℝ) ≤ lam := by linarith
  have hLamNear : |1 - lam| ≤ eps := by
    apply abs_le.mpr
    constructor <;> linarith
  have hcNorm : |c| ≤ 1 := by
    simpa [c, hu, homega] using (abs_real_inner_le_norm u omega)
  have hPomega : P omega = c • u := by
    change (inner ℝ u omega) • u = c • u
    rfl
  have hPu : P u = u := by
    change (inner ℝ u u) • u = u
    rw [real_inner_self_eq_norm_sq, hu]
    norm_num
  have hPy : P y = 0 := by
    change P (omega - c • u) = 0
    rw [map_sub, map_smul, hPomega, hPu, sub_self]
  have hDy : D y = R y := by
    change (R - P) y = R y
    rw [ContinuousLinearMap.sub_apply, hPy, sub_zero]
  have hRomega : R omega = c • u + D omega := by
    have hD : D omega = R omega - P omega := rfl
    rw [hD, hPomega]
    abel
  have hROmegaNorm : ‖R omega‖ = lam := by
    rw [hEig, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg R),
      homega, mul_one]
  have hDomega : ‖D omega‖ ≤ eps := by
    calc
      ‖D omega‖ ≤ ‖D‖ * ‖omega‖ := D.le_opNorm omega
      _ = eps := by rw [homega, mul_one]
  have hPomegaNorm : ‖P omega‖ = |c| := by
    rw [hPomega, norm_smul, Real.norm_eq_abs, hu, mul_one]
  have hCAbsLower : (1 / 2 : ℝ) ≤ |c| := by
    have hStep : lam ≤ |c| + eps := by
      calc
        lam = ‖R omega‖ := hROmegaNorm.symm
        _ = ‖P omega + D omega‖ := congrArg norm hRomega
        _ ≤ ‖P omega‖ + ‖D omega‖ := norm_add_le _ _
        _ ≤ |c| + eps := by rw [hPomegaNorm]; linarith
    linarith
  have hEigScalar : lam • omega = c • u + D omega :=
    hEig.symm.trans hRomega
  have hLamY :
      lam • y = ((1 - lam) * c) • u + D omega := by
    calc
      lam • y = lam • omega - (lam * c) • u := by
        dsimp [y]
        rw [smul_sub, smul_smul]
      _ = (c • u + D omega) - (lam * c) • u := by rw [hEigScalar]
      _ = ((1 - lam) * c) • u + D omega := by module
  have hTerm :
      ‖((1 - lam) * c) • u‖ ≤ eps := by
    rw [norm_smul, Real.norm_eq_abs, hu, mul_one, abs_mul]
    calc
      |1 - lam| * |c| ≤ eps * |c| :=
        mul_le_mul_of_nonneg_right hLamNear (abs_nonneg _)
      _ ≤ eps * 1 := mul_le_mul_of_nonneg_left hcNorm heps
      _ = eps := mul_one eps
  have hLamYnorm : lam * ‖y‖ ≤ 2 * eps := by
    calc
      lam * ‖y‖ = ‖lam • y‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg R)]
      _ = ‖((1 - lam) * c) • u + D omega‖ := congrArg norm hLamY
      _ ≤ ‖((1 - lam) * c) • u‖ + ‖D omega‖ := norm_add_le _ _
      _ ≤ eps + eps := add_le_add hTerm hDomega
      _ = 2 * eps := by ring
  have hyNorm : ‖y‖ ≤ 4 * eps := by
    have hLeft : (1 / 2 : ℝ) * ‖y‖ ≤ lam * ‖y‖ :=
      mul_le_mul_of_nonneg_right hLamHalf (norm_nonneg y)
    linarith
  have hOmegaDecomp : omega = c • u + y := by
    dsimp [y]
    abel
  have hRdecomp : R omega = c • R u + D y := by
    calc
      R omega = R (c • u + y) := by rw [← hOmegaDecomp]
      _ = c • R u + R y := by rw [map_add, map_smul]
      _ = c • R u + D y := by rw [hDy]
  have hEigInner : inner ℝ (R omega) u = lam * c := by
    rw [hEig, real_inner_smul_left]
    change lam * inner ℝ omega u = lam * c
    rw [real_inner_comm u omega]
  have hDecompInner :
      inner ℝ (R omega) u = c * r + inner ℝ (D y) u := by
    rw [hRdecomp, inner_add_left, real_inner_smul_left]
  have hScalar : c * (lam - r) = inner ℝ (D y) u := by
    nlinarith [hEigInner, hDecompInner]
  have hrLe : r ≤ lam := by
    calc
      r = inner ℝ (R u) u := rfl
      _ ≤ ‖R u‖ * ‖u‖ := real_inner_le_norm _ _
      _ ≤ (lam * ‖u‖) * ‖u‖ :=
        mul_le_mul_of_nonneg_right (R.le_opNorm u) (norm_nonneg u)
      _ = lam := by rw [hu]; ring
  have hDiffNonneg : 0 ≤ lam - r := sub_nonneg.mpr hrLe
  have hInnerBound : |inner ℝ (D y) u| ≤ eps * ‖y‖ := by
    calc
      |inner ℝ (D y) u| ≤ ‖D y‖ * ‖u‖ :=
        abs_real_inner_le_norm (D y) u
      _ = ‖D y‖ := by rw [hu, mul_one]
      _ ≤ ‖D‖ * ‖y‖ := D.le_opNorm y
      _ = eps * ‖y‖ := rfl
  have hHalfDiff : (1 / 2 : ℝ) * (lam - r) ≤ eps * ‖y‖ := by
    calc
      (1 / 2 : ℝ) * (lam - r) ≤ |c| * (lam - r) :=
        mul_le_mul_of_nonneg_right hCAbsLower hDiffNonneg
      _ = |c * (lam - r)| := by
        rw [abs_mul, abs_of_nonneg hDiffNonneg]
      _ = |inner ℝ (D y) u| := by rw [hScalar]
      _ ≤ eps * ‖y‖ := hInnerBound
  have hScaled : eps * ‖y‖ ≤ eps * (4 * eps) :=
    mul_le_mul_of_nonneg_left hyNorm heps
  constructor
  · exact hDiffNonneg
  · change lam - r ≤ 8 * eps^2
    nlinarith [hHalfDiff, hScaled]

local instance p4Q2PZ37ZU_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ZU_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ZU_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ZU_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ZU_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- Actual positive compact SU(2) Wilson transfer at true nonnegative
fine, with its original Haar vacuum and strict action budget. -/
theorem p4Q2PZ37ZU_originalPhysicalRawTopNorm_vacuum_gap_quadratic
    (H : ℕ) (t : Set.Ici (0 : ℝ))
    (hBudget : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
      (t : ℝ) ≤ (1 / 4 : ℝ)) :
    0 ≤
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 specialUnitaryTwoWilsonRankPositive (t : ℝ) t.property‖ -
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H 2 specialUnitaryTwoWilsonRankPositive (t : ℝ) t.property
          (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2))
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2) ∧
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 specialUnitaryTwoWilsonRankPositive (t : ℝ) t.property‖ -
      inner ℝ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H 2 specialUnitaryTwoWilsonRankPositive (t : ℝ) t.property
          (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2))
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2) ≤
      8 * (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
        (t : ℝ))^2 := by
  let Phys :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
  let U : Phys :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let R : Phys →L[ℝ] Phys :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H 2 specialUnitaryTwoWilsonRankPositive (t : ℝ) t.property
  let R0 : Phys →L[ℝ] Phys :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H 2 specialUnitaryTwoWilsonRankPositive 0 (by norm_num)
  let P : Phys →L[ℝ] Phys := InnerProductSpace.rankOne ℝ U U
  let B : ℝ := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  let omega : Phys :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector
      H 2 specialUnitaryTwoWilsonRankPositive (t : ℝ) t.property
  have hP : R0 = P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_zero_eq_rankOne
      H 2 specialUnitaryTwoWilsonRankPositive
  have hDist : ‖R - P‖ ≤ B * (t : ℝ) := by
    rw [← hP]
    exact periodicHypercubicEvenSpecialUnitaryPhysicalRawWilson_norm_sub_betaZero_le_actionBudget
      H 2 specialUnitaryTwoWilsonRankPositive (t : ℝ) t.property
  have hSmall : ‖R - P‖ ≤ (1 / 4 : ℝ) := hDist.trans hBudget
  have hU : ‖U‖ = 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_norm H 2
  have hOmega : ‖omega‖ = 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_norm
      H 2 specialUnitaryTwoWilsonRankPositive (t : ℝ) t.property
  have hEig : R omega = ‖R‖ • omega :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenvector_eigen
      H 2 specialUnitaryTwoWilsonRankPositive (t : ℝ) t.property
  obtain ⟨hNonneg, hBound⟩ :=
    p4Q2PZ37ZU_rankOne_topEigen_norm_gap_quadratic
      R U omega hU hOmega hEig hSmall
  have hSquare :
      ‖R - P‖^2 ≤ (B * (t : ℝ))^2 := by
    have hright : 0 ≤ B * (t : ℝ) :=
      (norm_nonneg (R - P)).trans hDist
    nlinarith [mul_nonneg (sub_nonneg.mpr hDist)
      (add_nonneg hright (norm_nonneg (R - P)))]
  constructor
  · exact hNonneg
  · exact hBound.trans (mul_le_mul_of_nonneg_left hSquare (by norm_num))

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37ZU_rankOne_topEigen_norm_gap_quadratic
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ZU_originalPhysicalRawTopNorm_vacuum_gap_quadratic
