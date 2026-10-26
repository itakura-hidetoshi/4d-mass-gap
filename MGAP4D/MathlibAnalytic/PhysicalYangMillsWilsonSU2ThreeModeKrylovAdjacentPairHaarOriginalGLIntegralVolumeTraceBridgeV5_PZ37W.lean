import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGLIntegralDetTraceV5_PZ37V
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Tactic

/-!
# P4-Q2-PZ37W — volume-sensitive original Wilson GL/physical Gram comparison

The true original SU(2) Wilson two-posterior GL integral Gram B and the
genuine Gauss-law physical three-mode Hankel Gram P have the SAME coefficient
domain. PZ37U identifies their kernels at every finite depth and proves a
fixed-model positive two-sided norm comparison. HO and PB identify BOTH
quadratic forms exactly, without changing the physical/posterior models.

This module converts that result into a genuine 3-by-3 *matrix quadratic*
comparison, and extracts the previously unquantified trace behavior:

    c(H,b,t) trace P(H,t) <= trace B(H,b,t)
                           <= C(H,b,t) trace P(H,t).

The physical trace is exactly the original Wilson moment sum m0+m2+m4
(PZ37R). On the PZ37V finite-H small-positive-fine interval we obtain

  4 det(B)/(C trace(P))^2 <= 4 det(B)/trace(B)^2
                          <= 4 det(B)/(c trace(P))^2.

Thus the trace contribution to the TRUE GL spectral certificate is
explicitly related to original Wilson physical moments. The determinant
det(B), the comparison constants and the positive fine radius still
depend on H. FK/FL/GA local Haar estimates are not falsely promoted to
an unproved global three-mode frame or volume-uniform determinant bound.

No U0, endpoint, arbitrary-depth common fine interval, H1-H4 or continuum
Yang--Mills mass gap follows. No proxy, Dobrushin, new axiom, sorry/admit
or native_decide.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Matrix
open scoped ENNReal InnerProductSpace BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37W_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37W_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37W_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37W_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37W_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2PZ37W_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- An exact coordinate-vector identity for the full quadratic form;
no diagonal-matrix or coefficient-orthogonality assumption is used. -/
private theorem p4Q2PZ37W_finThree_single_quad
    (A : Matrix (Fin 3) (Fin 3) ℝ) (i : Fin 3) :
    star (Pi.single i (1 : ℝ)) ⬝ᵥ
        (A *ᵥ Pi.single i (1 : ℝ)) = A i i := by
  let a : Fin 3 → ℝ := Pi.single i 1
  change star a ⬝ᵥ (A *ᵥ a) = A i i
  have hStar : star a = a := by
    ext j
    simp [a]
  rw [hStar]
  simp only [a, single_one_dotProduct, Matrix.mulVec_apply, dotProduct_single_one]

/-- Quadratic domination on *all* three coefficients implies trace
domination with the SAME constants. This is pure matrix algebra and
does not assume the two matrices can be diagonalized simultaneously. -/
theorem p4Q2PZ37W_finThree_quadratic_compare_trace
    (P B : Matrix (Fin 3) (Fin 3) ℝ) (c C : ℝ)
    (hCmp : ∀ a : Fin 3 → ℝ,
      c * (star a ⬝ᵥ (P *ᵥ a)) ≤ star a ⬝ᵥ (B *ᵥ a) ∧
      star a ⬝ᵥ (B *ᵥ a) ≤ C * (star a ⬝ᵥ (P *ᵥ a))) :
    c * (P).trace ≤ B.trace ∧ B.trace ≤ C * (P).trace := by
  have hDiag (i : Fin 3) :
      c * P i i ≤ B i i ∧ B i i ≤ C * P i i := by
    simpa only [p4Q2PZ37W_finThree_single_quad] using
      hCmp (Pi.single i (1 : ℝ))
  have h0 := hDiag 0
  have h1 := hDiag 1
  have h2 := hDiag 2
  simp only [Matrix.trace_fin_three]
  constructor <;> nlinarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2]

section TrueOriginalGLGramVolume
variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ k, 0 ≤ beta k}
variable (n : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "Phys" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule Hn 2
local notation "U" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector Hn 2
local notation "Fine" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    Hn 2 specialUnitaryTwoWilsonRankPositive
    (beta (n + 1)) (hbeta (n + 1))
local notation "Krylov" =>
  (fun j : Fin 3 => ((Fine ^ (j : ℕ)) U : Phys))
local notation "Src" =>
  p4Q2HJ_actualRightPhysicalSourceSynthesis
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 2
local notation "P" =>
  p4Q2PD_originalWilsonThreeHankel
    Hn (beta (n + 1)) (hbeta (n + 1))
local notation "B" =>
  p4Q2HO_actualRightOriginalGLIntegralMatrix
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 2
local notation "Mass" =>
  p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
    Hn (beta n) (hbeta n)

/-- Genuine original GL integral and physical Wilson Hankel quadratic
forms satisfy a two-sided coefficient-space comparison for every
finite volume, all nonnegative fine couplings and positive frozen
coupling. The constants are MODEL-DEPENDENT, not uniform in H. -/
theorem p4Q2PZ37W_allFinite_allFine_originalGL_physicalGram_quadratic_compare
    (hFrozen : 0 < beta n) (e : Link) (left₀ : Cfg) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      ∀ a : Fin 3 → ℝ,
        c * (star a ⬝ᵥ (P *ᵥ a)) ≤
          star a ⬝ᵥ ((B hFrozen) *ᵥ a) ∧
        star a ⬝ᵥ ((B hFrozen) *ᵥ a) ≤
          C * (star a ⬝ᵥ (P *ᵥ a)) := by
  obtain ⟨c, C, hc, hcC, hCompare⟩ :=
    p4Q2PZ37U_allFinite_allDepth_originalPosteriorMass_physicalNorm_compare
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n 2 hFrozen e left₀
  refine ⟨c, C, hc, hcC, ?_⟩
  intro a
  have hSource : Src a = (p4Q2AD_realFiniteSynthesis Krylov) a := rfl
  have hGram : Matrix.gram ℝ Krylov = P := by
    simpa only [p4Q2PD_originalWilsonThreeHankel] using
      (p4Q2PB_originalWilsonPhysicalGram_eq_actualHankel
        Hn (beta (n + 1)) (hbeta (n + 1)) 2)
  have hPhys :
      star a ⬝ᵥ (P *ᵥ a) = ‖Src a‖ ^ 2 := by
    calc
      star a ⬝ᵥ (P *ᵥ a) =
          star a ⬝ᵥ ((Matrix.gram ℝ Krylov) *ᵥ a) := by rw [hGram]
      _ = ‖(p4Q2AD_realFiniteSynthesis Krylov) a‖ ^ 2 :=
        p4Q2PZ37T_realFiniteSynthesis_gram_quadratic_eq_normSq Krylov a
      _ = ‖Src a‖ ^ 2 := by rw [hSource]
  have hExact :
      star a ⬝ᵥ ((B hFrozen) *ᵥ a) =
        Mass (Src a) (Finset.univ : Finset Link) := by
    simpa only [p4Q2HJ_actualRightPhysicalSourceSynthesis] using
      (p4Q2HO_actualRightOriginalGLIntegralMatrix_quad_eq_originalGLMass
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n 2 hFrozen a)
  rw [hPhys, hExact]
  exact hCompare a

/-- The true GL INTEGRAL MATRIX trace, without a substitute detector,
is quantitatively sandwiched by the original Wilson physical moment
trace m0+m2+m4. Constants may depend on every finite physical model. -/
theorem p4Q2PZ37W_allFinite_allFine_originalGLIntegral_trace_physicalMoments
    (hFrozen : 0 < beta n) (e : Link) (left₀ : Cfg) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
      c * (P).trace ≤ (B hFrozen).trace ∧
      (B hFrozen).trace ≤ C * (P).trace := by
  obtain ⟨c, C, hc, hcC, hCmp⟩ :=
    p4Q2PZ37W_allFinite_allFine_originalGL_physicalGram_quadratic_compare
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e left₀
  exact ⟨c, C, hc, hcC,
    p4Q2PZ37W_finThree_quadratic_compare_trace P (B hFrozen) c C hCmp⟩

/-- The EXACT volume-sensitive determinant/trace coefficient is bounded
above and below using the original physical moment trace. This isolates
the still-uncontrolled volume dependence of det(B), c, C and delta_H.
No uniform determinant or U0 premise is assumed. -/
theorem p4Q2PZ37W_allFiniteSmallFine_originalGLIntegral_detTrace_momentSandwich
    (hFrozen : 0 < beta n) (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ delta : ℝ, 0 < delta ∧
      (0 < beta (n + 1) → beta (n + 1) < delta →
        ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
          0 < (P).trace ∧
          c * (P).trace ≤ (B hFrozen).trace ∧
          (B hFrozen).trace ≤ C * (P).trace ∧
          0 < (B hFrozen).det ∧
          (4 * (B hFrozen).det / ((C * (P).trace) ^ 2)) ≤
            4 * (B hFrozen).det / ((B hFrozen).trace ^ 2) ∧
          4 * (B hFrozen).det / ((B hFrozen).trace ^ 2) ≤
            4 * (B hFrozen).det / ((c * (P).trace) ^ 2)) := by
  obtain ⟨delta, hdelta, hDef⟩ :=
    p4Q2PZ37V_allFiniteSmallFine_originalGLIntegralGram_posDef
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e e' left₀ right₀
  refine ⟨delta, hdelta, ?_⟩
  intro hFine hSmall
  obtain ⟨c, C, hc, hcC, hTraceLo, hTraceHi⟩ :=
    p4Q2PZ37W_allFinite_allFine_originalGLIntegral_trace_physicalMoments
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e left₀
  have hPosDef : (B hFrozen).PosDef := hDef hFine hSmall
  have hBtrace : 0 < (B hFrozen).trace := hPosDef.trace_pos
  have hBdet : 0 < (B hFrozen).det := hPosDef.det_pos
  have hC : 0 < C := lt_of_lt_of_le hc hcC
  have hPtrace : 0 < (P).trace := by
    by_contra hNot
    have hNonpos : (P).trace ≤ 0 := le_of_not_gt hNot
    have hUpperNonpos : C * (P).trace ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hC.le hNonpos
    linarith
  have hcp : 0 < c * (P).trace := mul_pos hc hPtrace
  have hCp : 0 < C * (P).trace := mul_pos hC hPtrace
  have hLowerSq : (c * (P).trace) ^ 2 ≤ (B hFrozen).trace ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hTraceLo)
      (add_nonneg hcp.le hBtrace.le)]
  have hUpperSq : (B hFrozen).trace ^ 2 ≤ (C * (P).trace) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hTraceHi)
      (add_nonneg hCp.le hBtrace.le)]
  have hNum : 0 ≤ 4 * (B hFrozen).det :=
    (mul_pos (by norm_num) hBdet).le
  have hLower :
      (4 * (B hFrozen).det / ((C * (P).trace) ^ 2)) ≤
        4 * (B hFrozen).det / ((B hFrozen).trace ^ 2) :=
    (div_le_div_iff₀ (pow_pos hCp 2) (pow_pos hBtrace 2)).mpr
      (mul_le_mul_of_nonneg_left hUpperSq hNum)
  have hUpper :
      4 * (B hFrozen).det / ((B hFrozen).trace ^ 2) ≤
        4 * (B hFrozen).det / ((c * (P).trace) ^ 2) :=
    (div_le_div_iff₀ (pow_pos hBtrace 2) (pow_pos hcp 2)).mpr
      (mul_le_mul_of_nonneg_left hLowerSq hNum)
  exact ⟨c, C, hc, hcC, hPtrace, hTraceLo, hTraceHi, hBdet, hLower, hUpper⟩

end TrueOriginalGLGramVolume
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37W_finThree_quadratic_compare_trace
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37W_allFinite_allFine_originalGL_physicalGram_quadratic_compare
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37W_allFinite_allFine_originalGLIntegral_trace_physicalMoments
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37W_allFiniteSmallFine_originalGLIntegral_detTrace_momentSandwich
