import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGLSharpD3DeterminantV5_PZ37Y
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic

/-!
# P4-Q2-PZ37Y — genuine Wilson physical D3 controls original GL integral determinant

This applies the sharp, finite-three Loewner determinant comparison to
the actual original SU(2) Wilson Gauss-law Hankel Gram P and the original
interacting-two-Wilson-posterior Haar GL detector matrix B.

At every finite H >= 0, with frozen coupling b>0 and sufficiently
small positive fine t, PZ37Q establishes the true moment determinant
D3(H,t)>0. PZ37W independently provides finite-model c,C>0 with
c P <= B <= C P in ALL real coefficient quadratic forms, while HO
identifies the quadratic form of B exactly with the unmodified original
posterior spatial GL mass.

Consequently,
  det(B) >= c^3 D3(H,t),
  gamma(B) >= 4 c^3 D3(H,t)/(C^2 (m0+m2+m4)^2) > 0
and this explicit certificate bounds the true GL mass of EVERY
three-mode coefficient vector.

The constants c,C and fine radius may depend on H and couplings.
Local FK/FL/GA Haar sensitivity does not make them H-uniform.
No U0, endpoint, common arbitrary-depth positive fine, H1-H4,
or continuum Yang--Mills mass gap is claimed.
No new axiom, sorry, admit, native_decide, Dobrushin, or proxy models.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Matrix
open scoped ENNReal InnerProductSpace BigOperators MatrixOrder
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37Y_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37Y_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37Y_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37Y_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37Y_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2PZ37Y_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

section OriginalGLPhysicalD3Sharp
variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ k, 0 ≤ beta k}
variable (n : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "P" =>
  p4Q2PD_originalWilsonThreeHankel
    Hn (beta (n + 1)) (hbeta (n + 1))
local notation "D3" =>
  p4Q2PD_originalWilsonThirdMomentGap
    Hn (beta (n + 1)) (hbeta (n + 1))
local notation "B" =>
  p4Q2HO_actualRightOriginalGLIntegralMatrix
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 2
local notation "Src" =>
  p4Q2HJ_actualRightPhysicalSourceSynthesis
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n 2
local notation "Mass" =>
  p4Q2GL_originalWilsonSignedGapSquareDivVarianceSpatialMass
    Hn (beta n) (hbeta n)

/-- No extra physical separation assumption: the original finite-H
Wilson third moment gap D3 and actual posterior GL integral Gram
satisfy the sharp Loewner determinant comparison. The same explicit
coefficient lower controls the genuine original posterior mass. -/
theorem p4Q2PZ37Y_allFiniteSmallFine_originalGLIntegral_sharpD3DetMass
    (hFrozen : 0 < beta n) (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ delta : ℝ, 0 < delta ∧
      (0 < beta (n + 1) → beta (n + 1) < delta →
        ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
          0 < D3 ∧
          c ^ 3 * D3 ≤ (B hFrozen).det ∧
          0 < (4 * (c ^ 3 * D3) / ((C * (P).trace) ^ 2)) ∧
          (4 * (c ^ 3 * D3) / ((C * (P).trace) ^ 2)) ≤
            4 * (B hFrozen).det / ((B hFrozen).trace ^ 2) ∧
          ∀ a : Fin 3 → ℝ,
            (4 * (c ^ 3 * D3) / ((C * (P).trace) ^ 2)) *
              (∑ j : Fin 3, (a j) ^ 2) ≤
              Mass (Src a) (Finset.univ : Finset Link)) := by
  obtain ⟨delta, hdelta, hThird⟩ :=
    p4Q2PZ37Q_allFiniteSmallFine_originalThirdSource_mass_and_signedGI
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e e' left₀ right₀
  refine ⟨delta, hdelta, ?_⟩
  intro hFine hSmall
  have hD3 : 0 < D3 := (hThird hFine hSmall).1
  obtain ⟨c, C, hc, hcC, hCmp⟩ :=
    p4Q2PZ37W_allFinite_allFine_originalGL_physicalGram_quadratic_compare
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e left₀
  have hPEq : (P).det = D3 :=
    p4Q2PD_originalWilsonThreeHankel_det_eq_gap
      Hn (beta (n + 1)) (hbeta (n + 1))
  have hPDet : 0 < (P).det := by rw [hPEq]; exact hD3
  have hPPSD : (P).PosSemidef :=
    p4Q2PZ37R_originalWilsonThreeHankel_posSemidef
      Hn (beta (n + 1)) (hbeta (n + 1))
  have hPDef : (P).PosDef :=
    (hPPSD.posDef_iff_det_ne_zero).mpr (ne_of_gt hPDet)
  have hBPSD : (B hFrozen).PosSemidef :=
    p4Q2HO_actualRightOriginalGLIntegralMatrix_posSemidef
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n 2 hFrozen
  have hSharp :
      c ^ 3 * (P).det ≤ (B hFrozen).det :=
    p4Q2PZ37Y_finThree_posDef_quadratic_det_mono
      P (B hFrozen) hPDef hBPSD c hc.le (fun a => (hCmp a).1)
  have hSharpD3 : c ^ 3 * D3 ≤ (B hFrozen).det := by
    rw [← hPEq]
    exact hSharp
  have hBDet : 0 < (B hFrozen).det :=
    lt_of_lt_of_le (mul_pos (pow_pos hc 3) hD3) hSharpD3
  have hBDef : (B hFrozen).PosDef :=
    (hBPSD.posDef_iff_det_ne_zero).mpr (ne_of_gt hBDet)
  have hPTrace : 0 < (P).trace := hPDef.trace_pos
  have hBTrace : 0 < (B hFrozen).trace := hBDef.trace_pos
  obtain ⟨_hTraceLo, hTraceHi⟩ :=
    p4Q2PZ37W_finThree_quadratic_compare_trace
      P (B hFrozen) c C hCmp
  have hC : 0 < C := lt_of_lt_of_le hc hcC
  have hDen : 0 < C * (P).trace := mul_pos hC hPTrace
  have hNumer : 0 < 4 * (c ^ 3 * D3) :=
    mul_pos (by norm_num) (mul_pos (pow_pos hc 3) hD3)
  have hDenSq :
      (B hFrozen).trace ^ 2 ≤ (C * (P).trace) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hTraceHi)
      (add_nonneg hDen.le hBTrace.le)]
  have hScaledDet :
      4 * (c ^ 3 * D3) ≤ 4 * (B hFrozen).det :=
    mul_le_mul_of_nonneg_left hSharpD3 (by norm_num)
  have hRatioDet :
      4 * (c ^ 3 * D3) / ((C * (P).trace) ^ 2) ≤
        4 * (B hFrozen).det / ((C * (P).trace) ^ 2) :=
    (div_le_div_iff₀ (pow_pos hDen 2) (pow_pos hDen 2)).mpr
      (mul_le_mul_of_nonneg_right hScaledDet (pow_pos hDen 2).le)
  have hRatioTrace :
      4 * (B hFrozen).det / ((C * (P).trace) ^ 2) ≤
        4 * (B hFrozen).det / ((B hFrozen).trace ^ 2) :=
    (div_le_div_iff₀ (pow_pos hDen 2) (pow_pos hBTrace 2)).mpr
      (mul_le_mul_of_nonneg_left hDenSq
        (mul_pos (by norm_num) hBDet).le)
  have hRatio := hRatioDet.trans hRatioTrace
  refine ⟨c, C, hc, hcC, hD3, hSharpD3,
    div_pos hNumer (pow_pos hDen 2), hRatio, ?_⟩
  intro a
  have hGEig :
      ∀ i : Fin 3,
        4 * (B hFrozen).det / ((B hFrozen).trace ^ 2) ≤
          hBPSD.isHermitian.eigenvalues i :=
    (p4Q2PZ37R_finThree_posSemidef_eigenvalue_explicit_lower
      (B hFrozen) hBPSD hBDet).2
  have hSpectral :=
    p4Q2PZ37T_finThree_posSemidef_spectral_quadratic_lower
      (B hFrozen) hBPSD
      (4 * (B hFrozen).det / ((B hFrozen).trace ^ 2)) hGEig a
  have hMassExact :
      star a ⬝ᵥ ((B hFrozen) *ᵥ a) =
        Mass (Src a) (Finset.univ : Finset Link) := by
    simpa only [p4Q2HJ_actualRightPhysicalSourceSynthesis] using
      (p4Q2HO_actualRightOriginalGLIntegralMatrix_quad_eq_originalGLMass
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n 2 hFrozen a)
  rw [hMassExact] at hSpectral
  exact (mul_le_mul_of_nonneg_right hRatio
    (Finset.sum_nonneg (fun j _ => sq_nonneg (a j)))).trans hSpectral

end OriginalGLPhysicalD3Sharp
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37Y_allFiniteSmallFine_originalGLIntegral_sharpD3DetMass
