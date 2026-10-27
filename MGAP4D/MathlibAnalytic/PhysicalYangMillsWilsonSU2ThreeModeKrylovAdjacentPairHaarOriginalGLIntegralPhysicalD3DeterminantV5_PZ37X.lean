import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalGLIntegralVolumeTraceBridgeV5_PZ37W
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

/-!
# P4-Q2-PZ37X — true Wilson GL integral determinant from physical D3

For every finite H, PZ37W proves a true quadratic comparison of the
original two-interacting-posterior Haar GL integral Gram G_GL against
the normalized Gauss-law physical three-Krylov Gram P:

    c P <= G_GL <= C P (quadratic forms), 0 < c <= C.

PZ37R/T supply the genuine Wilson three-moment Hankel certificate

    b(H,t) = 4 D3(H,t) / (m0+m2+m4)^2 > 0

for fixed positive frozen and sufficiently small positive fine
couplings. Spectral diagonalization of the ACTUAL GL integral matrix,
not a finite sampled or substitute detector, gives

    det(G_GL) >= (c b)^3 > 0
    4 (c b)^3 / (C trace P)^2
          <= 4 det(G_GL) / (trace G_GL)^2.

This is an explicit *finite-volume* bridge between the original
SU(2) Wilson physical Hankel D3 and original GL posterior Haar Gram
determinant. Unlike determinant monotonicity, it requires only the
proved coefficient-space lower estimate and the three eigenvalues.
The bound is cubic in the physical spectral floor; a stronger
c^3 D3 bound is NOT asserted here.

Constants c,C and the small-fine interval can depend on H, frozen
and fine couplings. No H-uniform determinant ratio, U0, common
fine radius, endpoint E, arbitrary-depth F, H1-H4 or continuum
Yang--Mills mass gap. No replacement kernel, Dobrushin, new axiom,
sorry, admit or native_decide.
-/

namespace MGAP4D.MathlibAnalytic
open MeasureTheory Matrix
open scoped ENNReal InnerProductSpace BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local instance p4Q2PZ37X_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37X_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37X_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37X_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37X_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
private noncomputable instance p4Q2PZ37X_linkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- A uniform lower quadratic bound for a real 3x3 PSD matrix
bounds ALL its genuine Hermitian eigenvalues. The input is a
quadratic inequality, not a separately assumed spectral gap. -/
theorem p4Q2PZ37X_finThree_quadratic_floor_eigenvalues
    (G : Matrix (Fin 3) (Fin 3) ℝ) (hG : G.PosSemidef)
    (k : ℝ)
    (hFloor : ∀ a : Fin 3 → ℝ,
      k * (∑ j : Fin 3, (a j) ^ 2) ≤ star a ⬝ᵥ (G *ᵥ a)) :
    ∀ i : Fin 3, k ≤ hG.isHermitian.eigenvalues i := by
  intro i
  let u : EuclideanSpace ℝ (Fin 3) :=
    hG.isHermitian.eigenvectorBasis i
  let a : Fin 3 → ℝ := ⇑u
  have hUnit : ‖u‖ = 1 :=
    (hG.isHermitian.eigenvectorBasis).orthonormal.1 i
  have hInner : ⟪u, u⟫_ℝ = 1 := by
    calc
      ⟪u, u⟫_ℝ = ‖u‖ ^ 2 := real_inner_self_eq_norm_sq u
      _ = 1 := by rw [hUnit]; norm_num
  have hCoeff : (∑ j : Fin 3, (a j) ^ 2) = 1 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct] at hInner
    simpa only [a, dotProduct, star_trivial, pow_two] using hInner
  have hValue :
      star a ⬝ᵥ (G *ᵥ a) = hG.isHermitian.eigenvalues i := by
    simpa [a] using (hG.isHermitian.eigenvalues_eq i).symm
  have h := hFloor a
  rw [hCoeff, hValue] at h
  simpa using h

/-- Three genuine nonnegative Hermitian eigenvalues above k give
the cubic determinant floor (no simultaneous diagonalization of
two different Gram matrices is used). -/
theorem p4Q2PZ37X_finThree_eigenvalues_floor_det
    (G : Matrix (Fin 3) (Fin 3) ℝ) (hG : G.PosSemidef)
    (k : ℝ) (hk : 0 ≤ k)
    (hFloor : ∀ i : Fin 3, k ≤ hG.isHermitian.eigenvalues i) :
    k ^ 3 ≤ G.det := by
  have hProd :
      (∏ _i : Fin 3, k) ≤
        ∏ i : Fin 3, hG.isHermitian.eigenvalues i :=
    Finset.prod_le_prod (fun _ _ => hk) (fun i _ => hFloor i)
  calc
    k ^ 3 = ∏ _i : Fin 3, k := by simp [Fin.prod_univ_three, pow_succ]
    _ ≤ ∏ i : Fin 3, hG.isHermitian.eigenvalues i := hProd
    _ = G.det := (hG.isHermitian.det_eq_prod_eigenvalues).symm

/-- Genuine PSD coefficient quadratic domination gives a cubic
determinant floor. Useful for the true physical/GL comparison,
but valid for any real PSD matrices and three coefficients. -/
theorem p4Q2PZ37X_finThree_twoGram_quadratic_to_det_lower
    (P G : Matrix (Fin 3) (Fin 3) ℝ)
    (hG : G.PosSemidef) (b c : ℝ)
    (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hPhysical : ∀ a : Fin 3 → ℝ,
      b * (∑ j : Fin 3, (a j) ^ 2) ≤ star a ⬝ᵥ (P *ᵥ a))
    (hCompare : ∀ a : Fin 3 → ℝ,
      c * (star a ⬝ᵥ (P *ᵥ a)) ≤ star a ⬝ᵥ (G *ᵥ a)) :
    (c * b) ^ 3 ≤ G.det := by
  have hCoef (a : Fin 3 → ℝ) :
      (c * b) * (∑ j : Fin 3, (a j) ^ 2) ≤ star a ⬝ᵥ (G *ᵥ a) := by
    calc
      (c * b) * (∑ j : Fin 3, (a j) ^ 2) =
          c * (b * (∑ j : Fin 3, (a j) ^ 2)) := by ring
      _ ≤ c * (star a ⬝ᵥ (P *ᵥ a)) :=
        mul_le_mul_of_nonneg_left (hPhysical a) hc
      _ ≤ star a ⬝ᵥ (G *ᵥ a) := hCompare a
  exact p4Q2PZ37X_finThree_eigenvalues_floor_det G hG
    (c * b) (mul_nonneg hc hb)
    (p4Q2PZ37X_finThree_quadratic_floor_eigenvalues G hG (c * b) hCoef)

section TrueOriginalGLIntegralPhysicalDeterminant
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
local notation "b" =>
  p4Q2PZ37R_originalWilsonThreeGramLower
    Hn (beta (n + 1)) (hbeta (n + 1))

/-- For the ACTUAL interacting Wilson posterior Haar matrix, not a
sampled detector, the genuine physical Hankel D3 produces a strictly
positive determinant lower certificate. Its constants and interval
are still allowed to depend on finite volume H. -/
theorem p4Q2PZ37X_allFiniteSmallFine_originalGLIntegral_D3_cubicDetAndGamma
    (hFrozen : 0 < beta n) (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ delta : ℝ, 0 < delta ∧
      (0 < beta (n + 1) → beta (n + 1) < delta →
        ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
          0 < b ∧
          c * (P).trace ≤ (B hFrozen).trace ∧
          (B hFrozen).trace ≤ C * (P).trace ∧
          (c * b) ^ 3 ≤ (B hFrozen).det ∧
          0 < 4 * ((c * b) ^ 3) / ((C * (P).trace) ^ 2) ∧
          4 * ((c * b) ^ 3) / ((C * (P).trace) ^ 2) ≤
            4 * (B hFrozen).det / ((B hFrozen).trace ^ 2)) := by
  obtain ⟨delta, hdelta, hPhys⟩ :=
    p4Q2PZ37T_allFiniteSmallFine_originalPhysicalSynthesis_quadratic_lower
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e e' left₀ right₀
  refine ⟨delta, hdelta, ?_⟩
  intro hFine hSmall
  obtain ⟨hb, hSourceFloor⟩ := hPhys hFine hSmall
  obtain ⟨c, C, hc, hcC, hCmp⟩ :=
    p4Q2PZ37W_allFinite_allFine_originalGL_physicalGram_quadratic_compare
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e left₀
  have hPGram : Matrix.gram ℝ Krylov = P := by
    simpa only [p4Q2PD_originalWilsonThreeHankel] using
      (p4Q2PB_originalWilsonPhysicalGram_eq_actualHankel
        Hn (beta (n + 1)) (hbeta (n + 1)) 2)
  have hPFloor (a : Fin 3 → ℝ) :
      b * (∑ j : Fin 3, (a j) ^ 2) ≤ star a ⬝ᵥ (P *ᵥ a) := by
    have hSource : Src a = (p4Q2AD_realFiniteSynthesis Krylov) a := rfl
    have hQuadratic :
        star a ⬝ᵥ (P *ᵥ a) = ‖Src a‖ ^ 2 := by
      calc
        star a ⬝ᵥ (P *ᵥ a) =
            star a ⬝ᵥ ((Matrix.gram ℝ Krylov) *ᵥ a) := by rw [hPGram]
        _ = ‖(p4Q2AD_realFiniteSynthesis Krylov) a‖ ^ 2 :=
          p4Q2PZ37T_realFiniteSynthesis_gram_quadratic_eq_normSq Krylov a
        _ = ‖Src a‖ ^ 2 := by rw [hSource]
    rw [hQuadratic]
    rw [hSource]
    exact hSourceFloor a
  have hPPSD : P.PosSemidef :=
    p4Q2PZ37R_originalWilsonThreeHankel_posSemidef
      Hn (beta (n + 1)) (hbeta (n + 1))
  have hPDef : P.PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos hPPSD.isHermitian
    intro a ha
    have hCoeff : 0 < ∑ j : Fin 3, (a j) ^ 2 := by
      simpa [dotProduct, pow_two] using
        (dotProduct_star_self_pos_iff.mpr ha)
    exact lt_of_lt_of_le (mul_pos hb hCoeff) (hPFloor a)
  have hPtrace : 0 < (P).trace := hPDef.trace_pos
  have hGPSD : (B hFrozen).PosSemidef :=
    p4Q2HO_actualRightOriginalGLIntegralMatrix_posSemidef
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n 2 hFrozen
  have hDetFloor :
      (c * b) ^ 3 ≤ (B hFrozen).det :=
    p4Q2PZ37X_finThree_twoGram_quadratic_to_det_lower
      P (B hFrozen) hGPSD b c hb.le hc.le hPFloor (fun a => (hCmp a).1)
  have hEig :
      ∀ i : Fin 3, c * b ≤ hGPSD.isHermitian.eigenvalues i := by
    apply p4Q2PZ37X_finThree_quadratic_floor_eigenvalues (B hFrozen) hGPSD (c * b)
    intro a
    calc
      (c * b) * (∑ j : Fin 3, (a j) ^ 2) =
          c * (b * (∑ j : Fin 3, (a j) ^ 2)) := by ring
      _ ≤ c * (star a ⬝ᵥ (P *ᵥ a)) :=
        mul_le_mul_of_nonneg_left (hPFloor a) hc.le
      _ ≤ star a ⬝ᵥ ((B hFrozen) *ᵥ a) := (hCmp a).1
  have hGDef : (B hFrozen).PosDef :=
    hGPSD.isHermitian.posDef_iff_eigenvalues_pos.mpr
      (fun i => lt_of_lt_of_le (mul_pos hc hb) (hEig i))
  have hGtrace : 0 < (B hFrozen).trace := hGDef.trace_pos
  have hGdet : 0 < (B hFrozen).det := hGDef.det_pos
  obtain ⟨hTraceLo, hTraceHi⟩ :=
    p4Q2PZ37W_finThree_quadratic_compare_trace P (B hFrozen) c C hCmp
  have hC : 0 < C := lt_of_lt_of_le hc hcC
  have hden : 0 < C * (P).trace := mul_pos hC hPtrace
  have hNum : 0 < 4 * ((c * b) ^ 3) :=
    mul_pos (by norm_num) (pow_pos (mul_pos hc hb) 3)
  have hGNum : 0 ≤ 4 * (B hFrozen).det :=
    (mul_pos (by norm_num) hGdet).le
  have hDenSq :
      (B hFrozen).trace ^ 2 ≤ (C * (P).trace) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hTraceHi)
      (add_nonneg hden.le hGtrace.le)]
  have hScaledDet :
      4 * ((c * b) ^ 3) ≤ 4 * (B hFrozen).det :=
    mul_le_mul_of_nonneg_left hDetFloor (by norm_num)
  have hRatioDet :
      4 * ((c * b) ^ 3) / ((C * (P).trace) ^ 2) ≤
        4 * (B hFrozen).det / ((C * (P).trace) ^ 2) :=
    (div_le_div_iff₀ (pow_pos hden 2) (pow_pos hden 2)).mpr
      (mul_le_mul_of_nonneg_right hScaledDet (pow_pos hden 2).le)
  have hRatioTrace :
      4 * (B hFrozen).det / ((C * (P).trace) ^ 2) ≤
        4 * (B hFrozen).det / ((B hFrozen).trace ^ 2) :=
    (div_le_div_iff₀ (pow_pos hden 2) (pow_pos hGtrace 2)).mpr
      (mul_le_mul_of_nonneg_left hDenSq hGNum)
  exact ⟨c, C, hc, hcC, hb, hTraceLo, hTraceHi, hDetFloor,
    div_pos hNum (pow_pos hden 2),
    hRatioDet.trans hRatioTrace⟩

end TrueOriginalGLIntegralPhysicalDeterminant
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37X_finThree_quadratic_floor_eigenvalues
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37X_finThree_eigenvalues_floor_det
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37X_finThree_twoGram_quadratic_to_det_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37X_allFiniteSmallFine_originalGLIntegral_D3_cubicDetAndGamma
