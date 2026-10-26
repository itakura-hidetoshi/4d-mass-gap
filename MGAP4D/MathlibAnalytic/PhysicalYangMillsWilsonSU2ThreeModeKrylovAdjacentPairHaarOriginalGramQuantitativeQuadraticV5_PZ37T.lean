import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPhysicalSynthesisCoercivityV5_PZ37S
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Tactic

/-!
# P4-Q2-PZ37T — explicit physical Wilson quadratic coercivity

PZ37R proved the explicit finite-volume spectral certificate
  4 det G / (trace G)^2 <= every eigenvalue of G
for the authentic normalized SU(2) Wilson Gauss-law 3-by-3 Gram matrix.
PZ37S proved an unspecified finite-volume anti-Lipschitz constant for
the actual three-mode synthesis.  This module closes the quantitative
bridge by transferring the SAME spectral certificate to every real
coefficient vector at a fixed physical fine coupling.

In the true original Gauss-law Hilbert space, with genuine U and T_t,
the result is:
  (4 D3(H,t)/(m0(H,t)+m2(H,t)+m4(H,t))^2) * (a0^2+a1^2+a2^2)
       <= ‖a0 U + a1 T_t U + a2 T_t² U‖².

Every finite half-extent H>=0 is covered on a sufficiently small positive
fine interval; the bound and interval depend on H.  No U0, endpoint,
arbitrary-depth fine, strong limit, continuum gap or surrogate model.
No new axioms, sorry, admit or native_decide.
-/

namespace MGAP4D.MathlibAnalytic
open Matrix Unitary
open scoped InnerProductSpace BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

namespace GroundStatePosteriorJoint

/-- A real Hermitian 3x3 spectral lower certificate bounds the entire
quadratic form, with NO dependence on the coefficient vector. The
orthogonal eigenvector change of basis and its unitarity are handled
inside the proof rather than assuming any quadratic coercivity. -/
theorem p4Q2PZ37T_finThree_posSemidef_spectral_quadratic_lower
    (G : Matrix (Fin 3) (Fin 3) ℝ) (hG : G.PosSemidef)
    (c : ℝ)
    (hEig : ∀ i : Fin 3, c ≤ hG.isHermitian.eigenvalues i)
    (a : Fin 3 → ℝ) :
    c * (∑ i : Fin 3, (a i) ^ 2) ≤ star a ⬝ᵥ (G *ᵥ a) := by
  let U : Matrix (Fin 3) (Fin 3) ℝ :=
    hG.isHermitian.eigenvectorUnitary
  let ev : Fin 3 → ℝ := hG.isHermitian.eigenvalues
  have hD : (Matrix.diagonal (fun i : Fin 3 => ev i - c)).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun i => sub_nonneg.mpr (hEig i))
  have hConj : (U * Matrix.diagonal (fun i : Fin 3 => ev i - c) * star U).PosSemidef := by
    simpa only [← star_eq_conjTranspose] using
      (hD.mul_mul_conjTranspose_same U)
  have hDiag : Matrix.diagonal (fun i : Fin 3 => ev i - c) =
      Matrix.diagonal ev - c • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.smul_apply]
    · simp [Matrix.smul_apply, hij]
  have hUnit : U * star U = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    simpa only [U] using
      (Unitary.coe_mul_star_self hG.isHermitian.eigenvectorUnitary)
  have hSpectral : G = U * Matrix.diagonal ev * star U := by
    simpa [U, ev, conjStarAlgAut_apply] using hG.isHermitian.spectral_theorem
  have hScalar :
      U * (c • (1 : Matrix (Fin 3) (Fin 3) ℝ)) * star U =
        c • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, mul_one, hUnit]
  have hConjugateDifference :
      U * (Matrix.diagonal ev - c • (1 : Matrix (Fin 3) (Fin 3) ℝ)) * star U =
        G - c • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
    rw [mul_sub, sub_mul, hScalar, ← hSpectral]
  have hShift : (G - c • (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosSemidef := by
    rw [← hConjugateDifference, ← hDiag]
    exact hConj
  have hQuadratic := hShift.dotProduct_mulVec_nonneg a
  have hSelfDot : star a ⬝ᵥ a = ∑ i : Fin 3, (a i) ^ 2 := by
    simp [dotProduct, pow_two]
  have hExpand :
      star a ⬝ᵥ ((G - c • (1 : Matrix (Fin 3) (Fin 3) ℝ)) *ᵥ a) =
        star a ⬝ᵥ (G *ᵥ a) - c * (∑ i : Fin 3, (a i) ^ 2) := by
    rw [sub_mulVec, smul_mulVec, one_mulVec, dotProduct_sub, dotProduct_smul]
    simp only [smul_eq_mul, hSelfDot]
  rw [hExpand] at hQuadratic
  exact sub_nonneg.mp hQuadratic

/-- EXACT REAL Hilbert Gram quadratic identity for the original synthesis
constructor. The coefficient vector is the same on both sides. -/
theorem p4Q2PZ37T_realFiniteSynthesis_gram_quadratic_eq_normSq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : Fin 3 → E) (a : Fin 3 → ℝ) :
    star a ⬝ᵥ ((Matrix.gram ℝ v) *ᵥ a) =
      ‖(p4Q2AD_realFiniteSynthesis v) a‖ ^ 2 := by
  rw [Matrix.star_dotProduct_gram_mulVec]
  change ⟪(p4Q2AD_realFiniteSynthesis v) a,
    (p4Q2AD_realFiniteSynthesis v) a⟫_ℝ = _
  exact real_inner_self_eq_norm_sq _

section OriginalPhysicalGramQuadratic
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
  (fun j : Fin (2 + 1) => ((Fine ^ (j : ℕ)) U : Phys))
local notation "S" => p4Q2AD_realFiniteSynthesis Krylov
local notation "G" =>
  p4Q2PD_originalWilsonThreeHankel
    Hn (beta (n + 1)) (hbeta (n + 1))
local notation "B" =>
  p4Q2PZ37R_originalWilsonThreeGramLower
    Hn (beta (n + 1)) (hbeta (n + 1))

/-- The original three-mode physical Gauss-law source has an explicitly
quantified squared-norm lower bound at all finite periods and small
positive fine couplings, WITHOUT replacing physical Wilson or Haar. -/
theorem p4Q2PZ37T_allFiniteSmallFine_originalPhysicalSynthesis_quadratic_lower
    (hFrozen : 0 < beta n)
    (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ delta : ℝ, 0 < delta ∧
      (0 < beta (n + 1) → beta (n + 1) < delta →
        0 < B ∧ ∀ a : Fin (2 + 1) → ℝ,
          B * (∑ j : Fin (2 + 1), (a j) ^ 2) ≤ ‖S a‖ ^ 2) := by
  obtain ⟨delta, hdelta, hCert⟩ :=
    p4Q2PZ37R_allFiniteSmallFine_originalPhysicalGram_eigenvalue_lower
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e e' left₀ right₀
  refine ⟨delta, hdelta, ?_⟩
  intro hFine hSmall
  obtain ⟨hB, hEig⟩ := hCert hFine hSmall
  refine ⟨hB, ?_⟩
  intro a
  have hGram : Matrix.gram ℝ Krylov = G := by
    simpa only [p4Q2PD_originalWilsonThreeHankel] using
      (p4Q2PB_originalWilsonPhysicalGram_eq_actualHankel
        Hn (beta (n + 1)) (hbeta (n + 1)) 2)
  have hPSD :
      (p4Q2PD_originalWilsonThreeHankel
        Hn (beta (n + 1)) (hbeta (n + 1))).PosSemidef :=
    p4Q2PZ37R_originalWilsonThreeHankel_posSemidef
      Hn (beta (n + 1)) (hbeta (n + 1))
  have hQuadratic :
      star a ⬝ᵥ (G *ᵥ a) = ‖S a‖ ^ 2 := by
    rw [← hGram]
    exact p4Q2PZ37T_realFiniteSynthesis_gram_quadratic_eq_normSq Krylov a
  have hEstimate :=
    p4Q2PZ37T_finThree_posSemidef_spectral_quadratic_lower G hPSD B hEig a
  rwa [hQuadratic] at hEstimate

end OriginalPhysicalGramQuadratic
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37T_finThree_posSemidef_spectral_quadratic_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37T_realFiniteSynthesis_gram_quadratic_eq_normSq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37T_allFiniteSmallFine_originalPhysicalSynthesis_quadratic_lower
