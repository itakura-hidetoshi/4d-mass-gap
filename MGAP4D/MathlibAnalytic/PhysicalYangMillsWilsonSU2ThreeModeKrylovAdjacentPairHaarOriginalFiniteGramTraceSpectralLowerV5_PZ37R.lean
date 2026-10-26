import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalAllFinitePhysicalRankThreeV5_PZ37Q
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# P4-Q2-PZ37R — explicit finite-volume spectral lower bound for the genuine Gram

The genuine original SU(2) normalized Gauss-law three-Krylov Gram equals
the original three-moment Wilson Hankel matrix G.  PZ37Q supplies positivity
of its determinant for all finite spatial half-extents (H >= 0) on a
positive, H-dependent fine interval.  For any positive definite real
3-by-3 matrix the elementary eigenvalue product/sum identities give

  lambda_min(G) >= 4 * det(G) / trace(G)^2 > 0.

Here det(G) is EXACTLY the original Wilson D3, and trace(G) is the sum
of the genuine original moments m0 + m2 + m4.  In particular, the
bound displays rather than conceals the H and coupling dependence.

This is a quantitative finite-volume statement.  No volume-independent
lower bound on det(G)/trace(G)^2, no uniform fine radius, and no U0,
endpoint, strong-limit, reconstruction or continuum mass gap is asserted.
-/

namespace MGAP4D.MathlibAnalytic

open Matrix
open scoped InnerProductSpace BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

namespace GroundStatePosteriorJoint

/-- The elementary three-number AM-GM estimate with one eigenvalue singled
out.  There is no spectral or model assumption in this algebraic lemma. -/
private theorem p4Q2PZ37R_three_nonnegative_product_bound
    (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    4 * a * b * c ≤ (a + b + c) ^ 2 * a := by
  have hbc : 4 * b * c ≤ (b + c) ^ 2 := by
    nlinarith [sq_nonneg (b - c)]
  have hmix : 0 ≤ a * (b + c) := mul_nonneg ha (add_nonneg hb hc)
  have htrace : (b + c) ^ 2 ≤ (a + b + c) ^ 2 := by
    nlinarith [sq_nonneg a, hmix]
  calc
    4 * a * b * c = (4 * b * c) * a := by ring
    _ ≤ (a + b + c) ^ 2 * a :=
      mul_le_mul_of_nonneg_right (hbc.trans htrace) ha

/-- Exact 3-by-3 positive-semidefinite determinant/trace certificate.
The bound holds even when the determinant vanishes.  Applying it to a
strictly positive determinant produces a positive lower eigenvalue. -/
theorem p4Q2PZ37R_finThree_posSemidef_eigenvalue_det_trace_bound
    (G : Matrix (Fin 3) (Fin 3) ℝ) (hG : G.PosSemidef)
    (i : Fin 3) :
    4 * G.det ≤ G.trace ^ 2 * hG.isHermitian.eigenvalues i := by
  let ev : Fin 3 → ℝ := hG.isHermitian.eigenvalues
  have hnonneg (j : Fin 3) : 0 ≤ ev j := hG.eigenvalues_nonneg j
  have hdet : G.det = ev 0 * ev 1 * ev 2 := by
    simpa only [ev, Fin.prod_univ_three] using
      hG.isHermitian.det_eq_prod_eigenvalues
  have htrace : G.trace = ev 0 + ev 1 + ev 2 := by
    simpa only [ev, Fin.sum_univ_three] using
      hG.isHermitian.trace_eq_sum_eigenvalues
  -- A calc chain uses proved equality rather than relying on the
  -- definitional equality checked by `change`. In particular, `4*(a*b*c)`
  -- and `((4*a)*b)*c` are only propositionally equal by associativity.
  have hcore (j : Fin 3) :
      4 * (ev 0 * ev 1 * ev 2) ≤
        (ev 0 + ev 1 + ev 2) ^ 2 * ev j := by
    -- Turn a finite-index case split into genuine propositional equalities.
    -- This keeps `ring` from seeing `ev ⟨1, proof⟩` and `ev 1` as
    -- separate opaque atoms after `fin_cases` introduces constructors.
    have hj : j = 0 ∨ j = 1 ∨ j = 2 := by
      fin_cases j <;> simp
    rcases hj with hj | hj | hj
    · subst j
      convert p4Q2PZ37R_three_nonnegative_product_bound
        (ev 0) (ev 1) (ev 2) (hnonneg 0) (hnonneg 1) (hnonneg 2) using 1
      ring
    · subst j
      convert p4Q2PZ37R_three_nonnegative_product_bound
        (ev 1) (ev 0) (ev 2) (hnonneg 1) (hnonneg 0) (hnonneg 2) using 1 <;>
          ring
    · subst j
      convert p4Q2PZ37R_three_nonnegative_product_bound
        (ev 2) (ev 0) (ev 1) (hnonneg 2) (hnonneg 0) (hnonneg 1) using 1 <;>
          ring
  calc
    4 * G.det = 4 * (ev 0 * ev 1 * ev 2) := by rw [hdet]
    _ ≤ (ev 0 + ev 1 + ev 2) ^ 2 * ev i := hcore i
    _ = G.trace ^ 2 * hG.isHermitian.eigenvalues i := by
      rw [htrace]

/-- Strict 3-by-3 Gram determinant gives the explicit strictly positive
finite-volume lower certificate det/trace^2 for EVERY real eigenvalue. -/
theorem p4Q2PZ37R_finThree_posSemidef_eigenvalue_explicit_lower
    (G : Matrix (Fin 3) (Fin 3) ℝ) (hG : G.PosSemidef)
    (hdet : 0 < G.det) :
    0 < 4 * G.det / (G.trace ^ 2) ∧
      ∀ i : Fin 3,
        4 * G.det / (G.trace ^ 2) ≤ hG.isHermitian.eigenvalues i := by
  have hpos : G.PosDef :=
    (hG.posDef_iff_det_ne_zero).mpr (ne_of_gt hdet)
  have htrace : 0 < G.trace := hpos.trace_pos
  have hden : 0 < G.trace ^ 2 := pow_pos htrace 2
  constructor
  · exact div_pos (mul_pos (by norm_num) hdet) hden
  · intro i
    apply (div_le_iff₀ hden).2
    calc
      4 * G.det ≤ G.trace ^ 2 * hG.isHermitian.eigenvalues i :=
        p4Q2PZ37R_finThree_posSemidef_eigenvalue_det_trace_bound G hG i
      _ = hG.isHermitian.eigenvalues i * G.trace ^ 2 := mul_comm _ _

/-- The true finite-volume original Wilson moment matrix is PSD because
it is LITERALLY the Gram of U, T U and T^2 U in the genuine physical
Gauss-law Hilbert carrier.  No auxiliary Gram or statistical proxy. -/
theorem p4Q2PZ37R_originalWilsonThreeHankel_posSemidef
    (H : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (p4Q2PD_originalWilsonThreeHankel H t ht).PosSemidef := by
  let Phys :=
    periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
  let U : Phys :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let Fine :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H 2 specialUnitaryTwoWilsonRankPositive t ht
  let Krylov : Fin (2 + 1) → Phys :=
    fun j => ((Fine ^ (j : ℕ)) U : Phys)
  have hGram :
      Matrix.gram ℝ Krylov =
        p4Q2PD_originalWilsonThreeHankel H t ht := by
    simpa only [p4Q2PD_originalWilsonThreeHankel] using
      (p4Q2PB_originalWilsonPhysicalGram_eq_actualHankel H t ht 2)
  rw [← hGram]
  exact Matrix.posSemidef_gram ℝ Krylov

/-- The trace in the finite-volume denominator is exactly the sum of
the original Wilson moments (0th, 2nd and 4th), not a replacement norm. -/
theorem p4Q2PZ37R_originalWilsonThreeHankel_trace_eq_moments
    (H : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (p4Q2PD_originalWilsonThreeHankel H t ht).trace =
      p4Q2PB_originalWilsonPhysicalMoment H t ht 0 +
      p4Q2PB_originalWilsonPhysicalMoment H t ht 2 +
      p4Q2PB_originalWilsonPhysicalMoment H t ht 4 := by
  simp [Matrix.trace_fin_three, p4Q2PD_originalWilsonThreeHankel]

/-- Explicit, volume- and fine-coupling-dependent genuine Gram
least-eigenvalue certificate.  Positivity is established below only in
the exact finite-volume region proved by PZ37Q. -/
noncomputable def p4Q2PZ37R_originalWilsonThreeGramLower
    (H : ℕ) (t : ℝ) (ht : 0 ≤ t) : ℝ :=
  let G := p4Q2PD_originalWilsonThreeHankel H t ht
  4 * G.det / (G.trace ^ 2)

/-- ALL finite H >= 0, original normalized SU(2) Wilson physical three-mode
Gram: an explicit positive eigenvalue lower bound on the common true
small-positive-fine interval.  Each delta and each certificate depend on
the finite volume.  This does NOT imply U0 or a continuum mass gap. -/
theorem p4Q2PZ37R_allFiniteSmallFine_originalPhysicalGram_eigenvalue_lower
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ k, 0 ≤ beta k}
    (n : ℕ) (hFrozen : 0 < beta n)
    (e e' : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)))
    (left₀ right₀ :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration
        (halfExtent (n + 1)) 2) :
    ∃ delta : ℝ, 0 < delta ∧
      (0 < beta (n + 1) → beta (n + 1) < delta →
        0 < p4Q2PZ37R_originalWilsonThreeGramLower
          (halfExtent (n + 1)) (beta (n + 1)) (hbeta (n + 1)) ∧
        ∀ i : Fin 3,
          p4Q2PZ37R_originalWilsonThreeGramLower
            (halfExtent (n + 1)) (beta (n + 1)) (hbeta (n + 1)) ≤
            (p4Q2PZ37R_originalWilsonThreeHankel_posSemidef
              (halfExtent (n + 1)) (beta (n + 1))
              (hbeta (n + 1))).isHermitian.eigenvalues i) := by
  obtain ⟨delta, hdelta, hThird⟩ :=
    p4Q2PZ37Q_allFiniteSmallFine_originalThirdSource_mass_and_signedGI
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e e' left₀ right₀
  refine ⟨delta, hdelta, ?_⟩
  intro hfine hsmall
  let H := halfExtent (n + 1)
  let t := beta (n + 1)
  let G : Matrix (Fin 3) (Fin 3) ℝ :=
    p4Q2PD_originalWilsonThreeHankel H t (hbeta (n + 1))
  have hPSD : G.PosSemidef :=
    p4Q2PZ37R_originalWilsonThreeHankel_posSemidef
      H t (hbeta (n + 1))
  have hdet : 0 < G.det := by
    change 0 < (p4Q2PD_originalWilsonThreeHankel
      H t (hbeta (n + 1))).det
    rw [p4Q2PD_originalWilsonThreeHankel_det_eq_gap]
    exact (hThird hfine hsmall).1
  have hcert :=
    p4Q2PZ37R_finThree_posSemidef_eigenvalue_explicit_lower G hPSD hdet
  simpa only [G, H, t, p4Q2PZ37R_originalWilsonThreeGramLower] using hcert

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37R_finThree_posSemidef_eigenvalue_det_trace_bound
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37R_finThree_posSemidef_eigenvalue_explicit_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37R_originalWilsonThreeHankel_posSemidef
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37R_originalWilsonThreeHankel_trace_eq_moments
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37R_allFiniteSmallFine_originalPhysicalGram_eigenvalue_lower
