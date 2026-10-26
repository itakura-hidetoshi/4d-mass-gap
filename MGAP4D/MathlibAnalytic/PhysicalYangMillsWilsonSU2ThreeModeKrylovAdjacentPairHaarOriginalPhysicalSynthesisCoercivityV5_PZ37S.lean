import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalFiniteGramTraceSpectralLowerV5_PZ37R
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic

/-!
# P4-Q2-PZ37S — genuine physical three-mode synthesis is bounded below

PZ37Q proves the image of the ORIGINAL normalized SU(2) Wilson physical
Krylov synthesis `a ↦ a₀ U + a₁ T_t U + a₂ T_t² U` has dimension three
in the authentic Gauss-law Hilbert space. PZ37R gives its genuinely
positive, volume-dependent 3x3 Gram spectral certificate
`4 det G / (trace G)^2`.

The first theorem below proves that a three-dimensional real finite
synthesis image has a TRIVIAL coefficient kernel. The pinned mathlib
finite-dimensional inverse bound then supplies a single positive
antilipschitz constant for all coefficient vectors (not a different
constant for each vector).

The final theorem proves this directly for the original physical Wilson
synthesis at every finite H >= 0 and every sufficiently small positive
fine coupling. In the same interval it retains PZ37R's explicit
spectral certificate.

The coefficient coercivity factor K(H,t) and the small-fine radius
delta(H, contexts) are NOT volume uniform. In particular this does
NOT establish U0, the genuine posterior-fiber coercivity normalized by
the lattice volume, fine at arbitrary depth, endpoint, the continuum
strong limit or a Yang--Mills mass gap. No replacement kernel is used.
-/

namespace MGAP4D.MathlibAnalytic
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Full rank of an actual three-vector real Hilbert synthesis implies
a nonzero coefficient norm lower bound. Unlike pointwise nonvanishing,
one K works for every real coefficient vector. -/
theorem p4Q2PZ37S_realFiniteThreeSynthesis_antilipschitz
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : Fin 3 → E)
    (hrank :
      Module.finrank ℝ (p4Q2AD_realFiniteSynthesis v).range = 3) :
    ∃ K : ℝ≥0, 0 < K ∧
      AntilipschitzWith K (p4Q2AD_realFiniteSynthesis v) := by
  classical
  let S := p4Q2AD_realFiniteSynthesis v
  have hdim : Module.finrank ℝ (Fin 3 → ℝ) = 3 := by
    simp
  have hkernelDim : Module.finrank ℝ S.ker = 0 := by
    have hrankNull := S.finrank_range_add_finrank_ker
    change Module.finrank ℝ S.range + Module.finrank ℝ S.ker =
      Module.finrank ℝ (Fin 3 → ℝ) at hrankNull
    rw [hrank, hdim] at hrankNull
    omega
  have hker : S.ker = ⊥ :=
    Submodule.finrank_eq_zero.mp hkernelDim
  exact S.exists_antilipschitzWith hker

/-- The anti-Lipschitz estimate in its useful direct physical form:
the coefficient norm is controlled by the unchanged physical source norm. -/
theorem p4Q2PZ37S_realFiniteThreeSynthesis_norm_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : Fin 3 → E)
    (hrank : Module.finrank ℝ (p4Q2AD_realFiniteSynthesis v).range = 3) :
    ∃ K : ℝ≥0, 0 < K ∧
      ∀ a : Fin 3 → ℝ,
        ‖a‖ ≤ (K : ℝ) * ‖(p4Q2AD_realFiniteSynthesis v) a‖ := by
  obtain ⟨K, hK, hAnti⟩ :=
    p4Q2PZ37S_realFiniteThreeSynthesis_antilipschitz v hrank
  refine ⟨K, hK, ?_⟩
  intro a
  simpa only [dist_zero_right, map_zero] using hAnti.le_mul_dist a 0

namespace GroundStatePosteriorJoint

section ActualThreeModeCoercivity
variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
variable {hbeta : ∀ n, 0 ≤ beta n}
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

/-- Original SU(2) Wilson Gauss-law physical synthesis is quantitatively
injective at all FINITE volumes: a single K works for every three-mode
coefficient a on each fixed positive fine coupling. -/
theorem p4Q2PZ37S_allFiniteSmallFine_originalPhysicalCoefficient_norm_bound
    (hFrozen : 0 < beta n)
    (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ delta : ℝ, 0 < delta ∧
      (0 < beta (n + 1) → beta (n + 1) < delta →
        ∃ K : ℝ≥0, 0 < K ∧
          ∀ a : Fin (2 + 1) → ℝ, ‖a‖ ≤ (K : ℝ) * ‖S a‖) := by
  obtain ⟨delta, hdelta, hThree⟩ :=
    p4Q2PZ37Q_allFiniteSmallFine_originalPhysicalKrylov_finrank_three
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e e' left₀ right₀
  refine ⟨delta, hdelta, ?_⟩
  intro hFine hSmall
  exact p4Q2PZ37S_realFiniteThreeSynthesis_norm_bound
    Krylov (hThree hFine hSmall)

/-- PZ37R spectral lower certificate and the PZ37S coefficient coercivity
hold on ONE true finite-volume original-Wilson fine interval. This is the
honest quantitative bridge, not the still-open U0 uniform limit. -/
theorem p4Q2PZ37S_allFiniteSmallFine_originalPhysicalGram_and_coefficient_lower
    (hFrozen : 0 < beta n)
    (e e' : Link) (left₀ right₀ : Cfg) :
    ∃ delta : ℝ, 0 < delta ∧
      (0 < beta (n + 1) → beta (n + 1) < delta →
        (0 < B ∧ ∀ i : Fin 3,
          B ≤ (p4Q2PZ37R_originalWilsonThreeHankel_posSemidef
            Hn (beta (n + 1)) (hbeta (n + 1))).isHermitian.eigenvalues i) ∧
        ∃ K : ℝ≥0, 0 < K ∧
          ∀ a : Fin (2 + 1) → ℝ, ‖a‖ ≤ (K : ℝ) * ‖S a‖) := by
  obtain ⟨deltaG, hdeltaG, hG⟩ :=
    p4Q2PZ37R_allFiniteSmallFine_originalPhysicalGram_eigenvalue_lower
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e e' left₀ right₀
  obtain ⟨deltaS, hdeltaS, hS⟩ :=
    p4Q2PZ37S_allFiniteSmallFine_originalPhysicalCoefficient_norm_bound
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n hFrozen e e' left₀ right₀
  refine ⟨min deltaG deltaS, lt_min hdeltaG hdeltaS, ?_⟩
  intro hFine hSmall
  have hSmallG : beta (n + 1) < deltaG :=
    lt_of_lt_of_le hSmall (min_le_left _ _)
  have hSmallS : beta (n + 1) < deltaS :=
    lt_of_lt_of_le hSmall (min_le_right _ _)
  exact ⟨hG hFine hSmallG, hS hFine hSmallS⟩

end ActualThreeModeCoercivity
end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37S_realFiniteThreeSynthesis_antilipschitz
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37S_realFiniteThreeSynthesis_norm_bound
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37S_allFiniteSmallFine_originalPhysicalCoefficient_norm_bound
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37S_allFiniteSmallFine_originalPhysicalGram_and_coefficient_lower
