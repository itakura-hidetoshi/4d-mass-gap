import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFixedBeta0ScaledRawFullNormStepBudgetV5_PZ37ALY
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ALZ — linear norm budget for genuine beta0 Wilson volume steps

ALY established a conditional estimate on genuine physical scalar norms:
  r_(H+1) <= r_H + t_H,
  r_H = ||R_H(beta0)||,
  t_H = (eta_H + xi_H)/(s_H * ||P_H|| - xi_H).
The raw/full comparisons and denominator positivity are independent
PHYSICAL premises; this leaf does not establish them.

Instead of paying the generic squared loss 2*t_H+t_H^2 at EACH step,
first telescope the linear excited norm. If partial sums of t_H are
bounded by T with r_0+T<1, then
  r_H <= r_0+T<1
and the original squared deficit satisfies
  delta_H = 1-r_H^2 >= 1-r_H >= 1-r_0-T.
Consequently gap_H >= (1-r_0-T)/2 uniformly over every finite H.
This is a genuinely weaker sufficient scalar budget than requiring
sum(2*t_H+t_H^2)<delta_0, but remains CONDITIONED on true Wilson
raw/full cross-volume bounds and a strict summability margin.

A tail version uses the previously certified finite-prefix certificate
from ALT and requires a relative-error budget only for H>=M. A geometric
tail-cost majorant is also supported. No action on unrelated physical
Hilbert spaces is subtracted, and the original SU(2) model, fixed
beta0=log(3/2)/64, Haar/AJA, P/R/K, roots and pins are unchanged.

No independent physical t_H bound, all-H original beta0 gap, Hamiltonian
gap, or 4d continuum Yang-Mills mass gap is proved unconditionally.
-/

namespace MGAP4D.MathlibAnalytic

open scoped InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace GroundStatePosteriorJoint

local notation "E" => p4Q2PZ37ALY_originalFixedExcitedNorm
local notation "Err" => p4Q2PZ37ALY_originalFixedRelativeStepError
local notation "D" => p4Q2PZ37ALN_originalFixedTopOrthogonalSquaredGap
local notation "Gap" => p4Q2PZ37ALT_originalFixedGapAt
local notation "Full" => p4Q2PZ37ALX_originalFixedFullNorm
local notation "Raw" => p4Q2PZ37ALX_originalFixedRawExcitationNorm

/-- Pure real telescoping before taking squared norms, with no positivity
of the step costs required for this algebraic inference. -/
theorem p4Q2PZ37ALZ_generic_linearNormTelescoping
    (u t : ℕ → ℝ)
    (hstep : ∀ H : ℕ, u (H + 1) ≤ u H + t H) :
    ∀ H : ℕ, u H ≤ u 0 + (Finset.range H).sum t := by
  intro H
  induction H with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hs := hstep n
      linarith

/-- Real-scalar telescoping from any finite physical prefix M. -/
theorem p4Q2PZ37ALZ_generic_linearNormTailTelescoping
    (u t : ℕ → ℝ) (M : ℕ)
    (hstep : ∀ H : ℕ, u (H + 1) ≤ u H + t H) :
    ∀ n : ℕ,
      u (M + n) ≤ u M + (Finset.range n).sum (fun i => t (M + i)) := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hidx : M + (n + 1) = M + n + 1 := by omega
      rw [hidx, Finset.sum_range_succ]
      have hs := hstep (M + n)
      linarith

/-- Exact original-Wilson normalized excited norm is bounded by the
cumulative REAL relative errors, conditional on ALY's unproved physical
raw/full scalar step estimates. -/
theorem p4Q2PZ37ALZ_originalFixedNorm_linearTelescoping
    (s eta xi : ℕ → ℝ)
    (heta : ∀ H : ℕ, 0 ≤ eta H)
    (hxi : ∀ H : ℕ, 0 ≤ xi H)
    (hden : ∀ H : ℕ, 0 < s H * Full H - xi H)
    (hRaw : ∀ H : ℕ, Raw (H + 1) ≤ s H * Raw H + eta H)
    (hFull : ∀ H : ℕ, s H * Full H - xi H ≤ Full (H + 1)) :
    ∀ H : ℕ, E H ≤ E 0 +
      (Finset.range H).sum (fun i => Err i (s i) (eta i) (xi i)) := by
  apply p4Q2PZ37ALZ_generic_linearNormTelescoping
    (fun H => E H) (fun H => Err H (s H) (eta H) (xi H))
  intro H
  exact p4Q2PZ37ALY_originalFixedExcitedNorm_scaledStep_le
    H (s H) (eta H) (xi H)
    (heta H) (hxi H) (hden H) (hRaw H) (hFull H)

/-- Genuine original-Wilson linear relative-error budget from a selected
finite physical volume M onward. No cross-volume Hilbert map is used. -/
theorem p4Q2PZ37ALZ_originalFixedNorm_linearTailTelescoping
    (M : ℕ) (s eta xi : ℕ → ℝ)
    (heta : ∀ H : ℕ, 0 ≤ eta H)
    (hxi : ∀ H : ℕ, 0 ≤ xi H)
    (hden : ∀ H : ℕ, 0 < s H * Full H - xi H)
    (hRaw : ∀ H : ℕ, Raw (H + 1) ≤ s H * Raw H + eta H)
    (hFull : ∀ H : ℕ, s H * Full H - xi H ≤ Full (H + 1)) :
    ∀ n : ℕ, E (M + n) ≤ E M +
      (Finset.range n).sum
        (fun i => Err (M + i) (s (M + i)) (eta (M + i)) (xi (M + i))) := by
  apply p4Q2PZ37ALZ_generic_linearNormTailTelescoping
    (fun H => E H) (fun H => Err H (s H) (eta H) (xi H)) M
  intro H
  exact p4Q2PZ37ALY_originalFixedExcitedNorm_scaledStep_le
    H (s H) (eta H) (xi H)
    (heta H) (hxi H) (hden H) (hRaw H) (hFull H)

/-- Stronger original beta0 conditional finite-volume gap criterion:
the total LINEAR relative Wilson error need only fit below 1-r_0.
Unlike ALY, no per-step replacement by 2*t+t^2 is made. -/
theorem p4Q2PZ37ALZ_uniformGap_of_linearRelativeErrorBudget
    (s eta xi : ℕ → ℝ) (T : ℝ)
    (heta : ∀ H : ℕ, 0 ≤ eta H)
    (hxi : ∀ H : ℕ, 0 ≤ xi H)
    (hden : ∀ H : ℕ, 0 < s H * Full H - xi H)
    (hRaw : ∀ H : ℕ, Raw (H + 1) ≤ s H * Raw H + eta H)
    (hFull : ∀ H : ℕ, s H * Full H - xi H ≤ Full (H + 1))
    (htotal : ∀ H : ℕ,
      (Finset.range H).sum
        (fun i => Err i (s i) (eta i) (xi i)) ≤ T)
    (hSmall : E 0 + T < 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ H : ℕ, ε ≤ Gap H := by
  have htel := p4Q2PZ37ALZ_originalFixedNorm_linearTelescoping
    s eta xi heta hxi hden hRaw hFull
  refine ⟨(1 - (E 0 + T)) / 2, by linarith only [hSmall], ?_⟩
  intro H
  have hnorm : E H ≤ E 0 + T := by
    have ht := htel H
    have hs := htotal H
    linarith only [ht, hs]
  have hsq : E H ^ 2 ≤ E H := by
    have hr0 := p4Q2PZ37ALY_originalFixedExcitedNorm_nonneg H
    have hr1 := p4Q2PZ37ALY_originalFixedExcitedNorm_le_one H
    have hproduct : 0 ≤ E H * (1 - E H) :=
      mul_nonneg hr0 (sub_nonneg.mpr hr1)
    nlinarith only [hproduct]
  have hgap := p4Q2PZ37ALT_originalFixedGap_ge_half_squaredDefect H
  rw [p4Q2PZ37ALV_deficit_eq_one_sub_excitedNormSq H,
    ← p4Q2PZ37ALY_originalFixedExcitedNorm_sq_eq_Q H] at hgap
  linarith only [hgap, hsq, hnorm]

/-- A fixed finite prefix is handled by ALT. For the rest, only linear
summability of the true physical ALY relative costs is requested. -/
theorem p4Q2PZ37ALZ_uniformGap_of_tailLinearRelativeErrorBudget
    (M : ℕ) (s eta xi : ℕ → ℝ) (T : ℝ)
    (heta : ∀ H : ℕ, 0 ≤ eta H)
    (hxi : ∀ H : ℕ, 0 ≤ xi H)
    (hden : ∀ H : ℕ, 0 < s H * Full H - xi H)
    (hRaw : ∀ H : ℕ, Raw (H + 1) ≤ s H * Raw H + eta H)
    (hFull : ∀ H : ℕ, s H * Full H - xi H ≤ Full (H + 1))
    (htotal : ∀ n : ℕ,
      (Finset.range n).sum
        (fun i => Err (M + i) (s (M + i)) (eta (M + i)) (xi (M + i))) ≤ T)
    (hSmall : E M + T < 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ H : ℕ, ε ≤ Gap H := by
  have htel := p4Q2PZ37ALZ_originalFixedNorm_linearTailTelescoping
    M s eta xi heta hxi hden hRaw hFull
  obtain ⟨εprefix, hprefixPos, hprefix⟩ :=
    p4Q2PZ37ALT_originalFixedFinitePrefixUniformGap M
  let εtail : ℝ := (1 - (E M + T)) / 2
  have htailPos : 0 < εtail := by
    dsimp [εtail]
    linarith only [hSmall]
  refine ⟨min εprefix εtail, lt_min hprefixPos htailPos, ?_⟩
  intro H
  by_cases hHM : H ≤ M
  · exact (min_le_left _ _).trans (hprefix H hHM)
  · let n : ℕ := H - M
    have hidx : M + n = H := by dsimp [n]; omega
    have ht := htel n
    rw [hidx] at ht
    have hnorm : E H ≤ E M + T := by
      have hs := htotal n
      linarith only [ht, hs]
    have hsq : E H ^ 2 ≤ E H := by
      have hr0 := p4Q2PZ37ALY_originalFixedExcitedNorm_nonneg H
      have hr1 := p4Q2PZ37ALY_originalFixedExcitedNorm_le_one H
      have hproduct : 0 ≤ E H * (1 - E H) :=
        mul_nonneg hr0 (sub_nonneg.mpr hr1)
      nlinarith only [hproduct]
    have hgap := p4Q2PZ37ALT_originalFixedGap_ge_half_squaredDefect H
    rw [p4Q2PZ37ALV_deficit_eq_one_sub_excitedNormSq H,
      ← p4Q2PZ37ALY_originalFixedExcitedNorm_sq_eq_Q H] at hgap
    have hmin : min εprefix εtail ≤ εtail := min_le_right _ _
    dsimp [εtail] at hmin
    linarith only [hmin, hgap, hsq, hnorm]

/-- A GEOMETRIC bound directly on the ALY linear relative error is
enough when its total C/(1-rho) fits below 1-r_M. This still requires
a separate genuine Wilson model estimate for every tail volume. -/
theorem p4Q2PZ37ALZ_uniformGap_of_tailGeometricLinearRelativeError
    (M : ℕ) (s eta xi : ℕ → ℝ) (C rho : ℝ)
    (heta : ∀ H : ℕ, 0 ≤ eta H)
    (hxi : ∀ H : ℕ, 0 ≤ xi H)
    (hden : ∀ H : ℕ, 0 < s H * Full H - xi H)
    (hRaw : ∀ H : ℕ, Raw (H + 1) ≤ s H * Raw H + eta H)
    (hFull : ∀ H : ℕ, s H * Full H - xi H ≤ Full (H + 1))
    (hC : 0 ≤ C) (hrho0 : 0 ≤ rho) (hrho1 : rho < 1)
    (hSmall : C < (1 - rho) * (1 - E M))
    (hGeom : ∀ n : ℕ,
      Err (M + n) (s (M + n)) (eta (M + n)) (xi (M + n))
        ≤ C * rho ^ n) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ H : ℕ, ε ≤ Gap H := by
  have hsums : ∀ n : ℕ,
      (Finset.range n).sum
        (fun i => Err (M + i) (s (M + i)) (eta (M + i)) (xi (M + i)))
        ≤ C / (1 - rho) := by
    intro n
    calc
      (Finset.range n).sum
          (fun i => Err (M + i) (s (M + i)) (eta (M + i)) (xi (M + i)))
          ≤ (Finset.range n).sum (fun i => C * rho ^ i) := by
              apply Finset.sum_le_sum
              intro i hi
              exact hGeom i
      _ ≤ C / (1 - rho) :=
        p4Q2PZ37ALV_geometricFiniteSum_le C rho hC hrho0 hrho1 n
  have hT : E M + C / (1 - rho) < 1 := by
    have hc : C / (1 - rho) < 1 - E M := by
      apply (div_lt_iff₀ (sub_pos.mpr hrho1)).2
      calc
        C < (1 - rho) * (1 - E M) := hSmall
        _ = (1 - E M) * (1 - rho) := by ring
    linarith only [hc]
  exact p4Q2PZ37ALZ_uniformGap_of_tailLinearRelativeErrorBudget
    M s eta xi (C / (1 - rho)) heta hxi hden hRaw hFull hsums hT

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALZ_generic_linearNormTelescoping
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALZ_generic_linearNormTailTelescoping
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALZ_originalFixedNorm_linearTelescoping
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALZ_originalFixedNorm_linearTailTelescoping
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALZ_uniformGap_of_linearRelativeErrorBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALZ_uniformGap_of_tailLinearRelativeErrorBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALZ_uniformGap_of_tailGeometricLinearRelativeError
