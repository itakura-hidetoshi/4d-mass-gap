import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFixedBeta0LinearRelativeErrorBudgetV5_PZ37ALZ
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AMA — exact lower obstruction for scaled Wilson relative-error costs

ALX proved the genuine same-volume original Wilson identity
  a_H = p_H * r_H,
where a_H=||A_H||, p_H=||P_H||>0, r_H=||R_H||<=1 at the actual
prescribed original SU(2) beta0=log(3/2)/64.

ALY derived r_(H+1)<=r_H+t_H from physically INDEPENDENT paired
raw/full scalar comparisons around a common positive scale s_H.

This file establishes that *arbitrary optimization of s_H alone*
cannot produce physical control. Every admissible ALY cost satisfies
  max(r_(H+1)-r_H,0) <= t_H.
Conversely, a canonical algebraic choice
  s_H = p_(H+1)/p_H,
  xi_H = 0,
  eta_H = p_(H+1)*max(r_(H+1)-r_H,0)
meets the paired scalar inequalities with equality in the relative cost
  t_H = max(r_(H+1)-r_H,0).

This canonical eta uses the UNKNOWN next-volume excited norm itself.
It is NOT an independent Wilson physical estimate, norm decay or
cross-H Hilbert embedding. The exact optimum is a structural OBSTRUCTION
to trying to obtain ALZ's strict summable total merely by selecting s_H.

No changes to original P/A/R/K, Haar, AJA, beta0, pinned Lean/mathlib,
roots or earlier theorem assumptions. These are finite-volume actual
real-scalar calculations; continuum Yang-Mills gap remains OPEN.
-/

namespace MGAP4D.MathlibAnalytic

open scoped InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace GroundStatePosteriorJoint

local notation "E" => p4Q2PZ37ALY_originalFixedExcitedNorm
local notation "Full" => p4Q2PZ37ALX_originalFixedFullNorm
local notation "Raw" => p4Q2PZ37ALX_originalFixedRawExcitationNorm
local notation "Err" => p4Q2PZ37ALY_originalFixedRelativeStepError

/-- The genuine positive full norm at each volume gives an exact
scalar scale for the next-volume full norm. Nothing is rescaled in
the original physical operator itself. -/
theorem p4Q2PZ37AMA_generic_fullNormCanonicalScale
    (p pn : ℝ) (hp : 0 < p) (hpn : 0 < pn) :
    0 < pn / p ∧ (pn / p) * p = pn := by
  constructor
  · exact div_pos hpn hp
  · exact div_mul_cancel₀ pn (ne_of_gt hp)

/-- The positive part of a real increase is the smallest
nonnegative additive scalar step that bounds this increase. -/
theorem p4Q2PZ37AMA_generic_positiveIncreaseStep
    (r rn : ℝ) :
    0 ≤ max (rn - r) 0 ∧ rn ≤ r + max (rn - r) 0 := by
  constructor
  · exact le_max_right _ _
  · have h := le_max_left (rn - r) (0 : ℝ)
    linarith

/-- A canonical positive scalar scale and paired nonnegative errors
always exist, but eta is defined USING rn. Thus this is an algebraic
witness, not a physically independent volume comparison. -/
theorem p4Q2PZ37AMA_generic_canonicalScaledCostWitness
    (p pn r rn : ℝ) (hp : 0 < p) (hpn : 0 < pn) :
    ∃ s eta xi : ℝ,
      0 < s ∧ 0 ≤ eta ∧ 0 ≤ xi ∧
      0 < s * p - xi ∧
      pn * rn ≤ s * (p * r) + eta ∧
      s * p - xi ≤ pn ∧
      (eta + xi) / (s * p - xi) = max (rn - r) 0 := by
  let s : ℝ := pn / p
  let t : ℝ := max (rn - r) 0
  let eta : ℝ := pn * t
  have hs : 0 < s := by
    dsimp [s]
    exact div_pos hpn hp
  have hsp : s * p = pn := by
    dsimp [s]
    exact div_mul_cancel₀ pn (ne_of_gt hp)
  have ht : 0 ≤ t := by
    dsimp [t]
    exact le_max_right _ _
  have hrt : rn ≤ r + t := by
    have hx : rn - r ≤ t := by
      dsimp [t]
      exact le_max_left _ _
    linarith
  have hnorm : s * (p * r) = pn * r := by
    calc
      s * (p * r) = (s * p) * r := by ring
      _ = pn * r := by rw [hsp]
  have hraw : pn * rn ≤ s * (p * r) + eta := by
    calc
      pn * rn ≤ pn * (r + t) := mul_le_mul_of_nonneg_left hrt hpn.le
      _ = pn * r + pn * t := by ring
      _ = s * (p * r) + eta := by
        dsimp [eta]
        rw [hnorm]
  have hden : 0 < s * p - (0 : ℝ) := by
    simpa only [sub_zero, hsp] using hpn
  have hfull : s * p - (0 : ℝ) ≤ pn := by
    simpa only [sub_zero, hsp] using (le_refl pn)
  have hcost : (eta + (0 : ℝ)) / (s * p - 0) = t := by
    rw [add_zero, sub_zero, hsp]
    dsimp [eta]
    field_simp [ne_of_gt hpn]
  exact ⟨s, eta, 0, hs, mul_nonneg hpn.le ht,
    le_refl (0 : ℝ), hden, hraw, hfull, hcost⟩

/-- Every admissible paired scaled raw/full estimate pays at least
the TRUE positive real norm increase, irrespective of the scale. -/
theorem p4Q2PZ37AMA_generic_anyScaledCost_ge_positiveIncrease
    (p pn r rn s eta xi : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hpn : 0 < pn)
    (heta : 0 ≤ eta) (hxi : 0 ≤ xi)
    (hden : 0 < s * p - xi)
    (hraw : pn * rn ≤ s * (p * r) + eta)
    (hfull : s * p - xi ≤ pn) :
    max (rn - r) 0 ≤ (eta + xi) / (s * p - xi) := by
  let t : ℝ := (eta + xi) / (s * p - xi)
  have ht : 0 ≤ t := by
    dsimp [t]
    exact div_nonneg (add_nonneg heta hxi) hden.le
  have hcostEq : t * (s * p - xi) = eta + xi := by
    dsimp [t]
    exact div_mul_cancel₀ (eta + xi) (ne_of_gt hden)
  have hs := p4Q2PZ37ALY_generic_scaledRatio_linearStep
    p pn r rn s eta xi t hr0 hr1 hpn hxi ht
    hraw hfull (le_of_eq hcostEq.symm)
  have hgrowth : rn - r ≤ t := by linarith only [hs]
  have hbound : max (rn - r) 0 ≤ t := max_le hgrowth ht
  simpa [t] using hbound

/-- The actual positive increase in the unchanged original Wilson
normalized full-top-orthogonal transfer norm between adjacent volumes.
A real scalar, not a difference of operators from different Hilbert spaces. -/
noncomputable def p4Q2PZ37AMA_originalFixedSharpPositiveNormIncrease
    (H : ℕ) : ℝ :=
  max (E (H + 1) - E H) 0

theorem p4Q2PZ37AMA_originalFixedSharpPositiveNormIncrease_nonneg
    (H : ℕ) :
    0 ≤ p4Q2PZ37AMA_originalFixedSharpPositiveNormIncrease H := by
  unfold p4Q2PZ37AMA_originalFixedSharpPositiveNormIncrease
  exact le_max_right _ _

/-- For the TRUE physical Wilson norms every ALY scaled comparison
cost dominates the actual positive normalized excitation-norm growth. -/
theorem p4Q2PZ37AMA_originalFixedSharpIncrease_le_anyScaledCost
    (H : ℕ) (s eta xi : ℝ)
    (heta : 0 ≤ eta) (hxi : 0 ≤ xi)
    (hden : 0 < s * Full H - xi)
    (hraw : Raw (H + 1) ≤ s * Raw H + eta)
    (hfull : s * Full H - xi ≤ Full (H + 1)) :
    p4Q2PZ37AMA_originalFixedSharpPositiveNormIncrease H ≤
      Err H s eta xi := by
  have hRawEq :
      Full (H + 1) * E (H + 1) ≤ s * (Full H * E H) + eta := by
    have h := hraw
    rw [p4Q2PZ37ALX_originalFixedRawExcitation_norm_eq (H + 1),
      p4Q2PZ37ALX_originalFixedRawExcitation_norm_eq H] at h
    change Full (H + 1) * E (H + 1) ≤
      s * (Full H * E H) + eta at h
    exact h
  change max (E (H + 1) - E H) 0 ≤
    (eta + xi) / (s * Full H - xi)
  exact p4Q2PZ37AMA_generic_anyScaledCost_ge_positiveIncrease
    (Full H) (Full (H + 1)) (E H) (E (H + 1))
    s eta xi
    (p4Q2PZ37ALY_originalFixedExcitedNorm_nonneg H)
    (p4Q2PZ37ALY_originalFixedExcitedNorm_le_one H)
    (p4Q2PZ37ALX_originalFixedFullNorm_pos (H + 1))
    heta hxi hden hRawEq hfull

/-- The canonical *algebraic* scale s=p_(H+1)/p_H realizes the
EXACT sharp scalar cost. The eta witness depends on the unknown next
excited norm and therefore is NOT independent Wilson physical input. -/
theorem p4Q2PZ37AMA_originalFixedCanonicalScaledCost_eq_sharpIncrease
    (H : ℕ) :
    ∃ s eta xi : ℝ,
      0 < s ∧ 0 ≤ eta ∧ 0 ≤ xi ∧
      0 < s * Full H - xi ∧
      Raw (H + 1) ≤ s * Raw H + eta ∧
      s * Full H - xi ≤ Full (H + 1) ∧
      Err H s eta xi =
        p4Q2PZ37AMA_originalFixedSharpPositiveNormIncrease H := by
  obtain ⟨s, eta, xi, hs, heta, hxi, hden, hraw, hfull, hcost⟩ :=
    p4Q2PZ37AMA_generic_canonicalScaledCostWitness
      (Full H) (Full (H + 1)) (E H) (E (H + 1))
      (p4Q2PZ37ALX_originalFixedFullNorm_pos H)
      (p4Q2PZ37ALX_originalFixedFullNorm_pos (H + 1))
  refine ⟨s, eta, xi, hs, heta, hxi, hden, ?_, hfull, ?_⟩
  · rw [p4Q2PZ37ALX_originalFixedRawExcitation_norm_eq (H + 1),
      p4Q2PZ37ALX_originalFixedRawExcitation_norm_eq H]
    change Full (H + 1) * E (H + 1) ≤
      s * (Full H * E H) + eta
    exact hraw
  · change (eta + xi) / (s * Full H - xi) =
      max (E (H + 1) - E H) 0
    exact hcost

/-- Genuine Wilson positive normalized-growth cumulative variation is
a necessary LOWER budget for every sequence of ALY physical scalar
costs. No all-H summability bound is asserted. -/
theorem p4Q2PZ37AMA_originalFixedSharpVariation_le_anyScaledCostSum
    (s eta xi : ℕ → ℝ) (H : ℕ)
    (heta : ∀ i : ℕ, 0 ≤ eta i)
    (hxi : ∀ i : ℕ, 0 ≤ xi i)
    (hden : ∀ i : ℕ, 0 < s i * Full i - xi i)
    (hraw : ∀ i : ℕ, Raw (i + 1) ≤ s i * Raw i + eta i)
    (hfull : ∀ i : ℕ, s i * Full i - xi i ≤ Full (i + 1)) :
    (Finset.range H).sum p4Q2PZ37AMA_originalFixedSharpPositiveNormIncrease ≤
      (Finset.range H).sum (fun i => Err i (s i) (eta i) (xi i)) := by
  apply Finset.sum_le_sum
  intro i hi
  exact p4Q2PZ37AMA_originalFixedSharpIncrease_le_anyScaledCost
    i (s i) (eta i) (xi i)
    (heta i) (hxi i) (hden i) (hraw i) (hfull i)

/-- A sufficiently large observed cumulative positive norm growth
REFUTES ALZ's proposed strict linear COST budget, for any common
scale and admissible paired error estimates. This obstruction is to
the ALZ sufficient criterion, NOT a proof of no Yang-Mills mass gap. -/
theorem p4Q2PZ37AMA_noSmallLinearCostBudget_of_sharpVariation
    (s eta xi : ℕ → ℝ) (H : ℕ) (T : ℝ)
    (heta : ∀ i : ℕ, 0 ≤ eta i)
    (hxi : ∀ i : ℕ, 0 ≤ xi i)
    (hden : ∀ i : ℕ, 0 < s i * Full i - xi i)
    (hraw : ∀ i : ℕ, Raw (i + 1) ≤ s i * Raw i + eta i)
    (hfull : ∀ i : ℕ, s i * Full i - xi i ≤ Full (i + 1))
    (hvariation : 1 - E 0 ≤
      (Finset.range H).sum
        p4Q2PZ37AMA_originalFixedSharpPositiveNormIncrease)
    (hbudget :
      (Finset.range H).sum
        (fun i => Err i (s i) (eta i) (xi i)) ≤ T)
    (hsmall : E 0 + T < 1) : False := by
  have hv := p4Q2PZ37AMA_originalFixedSharpVariation_le_anyScaledCostSum
    s eta xi H heta hxi hden hraw hfull
  linarith only [hvariation, hv, hbudget, hsmall]

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMA_generic_fullNormCanonicalScale
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMA_generic_positiveIncreaseStep
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMA_generic_canonicalScaledCostWitness
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMA_generic_anyScaledCost_ge_positiveIncrease
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMA_originalFixedSharpPositiveNormIncrease
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMA_originalFixedSharpPositiveNormIncrease_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMA_originalFixedSharpIncrease_le_anyScaledCost
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMA_originalFixedCanonicalScaledCost_eq_sharpIncrease
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMA_originalFixedSharpVariation_le_anyScaledCostSum
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMA_noSmallLinearCostBudget_of_sharpVariation
