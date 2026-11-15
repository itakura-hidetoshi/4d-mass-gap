import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFixedBeta0LinearRelativeErrorBudgetV5_PZ37ALZ
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AMA — sharpness obstruction of original Wilson scaled relative loss

For the UNCHANGED genuine SU(2) fixed-beta0=log(3/2)/64 physical transfer,
ALY/ALZ use two-volume true scalar raw/full inequalities containing a free
common scale s_H and two nonnegative physical remainder bounds eta_H, xi_H.

A choice of scale alone CANNOT prove physical summability.
The exact unavoidable per-step ALY cost is at least
  max(||R_(H+1)|| - ||R_H||, 0).
Moreover, this bound is SHARP as a *formal scalar witness*: choosing
  s_H = ||P_(H+1)|| / ||P_H||,  xi_H=0,
  eta_H = ||P_(H+1)|| * max(||R_(H+1)||-||R_H||, 0)
produces an admissible step cost equal to that positive increment.

This sharp witness is deliberately NON-PREDICTIVE: eta_H is defined using
the unknown NEXT-volume excited norm. It supplies no independent physical
Wilson kernel estimate, no decay or summability, and no mass gap.
Instead it isolates the circularity that would arise if one treated the
mere existence of scale/error witnesses as a genuine mixing estimate.

An all-volume positive-variation lower bound is then proved and can refute
proposed ALZ total budgets independently of the selected common scales.
Only REAL scalar quantities are compared; original distinct H-dependent
Hilbert carriers are never identified or subtracted. All existing original
Wilson/Haar/AJA definitions, Lean/mathlib pins, public roots, theorems and
CI workflows remain unchanged.
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

/-- Even with a free shared scale and slack variables, the ALY
relative cost cannot be smaller than the actual positive norm increment.
The normalized current-volume scalar must be in [0,1]. -/
theorem p4Q2PZ37AMA_generic_scaledCost_ge_positiveIncrease
    (p pn r rn s eta xi : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hpn : 0 < pn) (heta : 0 ≤ eta) (hxi : 0 ≤ xi)
    (hden : 0 < s * p - xi)
    (hRaw : pn * rn ≤ s * (p * r) + eta)
    (hFull : s * p - xi ≤ pn) :
    max (rn - r) 0 ≤ (eta + xi) / (s * p - xi) := by
  let t : ℝ := (eta + xi) / (s * p - xi)
  have ht : 0 ≤ t := by
    dsimp [t]
    exact div_nonneg (add_nonneg heta hxi) hden.le
  have hCostEq : t * (s * p - xi) = eta + xi := by
    dsimp [t]
    exact div_mul_cancel₀ (eta + xi) (ne_of_gt hden)
  have hCost : eta + xi ≤ t * (s * p - xi) :=
    le_of_eq hCostEq.symm
  have hStep : rn ≤ r + t :=
    p4Q2PZ37ALY_generic_scaledRatio_linearStep
      p pn r rn s eta xi t hr0 hr1 hpn hxi ht hRaw hFull hCost
  change max (rn - r) 0 ≤ t
  apply max_le
  · linarith only [hStep]
  · exact ht

/-- The previous lower bound is exactly sharp on real scalar norm data.
The explicit witness uses the NEXT norm rn itself; its existence does not
supply any independent physical estimate or summable error majorant. -/
theorem p4Q2PZ37AMA_generic_sharpScaledWitness
    (p pn r rn : ℝ) (hp : 0 < p) (hpn : 0 < pn) :
    ∃ s eta xi : ℝ,
      0 < s ∧
      0 ≤ eta ∧ 0 ≤ xi ∧
      0 < s * p - xi ∧
      pn * rn ≤ s * (p * r) + eta ∧
      s * p - xi ≤ pn ∧
      (eta + xi) / (s * p - xi) = max (rn - r) 0 := by
  let s : ℝ := pn / p
  let eta : ℝ := pn * max (rn - r) 0
  let xi : ℝ := 0
  have hs : 0 < s := div_pos hpn hp
  have hScale : s * p = pn := by
    dsimp [s]
    exact div_mul_cancel₀ pn (ne_of_gt hp)
  have heta : 0 ≤ eta := by
    dsimp [eta]
    exact mul_nonneg hpn.le (le_max_right _ _)
  have hxi : 0 ≤ xi := by
    dsimp [xi]
    norm_num
  have hden : 0 < s * p - xi := by
    rw [hScale]
    dsimp [xi]
    linarith only [hpn]
  have hsp : s * (p * r) = pn * r := by
    calc
      s * (p * r) = (s * p) * r := by ring
      _ = pn * r := by rw [hScale]
  have hRaw : pn * rn ≤ s * (p * r) + eta := by
    have hmax : rn - r ≤ max (rn - r) (0 : ℝ) :=
      le_max_left _ _
    have hr : rn ≤ r + max (rn - r) (0 : ℝ) := by
      linarith only [hmax]
    calc
      pn * rn ≤ pn * (r + max (rn - r) 0) :=
        mul_le_mul_of_nonneg_left hr hpn.le
      _ = s * (p * r) + eta := by
        rw [hsp]
        dsimp [eta]
        ring
  have hFull : s * p - xi ≤ pn := by
    rw [hScale]
    dsimp [xi]
    linarith
  have hCost : (eta + xi) / (s * p - xi) = max (rn - r) 0 := by
    rw [hScale]
    dsimp [eta, xi]
    simp only [add_zero, sub_zero]
    field_simp [hpn.ne'] <;> ring
  exact ⟨s, eta, xi, hs, heta, hxi, hden, hRaw, hFull, hCost⟩

/-- Genuine unmodified original-beta0 Wilson scalar norms retain the
positive-increment obstruction for EVERY admissible ALY error choice. -/
theorem p4Q2PZ37AMA_originalFixedScaledCost_ge_positiveIncrease
    (H : ℕ) (s eta xi : ℝ)
    (heta : 0 ≤ eta) (hxi : 0 ≤ xi)
    (hden : 0 < s * Full H - xi)
    (hRaw : Raw (H + 1) ≤ s * Raw H + eta)
    (hFull : s * Full H - xi ≤ Full (H + 1)) :
    max (E (H + 1) - E H) 0 ≤ Err H s eta xi := by
  have hStep :=
    p4Q2PZ37ALY_originalFixedExcitedNorm_scaledStep_le
      H s eta xi heta hxi hden hRaw hFull
  have hCostNonneg :=
    p4Q2PZ37ALY_originalFixedRelativeStepError_nonneg
      H s eta xi heta hxi hden
  apply max_le
  · linarith only [hStep]
  · exact hCostNonneg

/-- The same actual Wilson scalar data admits a sharp formally constructed
scale/error witness. eta uses the next excited norm and therefore this
statement is NOT an independently proved physical mixing bound. -/
theorem p4Q2PZ37AMA_originalFixedSharpScaledWitness (H : ℕ) :
    ∃ s eta xi : ℝ,
      0 < s ∧ 0 ≤ eta ∧ 0 ≤ xi ∧
      0 < s * Full H - xi ∧
      Raw (H + 1) ≤ s * Raw H + eta ∧
      s * Full H - xi ≤ Full (H + 1) ∧
      Err H s eta xi = max (E (H + 1) - E H) 0 := by
  obtain ⟨s, eta, xi, hs, heta, hxi, hden, hRawScalar,
      hFull, hCost⟩ :=
    p4Q2PZ37AMA_generic_sharpScaledWitness
      (Full H) (Full (H + 1)) (E H) (E (H + 1))
      (p4Q2PZ37ALX_originalFixedFullNorm_pos H)
      (p4Q2PZ37ALX_originalFixedFullNorm_pos (H + 1))
  refine ⟨s, eta, xi, hs, heta, hxi, hden, ?_, hFull, ?_⟩
  · rw [p4Q2PZ37ALX_originalFixedRawExcitation_norm_eq (H + 1),
      p4Q2PZ37ALX_originalFixedRawExcitation_norm_eq H]
    change Full (H + 1) * E (H + 1) ≤
      s * (Full H * E H) + eta
    exact hRawScalar
  · change (eta + xi) / (s * Full H - xi) =
      max (E (H + 1) - E H) 0
    exact hCost

/-- Unavoidable cumulative original Wilson normalized norm variation.
No selection of scale-dependent ALY error bounds can undercut this
true observed positive variation. -/
theorem p4Q2PZ37AMA_originalFixedPositiveVariation_le_scaledBudget
    (N : ℕ) (s eta xi : ℕ → ℝ)
    (heta : ∀ H : ℕ, 0 ≤ eta H)
    (hxi : ∀ H : ℕ, 0 ≤ xi H)
    (hden : ∀ H : ℕ, 0 < s H * Full H - xi H)
    (hRaw : ∀ H : ℕ, Raw (H + 1) ≤ s H * Raw H + eta H)
    (hFull : ∀ H : ℕ, s H * Full H - xi H ≤ Full (H + 1)) :
    (Finset.range N).sum
      (fun H => max (E (H + 1) - E H) 0) ≤
    (Finset.range N).sum
      (fun H => Err H (s H) (eta H) (xi H)) := by
  apply Finset.sum_le_sum
  intro H hH
  exact p4Q2PZ37AMA_originalFixedScaledCost_ge_positiveIncrease
    H (s H) (eta H) (xi H)
    (heta H) (hxi H) (hden H) (hRaw H) (hFull H)

/-- A genuine observed positive-variation excess falsifies a proposed
uniform linear scaled-error budget, regardless of common scale choice. -/
theorem p4Q2PZ37AMA_originalFixedExcessVariation_refutes_budget
    (N : ℕ) (s eta xi : ℕ → ℝ) (T : ℝ)
    (heta : ∀ H : ℕ, 0 ≤ eta H)
    (hxi : ∀ H : ℕ, 0 ≤ xi H)
    (hden : ∀ H : ℕ, 0 < s H * Full H - xi H)
    (hRaw : ∀ H : ℕ, Raw (H + 1) ≤ s H * Raw H + eta H)
    (hFull : ∀ H : ℕ, s H * Full H - xi H ≤ Full (H + 1))
    (hExcess : T <
      (Finset.range N).sum
        (fun H => max (E (H + 1) - E H) 0)) :
    ¬ (∀ M : ℕ,
      (Finset.range M).sum
        (fun H => Err H (s H) (eta H) (xi H)) ≤ T) := by
  intro htotal
  have hLower :=
    p4Q2PZ37AMA_originalFixedPositiveVariation_le_scaledBudget
      N s eta xi heta hxi hden hRaw hFull
  have hUpper := htotal N
  linarith only [hLower, hUpper, hExcess]

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMA_generic_scaledCost_ge_positiveIncrease
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMA_generic_sharpScaledWitness
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMA_originalFixedScaledCost_ge_positiveIncrease
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMA_originalFixedSharpScaledWitness
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMA_originalFixedPositiveVariation_le_scaledBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AMA_originalFixedExcessVariation_refutes_budget
