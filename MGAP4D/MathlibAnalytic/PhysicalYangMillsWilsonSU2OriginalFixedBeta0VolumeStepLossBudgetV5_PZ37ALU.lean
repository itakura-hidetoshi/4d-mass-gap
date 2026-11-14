import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFixedBeta0FinitePrefixTailDescentV5_PZ37ALT
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ALU — exact original beta0 volume-step deficit variation

The *actual* physical original Wilson SU(2) normalized transfer restrictions
R_H(beta0) act on H-dependent Hilbert spaces. There is NO canonical
subtraction R_(H+1) - R_H in these statements.

The previous ALN / ALT results, however, construct the same real-valued
squared deficit for every finite H:
   delta_H = 1 - ||R_H(beta0)||^2 > 0,
   gap_H >= delta_H / 2.

This file introduces the smallest NONNEGATIVE scalar one-step downward loss
   L_H := max(0, delta_H - delta_(H+1))
and its finite cumulative downward variation
   V_H := sum_{i=0}^{H-1} L_i.

An exact telescoping inequality, not a spectral approximation, gives
   delta_H >= delta_0 - V_H,
   gap_H >= (delta_0 - V_H)/2.

If a separately certified uniform bound V_H <= B < delta_0 holds for every
finite H, then the original fixed-beta0 Wilson gap is uniformly positive:
   gap_H >= (delta_0 - B)/2 > 0.

A second result permits independent physically derived nonnegative step
budgets b_H >= 0 with delta_(H+1) >= delta_H - b_H and a uniform partial-sum
budget. This is a DIFFERENT, step-local candidate route to large-H control,
not the overstrong floor-normalized all-H raw moment requirement in ALN.

IMPORTANT: Neither V_H <= B < delta_0 nor a summable majorant b_H is
asserted for the actual original Wilson model. ALM's high-temperature
obstruction is preserved; no unconditional all-H or continuum mass gap
is inferred. All operators, Haar measures, physical beta0, normalization,
existing theorems, and imports are unchanged.
-/

namespace MGAP4D.MathlibAnalytic

open scoped InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace GroundStatePosteriorJoint

local notation "D" => p4Q2PZ37ALN_originalFixedTopOrthogonalSquaredGap
local notation "Gap" => p4Q2PZ37ALT_originalFixedGapAt

/-- Exactly the positive part of the drop in physical original beta0
squared spectral deficit between adjacent finite volume indices. -/
noncomputable def p4Q2PZ37ALU_originalFixedOneStepDownwardLoss
    (H : ℕ) : ℝ :=
  max (D H - D (H + 1)) 0

theorem p4Q2PZ37ALU_originalFixedOneStepDownwardLoss_nonneg
    (H : ℕ) :
    0 ≤ p4Q2PZ37ALU_originalFixedOneStepDownwardLoss H := by
  unfold p4Q2PZ37ALU_originalFixedOneStepDownwardLoss
  exact le_max_right _ _

/-- Without comparing Hilbert vectors across different H, the REAL scalar
deficit is bounded across a one-step change by its actual downward loss. -/
theorem p4Q2PZ37ALU_originalFixedOneStepDownwardLoss_controlsDeficit
    (H : ℕ) :
    D H ≤
      D (H + 1) + p4Q2PZ37ALU_originalFixedOneStepDownwardLoss H := by
  have hd :
      D H - D (H + 1) ≤
        p4Q2PZ37ALU_originalFixedOneStepDownwardLoss H := by
    unfold p4Q2PZ37ALU_originalFixedOneStepDownwardLoss
    exact le_max_left _ _
  linarith

/-- L_H is the SHARP minimal nonnegative scalar penalty needed to bound
the original fixed-beta0 deficit degradation in this one step. -/
theorem p4Q2PZ37ALU_originalFixedOneStepDownwardLoss_le_iff
    (H : ℕ) (b : ℝ) (hb : 0 ≤ b) :
    p4Q2PZ37ALU_originalFixedOneStepDownwardLoss H ≤ b ↔
      D H ≤ D (H + 1) + b := by
  constructor
  · intro h
    have hs :=
      p4Q2PZ37ALU_originalFixedOneStepDownwardLoss_controlsDeficit H
    linarith
  · intro h
    unfold p4Q2PZ37ALU_originalFixedOneStepDownwardLoss
    apply max_le
    · linarith
    · exact hb

/-- Exact total downward variation up through the H-th volume.
It is NOT assumed bounded as H tends to infinity. -/
noncomputable def p4Q2PZ37ALU_originalFixedDownwardVariation
    (H : ℕ) : ℝ :=
  (Finset.range H).sum p4Q2PZ37ALU_originalFixedOneStepDownwardLoss

theorem p4Q2PZ37ALU_originalFixedDownwardVariation_zero :
    p4Q2PZ37ALU_originalFixedDownwardVariation 0 = 0 := by
  simp [p4Q2PZ37ALU_originalFixedDownwardVariation]

theorem p4Q2PZ37ALU_originalFixedDownwardVariation_succ
    (H : ℕ) :
    p4Q2PZ37ALU_originalFixedDownwardVariation (H + 1) =
      p4Q2PZ37ALU_originalFixedDownwardVariation H +
        p4Q2PZ37ALU_originalFixedOneStepDownwardLoss H := by
  change
    (Finset.range (H + 1)).sum p4Q2PZ37ALU_originalFixedOneStepDownwardLoss =
      (Finset.range H).sum p4Q2PZ37ALU_originalFixedOneStepDownwardLoss +
        p4Q2PZ37ALU_originalFixedOneStepDownwardLoss H
  exact Finset.sum_range_succ _ _

theorem p4Q2PZ37ALU_originalFixedDownwardVariation_nonneg
    (H : ℕ) :
    0 ≤ p4Q2PZ37ALU_originalFixedDownwardVariation H := by
  induction H with
  | zero =>
      rw [p4Q2PZ37ALU_originalFixedDownwardVariation_zero]
  | succ n ih =>
      rw [p4Q2PZ37ALU_originalFixedDownwardVariation_succ]
      have hd := p4Q2PZ37ALU_originalFixedOneStepDownwardLoss_nonneg n
      linarith

theorem p4Q2PZ37ALU_originalFixedDownwardVariation_mono
    (H : ℕ) :
    p4Q2PZ37ALU_originalFixedDownwardVariation H ≤
      p4Q2PZ37ALU_originalFixedDownwardVariation (H + 1) := by
  rw [p4Q2PZ37ALU_originalFixedDownwardVariation_succ]
  have hd := p4Q2PZ37ALU_originalFixedOneStepDownwardLoss_nonneg H
  linarith

/-- Exact finite-volume descent certificate. Each term is a REAL scalar
belonging to the unchanged physical Wilson model at the original beta0. -/
theorem p4Q2PZ37ALU_originalFixedSquaredDeficit_telescoping
    (H : ℕ) :
    D 0 ≤
      D H + p4Q2PZ37ALU_originalFixedDownwardVariation H := by
  induction H with
  | zero =>
      rw [p4Q2PZ37ALU_originalFixedDownwardVariation_zero]
      simp
  | succ n ih =>
      rw [p4Q2PZ37ALU_originalFixedDownwardVariation_succ]
      have hstep :=
        p4Q2PZ37ALU_originalFixedOneStepDownwardLoss_controlsDeficit n
      linarith

/-- Unconditional, volume-by-volume quantitative estimate from the exact
accumulated original-beta0 deficit losses. It may be trivial when V_H is large;
no all-H positivity is falsely asserted. -/
theorem p4Q2PZ37ALU_originalFixedGap_ge_initialDeficit_sub_variation
    (H : ℕ) :
    (D 0 - p4Q2PZ37ALU_originalFixedDownwardVariation H) / 2 ≤ Gap H := by
  have htel := p4Q2PZ37ALU_originalFixedSquaredDeficit_telescoping H
  have hgap := p4Q2PZ37ALT_originalFixedGap_ge_half_squaredDefect H
  linarith

/-- Complementary observable obstruction: if delta_H drops to at most r,
the cumulative actual downward-variation budget must have spent at least
delta_0-r. -/
theorem p4Q2PZ37ALU_originalFixedVariation_ge_of_deficit_le
    (H : ℕ) (r : ℝ)
    (hsmall : D H ≤ r) :
    D 0 - r ≤ p4Q2PZ37ALU_originalFixedDownwardVariation H := by
  have htel := p4Q2PZ37ALU_originalFixedSquaredDeficit_telescoping H
  linarith

/-- An explicitly unproved common bound on the actual ORIGINAL Wilson
downward variation suffices for a uniform positive beta0 gap. -/
theorem p4Q2PZ37ALU_originalFixedUniformGap_of_variationBudget
    (B : ℝ)
    (hbudget : ∀ H : ℕ,
      p4Q2PZ37ALU_originalFixedDownwardVariation H ≤ B)
    (hstrict : B < D 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ H : ℕ, ε ≤ Gap H := by
  refine ⟨(D 0 - B) / 2, by linarith, ?_⟩
  intro H
  have hbound :=
    p4Q2PZ37ALU_originalFixedGap_ge_initialDeficit_sub_variation H
  have hV := hbudget H
  linarith

/-- Stepwise estimates on the true real deficits can be supplied by
independent Wilson kernel analyses; they never subtract vectors/operators
across H-dependent physical Hilbert spaces. -/
theorem p4Q2PZ37ALU_originalFixedTelescoping_of_stepwiseBound
    (b : ℕ → ℝ)
    (hstep : ∀ H : ℕ, D H ≤ D (H + 1) + b H) :
    ∀ H : ℕ, D 0 ≤ D H + (Finset.range H).sum b := by
  intro H
  induction H with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hs := hstep n
      linarith

/-- The alternative sufficient condition consists of independently
proved NONNEGATIVE one-step Wilson deficit costs b_H with a total bound
strictly smaller than delta_0. Neither premise is supplied here.
The all-H conclusion is conditional, not a solved mass-gap problem. -/
theorem p4Q2PZ37ALU_originalFixedUniformGap_of_stepwiseBudget
    (b : ℕ → ℝ) (B : ℝ)
    (hb : ∀ H : ℕ, 0 ≤ b H)
    (hstep : ∀ H : ℕ, D H ≤ D (H + 1) + b H)
    (htotal : ∀ H : ℕ, (Finset.range H).sum b ≤ B)
    (hstrict : B < D 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ H : ℕ, ε ≤ Gap H := by
  have htel :=
    p4Q2PZ37ALU_originalFixedTelescoping_of_stepwiseBound b hstep
  have hB0 : 0 ≤ B := by
    have hOne : b 0 ≤ B := by
      simpa [Finset.sum_range_succ] using (htotal 1)
    exact (hb 0).trans hOne
  refine ⟨(D 0 - B) / 2, by linarith, ?_⟩
  intro H
  have hH := htel H
  have hsum := htotal H
  have hgap := p4Q2PZ37ALT_originalFixedGap_ge_half_squaredDefect H
  linarith

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALU_originalFixedOneStepDownwardLoss
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALU_originalFixedOneStepDownwardLoss_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALU_originalFixedOneStepDownwardLoss_controlsDeficit
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALU_originalFixedOneStepDownwardLoss_le_iff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALU_originalFixedDownwardVariation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALU_originalFixedDownwardVariation_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALU_originalFixedDownwardVariation_succ
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALU_originalFixedDownwardVariation_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALU_originalFixedDownwardVariation_mono
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALU_originalFixedSquaredDeficit_telescoping
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALU_originalFixedGap_ge_initialDeficit_sub_variation
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALU_originalFixedVariation_ge_of_deficit_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALU_originalFixedUniformGap_of_variationBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALU_originalFixedTelescoping_of_stepwiseBound
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALU_originalFixedUniformGap_of_stepwiseBudget
