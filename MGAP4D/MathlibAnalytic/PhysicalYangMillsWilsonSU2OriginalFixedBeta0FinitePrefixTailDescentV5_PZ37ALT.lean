import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalHighTemperatureConcreteEightColorFrameV5_PZ37ALS
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFixedWilsonSpectralDefectFloorV5_PZ37ALN
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ALT: exact original beta0, finite-prefix positivity and tail descent

The new result is UNCONDITIONAL for each bounded finite-volume prefix, not a
uniform-in-all-H assertion. The original SU(2) Wilson physical transfer and
fixed beta0 are unchanged. Existing ALN proves on the true full-top-orthogonal
carrier at this exact beta0, for every finite H:

  delta_H = 1 - ||R_H||^2 > 0.

This file proves the exact factorization delta_H = gap_H*(1+||R_H||),
constructs by primitive recursion a strictly positive lower certificate
d_M = min { delta_H : 0 <= H <= M }, and shows
  all H <= M: gap_H >= d_M/2 > 0.

It then isolates the sole remaining tail obstruction: for H>M, an ACTUAL
physical raw Wilson norm bound in terms of ALJ's genuine moment floor F_H
with one 0<=q<1 yields the all-H gap with rate min(d_M/2,1-q)>0.
No all-H tail bound is asserted. No high-temperature s/Harnack cutoff is used
in these results, nor does finite-prefix compactness imply a common all-H rate.

Only one new append-only Lean leaf, preserving all original physics and imports.
-/

namespace MGAP4D.MathlibAnalytic

open scoped InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000

namespace GroundStatePosteriorJoint

local notation "beta0" => p4Q2PZ37ADC_fixedCoupling

/-- Transparent notation for the EXISTING original SU(2) fixed-beta0 gap. -/
noncomputable def p4Q2PZ37ALT_originalFixedGapAt (H : ℕ) : ℝ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
    H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le

section FiniteVolume
variable (H : ℕ)

local notation "R" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
    H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "deltaH" => p4Q2PZ37ALN_originalFixedTopOrthogonalSquaredGap H
local notation "gapH" => p4Q2PZ37ALT_originalFixedGapAt H

/-- Exact, not merely estimated, physical squared-defect factorization. -/
theorem p4Q2PZ37ALT_originalFixedSquaredDefect_eq_gap_mul :
    deltaH = gapH * (1 + ‖R‖) := by
  change 1 - ‖R‖ ^ 2 = (1 - ‖R‖) * (1 + ‖R‖)
  ring

/-- A finite-volume original-beta0 spectral gap is at least half the
strictly positive ALN squared defect; no Harnack estimate is used. -/
theorem p4Q2PZ37ALT_originalFixedGap_ge_half_squaredDefect :
    deltaH / 2 ≤ gapH := by
  change (1 - ‖R‖ ^ 2) / 2 ≤ 1 - ‖R‖
  nlinarith [sq_nonneg (1 - ‖R‖)]

theorem p4Q2PZ37ALT_originalFixedGap_pos :
    0 < gapH := by
  have hd := p4Q2PZ37ALN_originalFixedTopOrthogonalSquaredGap_pos H
  have hg := p4Q2PZ37ALT_originalFixedGap_ge_half_squaredDefect H
  linarith

end FiniteVolume

/-- A canonical positive finite-prefix certificate for the ACTUAL original
beta0. Choosing a value for each finite H is not an all-H estimate. -/
noncomputable def p4Q2PZ37ALT_originalFixedFinitePrefixSquaredFloor : ℕ → ℝ
  | 0 => p4Q2PZ37ALN_originalFixedTopOrthogonalSquaredGap 0
  | n + 1 =>
      min (p4Q2PZ37ALT_originalFixedFinitePrefixSquaredFloor n)
        (p4Q2PZ37ALN_originalFixedTopOrthogonalSquaredGap (n + 1))

theorem p4Q2PZ37ALT_originalFixedFinitePrefixSquaredFloor_pos
    (M : ℕ) :
    0 < p4Q2PZ37ALT_originalFixedFinitePrefixSquaredFloor M := by
  induction M with
  | zero =>
      simpa [p4Q2PZ37ALT_originalFixedFinitePrefixSquaredFloor] using
        (p4Q2PZ37ALN_originalFixedTopOrthogonalSquaredGap_pos 0)
  | succ n ih =>
      change 0 < min
        (p4Q2PZ37ALT_originalFixedFinitePrefixSquaredFloor n)
        (p4Q2PZ37ALN_originalFixedTopOrthogonalSquaredGap (n + 1))
      exact lt_min ih
        (p4Q2PZ37ALN_originalFixedTopOrthogonalSquaredGap_pos (n + 1))

theorem p4Q2PZ37ALT_originalFixedFinitePrefixSquaredFloor_antitone
    (M : ℕ) :
    p4Q2PZ37ALT_originalFixedFinitePrefixSquaredFloor (M + 1) ≤
      p4Q2PZ37ALT_originalFixedFinitePrefixSquaredFloor M := by
  change min (p4Q2PZ37ALT_originalFixedFinitePrefixSquaredFloor M)
    (p4Q2PZ37ALN_originalFixedTopOrthogonalSquaredGap (M + 1)) ≤
      p4Q2PZ37ALT_originalFixedFinitePrefixSquaredFloor M
  exact min_le_left _ _

/-- The recursively constructed certificate bounds EVERY original finite H
in the prefix; the quantifier is checked by induction rather than assumed. -/
theorem p4Q2PZ37ALT_originalFixedFinitePrefixSquaredFloor_le
    (M : ℕ) :
    ∀ H : ℕ, H ≤ M →
      p4Q2PZ37ALT_originalFixedFinitePrefixSquaredFloor M ≤
        p4Q2PZ37ALN_originalFixedTopOrthogonalSquaredGap H := by
  induction M with
  | zero =>
      intro H hH
      have heq : H = 0 := by omega
      subst H
      exact le_rfl
  | succ n ih =>
      intro H hH
      by_cases hlast : H = n + 1
      · subst H
        change min (p4Q2PZ37ALT_originalFixedFinitePrefixSquaredFloor n)
          (p4Q2PZ37ALN_originalFixedTopOrthogonalSquaredGap (n + 1)) ≤
            p4Q2PZ37ALN_originalFixedTopOrthogonalSquaredGap (n + 1)
        exact min_le_right _ _
      · have hprev : H ≤ n := by omega
        exact (p4Q2PZ37ALT_originalFixedFinitePrefixSquaredFloor_antitone n).trans
          (ih H hprev)

/-- Unconditional strictly positive common original-beta0 gap lower bound
for any fixed FINITE collection of volume scales H<=M. -/
theorem p4Q2PZ37ALT_originalFixedFinitePrefixUniformGap
    (M : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ H : ℕ, H ≤ M → ε ≤ p4Q2PZ37ALT_originalFixedGapAt H := by
  refine ⟨p4Q2PZ37ALT_originalFixedFinitePrefixSquaredFloor M / 2,
    div_pos (p4Q2PZ37ALT_originalFixedFinitePrefixSquaredFloor_pos M)
      (by norm_num), ?_⟩
  intro H hH
  have hfloor :=
    p4Q2PZ37ALT_originalFixedFinitePrefixSquaredFloor_le M H hH
  have hgap := p4Q2PZ37ALT_originalFixedGap_ge_half_squaredDefect H
  linarith

/-- An explicit original physical raw Wilson tail condition, referring to
the genuine Wilson operator P_H and genuine ALJ moment floor F_H(beta0).
It is a NEW premise, not asserted to hold at all large H. -/
def p4Q2PZ37ALT_originalFixedTailRawMomentBound
    (M : ℕ) (q : ℝ) : Prop :=
  ∀ H : ℕ, M < H →
    ∀ x :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
        H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le,
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
          (x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)‖ ≤
        q * p4Q2PZ37ALN_originalFixedPhysicalNormMomentFloor H *
          ‖(x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)‖

/-- Non-Harnack tail descent: all finite H<=M are handled WITHOUT premises,
so proving one DIRECT original Wilson raw-moment estimate for H>M suffices.
This does not promote finite-prefix positivity to all-H positivity by itself. -/
theorem p4Q2PZ37ALT_originalFixedTailRawMoment_descent
    (M : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hTail : p4Q2PZ37ALT_originalFixedTailRawMomentBound M q) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ H : ℕ, ε ≤ p4Q2PZ37ALT_originalFixedGapAt H := by
  let ε : ℝ := min
    (p4Q2PZ37ALT_originalFixedFinitePrefixSquaredFloor M / 2)
    (1 - q)
  have hε : 0 < ε := by
    dsimp [ε]
    apply lt_min
    · exact div_pos
        (p4Q2PZ37ALT_originalFixedFinitePrefixSquaredFloor_pos M)
        (by norm_num)
    · linarith
  refine ⟨ε, hε, ?_⟩
  intro H
  by_cases hhead : H ≤ M
  · have hf :=
      p4Q2PZ37ALT_originalFixedFinitePrefixSquaredFloor_le M H hhead
    have hg := p4Q2PZ37ALT_originalFixedGap_ge_half_squaredDefect H
    have hεle :
        ε ≤ p4Q2PZ37ALT_originalFixedFinitePrefixSquaredFloor M / 2 := by
      dsimp [ε]
      exact min_le_left _ _
    linarith
  · have htail : M < H := by omega
    have hgap :=
      (p4Q2PZ37ALN_originalFixedGap_ge_of_rawMomentBound
        H q hq0 hq1 (hTail H htail)).2
    have hεle : ε ≤ 1 - q := by
      dsimp [ε]
      exact min_le_right _ _
    exact hεle.trans hgap

end GroundStatePosteriorJoint
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALT_originalFixedGapAt
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALT_originalFixedSquaredDefect_eq_gap_mul
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALT_originalFixedGap_ge_half_squaredDefect
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALT_originalFixedGap_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALT_originalFixedFinitePrefixSquaredFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALT_originalFixedFinitePrefixSquaredFloor_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALT_originalFixedFinitePrefixSquaredFloor_antitone
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALT_originalFixedFinitePrefixSquaredFloor_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALT_originalFixedFinitePrefixUniformGap
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALT_originalFixedTailRawMomentBound
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALT_originalFixedTailRawMoment_descent
