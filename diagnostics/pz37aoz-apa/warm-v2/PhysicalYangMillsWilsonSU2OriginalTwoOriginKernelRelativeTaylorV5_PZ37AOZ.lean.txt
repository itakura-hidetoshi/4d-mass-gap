import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalTwoOriginMixedCenterDifferenceV5_PZ37AOY
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AOZ — original Wilson double-center kernel relative Taylor error

The pointwise original action identity AOY is connected to AOH's local
exponential remainder estimate. All kernels and center twists are those
of the original finite-volume SU(2) model, for every finite H including
zero. With 16 * beta <= 1 the kernel mixed difference has a relative
error bounded by 384 * beta^2 times the original unflipped kernel.
The eventual Haar integral and normalized row response remain separate.
-/

namespace MGAP4D.MathlibAnalytic

open scoped ENNReal Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 12000000

local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration
local notation "S" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction
local notation "K" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
local notation "T" => p4Q2PZ37ANV_singleLinkCenterTwist
local notation "E" => p4Q2PZ37AMS_primarySpatialSliceEdge
local notation "Chi" => p4Q2PZ35C_originalOneLinkCharacter
local notation "Hol" => p4Q2PZ37AMS_primarySpatialSliceCyclicHolonomy

/-- The existing local remainder at eight, rescaled to sixteen,
retains the same exponential argument. -/
theorem p4Q2PZ37AOZ_real_exp_relativeLinearRemainder_abs_le_sixteen
    (beta delta : ℝ) (hbeta : 0 ≤ beta)
    (hsmall : 16 * beta ≤ 1) (hdelta : |delta| ≤ 16) :
    |Real.exp (-beta * delta) - 1 + beta * delta| ≤ 256 * beta^2 := by
  have hd : |delta / 2| ≤ 8 := by
    rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith only [hdelta]
  have h := p4Q2PZ37AOH_real_exp_relativeLinearRemainder_abs_le
    (2 * beta) (delta / 2) (by positivity) (by linarith only [hsmall]) hd
  have harg : -(2 * beta) * (delta / 2) = -beta * delta := by ring
  have hlin : (2 * beta) * (delta / 2) = beta * delta := by ring
  have hsq : 64 * (2 * beta)^2 = 256 * beta^2 := by ring
  rw [harg, hlin, hsq] at h
  exact h

private theorem p4Q2PZ37AOZ_kernel_factor
    (H : ℕ) (beta : ℝ) (A B C : Cfg H 2) :
    K H 2 beta A C = K H 2 beta A B *
      Real.exp (-beta * (S H 2 A C - S H 2 A B)) := by
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann,
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann,
    ← Real.exp_add]
  congr 1
  ring

private theorem p4Q2PZ37AOZ_pair_relativeRemainder_abs_le
    (H : ℕ) (beta bound : ℝ) (A B C : Cfg H 2)
    (hscalar : |Real.exp (-beta * (S H 2 A C - S H 2 A B)) - 1 +
      beta * (S H 2 A C - S H 2 A B)| ≤ bound) :
    |K H 2 beta A C - K H 2 beta A B +
      beta * (S H 2 A C - S H 2 A B) * K H 2 beta A B| ≤
      bound * K H 2 beta A B := by
  let k := K H 2 beta A B
  let delta := S H 2 A C - S H 2 A B
  have hk : 0 ≤ k := by
    dsimp [k]
    rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann]
    exact Real.exp_nonneg _
  have hfactor : K H 2 beta A C = k * Real.exp (-beta * delta) :=
    p4Q2PZ37AOZ_kernel_factor H beta A B C
  change |K H 2 beta A C - k + beta * delta * k| ≤ bound * k
  rw [hfactor]
  have heq : k * Real.exp (-beta * delta) - k + beta * delta * k =
      k * (Real.exp (-beta * delta) - 1 + beta * delta) := by ring
  rw [heq, abs_mul, abs_of_nonneg hk]
  exact (mul_le_mul_of_nonneg_left hscalar hk).trans_eq (mul_comm k bound)

private theorem p4Q2PZ37AOZ_singleTwist_relativeRemainder_abs_le
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (hsmall : 16 * beta ≤ 1)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (A B : Cfg H 2) :
    |K H 2 beta A (T H target B) - K H 2 beta A B +
      beta * (S H 2 A (T H target B) - S H 2 A B) * K H 2 beta A B| ≤
      64 * beta^2 * K H 2 beta A B := by
  apply p4Q2PZ37AOZ_pair_relativeRemainder_abs_le
  apply p4Q2PZ37AOH_real_exp_relativeLinearRemainder_abs_le beta _ hbeta
    (by linarith only [hbeta, hsmall])
  exact p4Q2PZ37AOC_originalSlabAction_rightCenterTwist_sub_abs_le_eight H target A B

/-- The two successive genuine center flips alter the original action
by at most sixteen. No total-action budget enters. -/
theorem p4Q2PZ37AOZ_twoOriginActionDifference_abs_le_sixteen
    (H : ℕ) (A B : Cfg H 2) :
    |S H 2 A (T H (E H 3) (T H (E H 0) B)) - S H 2 A B| ≤ 16 := by
  let B0 := T H (E H 0) B
  let B03 := T H (E H 3) B0
  have h0 : |S H 2 A B0 - S H 2 A B| ≤ 8 :=
    p4Q2PZ37AOC_originalSlabAction_rightCenterTwist_sub_abs_le_eight H (E H 0) A B
  have h3 : |S H 2 A B03 - S H 2 A B0| ≤ 8 :=
    p4Q2PZ37AOC_originalSlabAction_rightCenterTwist_sub_abs_le_eight H (E H 3) A B0
  change |S H 2 A B03 - S H 2 A B| ≤ 16
  calc
    _ = |(S H 2 A B03 - S H 2 A B0) + (S H 2 A B0 - S H 2 A B)| := by
      congr 1
      ring
    _ ≤ |S H 2 A B03 - S H 2 A B0| + |S H 2 A B0 - S H 2 A B| :=
      abs_add_le _ _
    _ ≤ 16 := by linarith only [h0, h3]

/-- Pointwise double-center Wilson kernel difference:
the original primary character is the exact first-order coefficient,
and the error is bounded relative to the original kernel, uniformly in H. -/
theorem p4Q2PZ37AOZ_originalKernel_twoOriginMixedRelativeTaylor_abs_le
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (hsmall : 16 * beta ≤ 1)
    (A B : Cfg H 2) :
    |K H 2 beta A B - K H 2 beta A (T H (E H 0) B) -
      K H 2 beta A (T H (E H 3) B) +
      K H 2 beta A (T H (E H 3) (T H (E H 0) B)) -
      2 * beta * Chi (Hol H 2 B) * K H 2 beta A B| ≤
      384 * beta^2 * K H 2 beta A B := by
  let B0 := T H (E H 0) B
  let B3 := T H (E H 3) B
  let B03 := T H (E H 3) B0
  let k := K H 2 beta A B
  let k0 := K H 2 beta A B0
  let k3 := K H 2 beta A B3
  let k03 := K H 2 beta A B03
  let chi := Chi (Hol H 2 B)
  let d0 := S H 2 A B0 - S H 2 A B
  let d3 := S H 2 A B3 - S H 2 A B
  let d03 := S H 2 A B03 - S H 2 A B
  let r0 := k0 - k + beta * d0 * k
  let r3 := k3 - k + beta * d3 * k
  let r03 := k03 - k + beta * d03 * k
  have hr0 : |r0| ≤ 64 * beta^2 * k :=
    p4Q2PZ37AOZ_singleTwist_relativeRemainder_abs_le H beta hbeta hsmall (E H 0) A B
  have hr3 : |r3| ≤ 64 * beta^2 * k :=
    p4Q2PZ37AOZ_singleTwist_relativeRemainder_abs_le H beta hbeta hsmall (E H 3) A B
  have hd03 : |d03| ≤ 16 := p4Q2PZ37AOZ_twoOriginActionDifference_abs_le_sixteen H A B
  have hscalar := p4Q2PZ37AOZ_real_exp_relativeLinearRemainder_abs_le_sixteen beta d03 hbeta hsmall hd03
  have hr03 : |r03| ≤ 256 * beta^2 * k :=
    p4Q2PZ37AOZ_pair_relativeRemainder_abs_le H beta (256 * beta^2) A B B03 hscalar
  have hGap : d0 + d3 - d03 = 2 * chi := by
    have h := p4Q2PZ37AOY_originalOneSlabAction_twoOriginMixedDifference H A B
    change S H 2 A B - S H 2 A B0 - S H 2 A B3 + S H 2 A B03 = -2 * chi at h
    dsimp only [d0, d3, d03]
    linarith only [h]
  have hLinear : beta * (d0 + d3 - d03) * k = 2 * beta * chi * k := by
    rw [hGap]
    ring
  have hEq : k - k0 - k3 + k03 - 2 * beta * chi * k = -r0 - r3 + r03 := by
    rw [← hLinear]
    dsimp only [r0, r3, r03]
    ring
  have hNeg : |-r0 - r3| ≤ |r0| + |r3| := by
    simpa only [sub_eq_add_neg, abs_neg] using (abs_add_le (-r0) (-r3))
  change |k - k0 - k3 + k03 - 2 * beta * chi * k| ≤ 384 * beta^2 * k
  calc
    _ = |-r0 - r3 + r03| := by rw [hEq]
    _ ≤ |-r0 - r3| + |r03| := abs_add_le _ _
    _ ≤ (|r0| + |r3|) + |r03| := add_le_add hNeg (le_refl |r03|)
    _ ≤ (64 * beta^2 * k + 64 * beta^2 * k) + 256 * beta^2 * k :=
      add_le_add (add_le_add hr0 hr3) hr03
    _ = 384 * beta^2 * k := by ring

end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOZ_real_exp_relativeLinearRemainder_abs_le_sixteen
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOZ_twoOriginActionDifference_abs_le_sixteen
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AOZ_originalKernel_twoOriginMixedRelativeTaylor_abs_le
