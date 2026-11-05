import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalSignedSpatialIntervalCertificateV5_PZ37AGI
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AGJ — rational Taylor evaluation of the original Wilson kernel

AGI's rational table evaluator still needs evidence about original values.
AGJ removes a transcendental kernel-value oracle: a certified interval for
the ORIGINAL one-slab action, a certified coupling interval, and purely
rational scale checks produce an AFV interval for the ORIGINAL kernel.

For rational q with |q|<=1 and n>0, the pinned mathlib exp_bound proves
  |exp(q)-P_n(q)| <= R_n(q),
  P_n(q)=sum_{j<n} q^j/j!, R_n(q)=|q|^n*(n+1)/(n!*n).
For a positive integer k, exp(x)=exp(x/k)^k. The lower Taylor endpoint
is clipped at ZERO BEFORE taking its kth power. Omitting this clipping
would be unsound for a negative lower endpoint and an even k.

Exact rational regression inequalities exp(2/5)<3/2<exp(13/32), combined
with the existing exp(64*beta0)=3/2, prove unconditionally
  1/160 < beta0 < 13/2048.
This is a proved enclosure, not a floating-point assumption.

The rational evaluator uses no classical choice of an unknown exponential.
Actual action intervals must still be justified against the same Wilson
sum. Haar mass intervals and the centered source mean are separate inputs
not evaluated here. No realized nonzero signed transfer, two-threshold
shell, volume-uniform coercivity, Hamiltonian or continuum gap is claimed.
-/

namespace MGAP4D.MathlibAnalytic

open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Finite exact rational Taylor polynomial. -/
def p4Q2PZ37AGJ_taylorSum (q : ℚ) (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range n, q ^ j / (j.factorial : ℚ)

/-- Explicit rational remainder, interpreted only with n>0. -/
def p4Q2PZ37AGJ_taylorError (q : ℚ) (n : ℕ) : ℚ :=
  |q| ^ n * ((n + 1 : ℕ) : ℚ) / ((n.factorial : ℚ) * (n : ℚ))

/-- Clipping prevents the even-power negative-endpoint failure. -/
def p4Q2PZ37AGJ_expLower (q : ℚ) (k n : ℕ) : ℚ :=
  (max 0 (p4Q2PZ37AGJ_taylorSum (q / k) n -
    p4Q2PZ37AGJ_taylorError (q / k) n)) ^ k

def p4Q2PZ37AGJ_expUpper (q : ℚ) (k n : ℕ) : ℚ :=
  (max 0 (p4Q2PZ37AGJ_taylorSum (q / k) n +
    p4Q2PZ37AGJ_taylorError (q / k) n)) ^ k

/-- Arithmetic tests against the exact rational 3/2. -/
theorem p4Q2PZ37AGJ_couplingArithmetic_checked :
    p4Q2PZ37AGJ_taylorSum (2 / 5) 5 +
      p4Q2PZ37AGJ_taylorError (2 / 5) 5 < 3 / 2 ∧
    3 / 2 < p4Q2PZ37AGJ_taylorSum (13 / 32) 5 -
      p4Q2PZ37AGJ_taylorError (13 / 32) 5 := by
  norm_num [p4Q2PZ37AGJ_taylorSum, p4Q2PZ37AGJ_taylorError,
    Finset.sum_range_succ, Nat.factorial]

/-- Synthetic regression: un-clipped (-1)^2 would give a false lower 1. -/
theorem p4Q2PZ37AGJ_negativeClipping_checked :
    p4Q2PZ37AGJ_expLower (-2) 2 1 = 0 ∧
      p4Q2PZ37AGJ_expUpper (-2) 2 1 = 9 := by
  norm_num [p4Q2PZ37AGJ_expLower, p4Q2PZ37AGJ_expUpper,
    p4Q2PZ37AGJ_taylorSum, p4Q2PZ37AGJ_taylorError,
    Finset.sum_range_succ, Nat.factorial]

theorem p4Q2PZ37AGJ_zeroExponent_checked :
    p4Q2PZ37AGJ_expLower 0 3 5 = 1 ∧
      p4Q2PZ37AGJ_expUpper 0 3 5 = 1 := by
  norm_num [p4Q2PZ37AGJ_expLower, p4Q2PZ37AGJ_expUpper,
    p4Q2PZ37AGJ_taylorSum, p4Q2PZ37AGJ_taylorError,
    Finset.sum_range_succ, Nat.factorial]

noncomputable section

/-- Directly reuse the pinned mathlib remainder theorem. -/
theorem p4Q2PZ37AGJ_taylor_accuracy
    (q : ℚ) (n : ℕ) (hq : |q| ≤ 1) (hn : 0 < n) :
    |Real.exp (q : ℝ) - (p4Q2PZ37AGJ_taylorSum q n : ℝ)| ≤
      (p4Q2PZ37AGJ_taylorError q n : ℝ) := by
  have hqR : |(q : ℝ)| ≤ 1 := by exact_mod_cast hq
  have h := Real.exp_bound (n := n) hqR hn
  simpa [p4Q2PZ37AGJ_taylorSum, p4Q2PZ37AGJ_taylorError,
    mul_div_assoc] using h

/-- A small rational exponent yields an actual AFV exponential interval. -/
def p4Q2PZ37AGJ_smallExpInterval
    (q : ℚ) (n : ℕ) (hq : |q| ≤ 1) (hn : 0 < n) :
    p4Q2PZ37AFV_verifiedInterval (Real.exp (q : ℝ)) where
  lower := p4Q2PZ37AGJ_taylorSum q n - p4Q2PZ37AGJ_taylorError q n
  upper := p4Q2PZ37AGJ_taylorSum q n + p4Q2PZ37AGJ_taylorError q n
  hLower := by
    have h := (abs_le.mp (p4Q2PZ37AGJ_taylor_accuracy q n hq hn)).1
    push_cast
    linarith only [h]
  hUpper := by
    have h := (abs_le.mp (p4Q2PZ37AGJ_taylor_accuracy q n hq hn)).2
    push_cast
    linarith only [h]

/-- Exact rescaling, with the zero-divisor case explicitly excluded. -/
theorem p4Q2PZ37AGJ_exp_scale_identity
    (q : ℚ) (k : ℕ) (hk : 0 < k) :
    Real.exp ((q / (k : ℚ) : ℚ) : ℝ) ^ k = Real.exp (q : ℝ) := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  rw [← Real.exp_nat_mul]
  congr 1
  push_cast
  field_simp

/-- Arbitrary magnitude is handled by a finite positive integer scale.
All endpoint arithmetic is rational; the input interval is for x, not exp x. -/
def p4Q2PZ37AGJ_scaledExpInterval {x : ℝ}
    (lo hi : ℚ) (k n : ℕ) (hk : 0 < k) (hn : 0 < n)
    (hloSmall : |lo / (k : ℚ)| ≤ 1) (hhiSmall : |hi / (k : ℚ)| ≤ 1)
    (hlo : (lo : ℝ) ≤ x) (hhi : x ≤ (hi : ℝ)) :
    p4Q2PZ37AFV_verifiedInterval (Real.exp x) where
  lower := p4Q2PZ37AGJ_expLower lo k n
  upper := p4Q2PZ37AGJ_expUpper hi k n
  hLower := by
    let c := p4Q2PZ37AGJ_smallExpInterval (lo / k) n hloSmall hn
    have hm : max (0 : ℝ) (c.lower : ℝ) ≤ Real.exp ((lo / (k : ℚ) : ℚ) : ℝ) :=
      max_le (Real.exp_pos _).le c.hLower
    calc
      (p4Q2PZ37AGJ_expLower lo k n : ℝ) =
        (max (0 : ℝ) (c.lower : ℝ)) ^ k := by
          simp [p4Q2PZ37AGJ_expLower, c, p4Q2PZ37AGJ_smallExpInterval]
      _ ≤ Real.exp ((lo / (k : ℚ) : ℚ) : ℝ) ^ k :=
        pow_le_pow_left₀ (le_max_left _ _) hm k
      _ = Real.exp (lo : ℝ) := p4Q2PZ37AGJ_exp_scale_identity lo k hk
      _ ≤ Real.exp x := Real.exp_le_exp.mpr hlo
  hUpper := by
    let c := p4Q2PZ37AGJ_smallExpInterval (hi / k) n hhiSmall hn
    have hm : Real.exp ((hi / (k : ℚ) : ℚ) : ℝ) ≤ max (0 : ℝ) (c.upper : ℝ) :=
      c.hUpper.trans (le_max_right _ _)
    calc
      Real.exp x ≤ Real.exp (hi : ℝ) := Real.exp_le_exp.mpr hhi
      _ = Real.exp ((hi / (k : ℚ) : ℚ) : ℝ) ^ k :=
        (p4Q2PZ37AGJ_exp_scale_identity hi k hk).symm
      _ ≤ (max (0 : ℝ) (c.upper : ℝ)) ^ k :=
        pow_le_pow_left₀ (Real.exp_pos _).le hm k
      _ = (p4Q2PZ37AGJ_expUpper hi k n : ℝ) := by
        simp [p4Q2PZ37AGJ_expUpper, c, p4Q2PZ37AGJ_smallExpInterval]

/-- A nonnegative coupling/action interval produces a Boltzmann interval;
no approximation to the unknown exponential itself is assumed. -/
def p4Q2PZ37AGJ_boltzmannInterval {beta action : ℝ}
    (b : p4Q2PZ37AFV_verifiedInterval beta)
    (s : p4Q2PZ37AFV_verifiedInterval action)
    (hb : 0 ≤ b.lower) (hs : 0 ≤ s.lower)
    (k n : ℕ) (hk : 0 < k) (hn : 0 < n)
    (hloSmall : |-(b.upper * s.upper) / (k : ℚ)| ≤ 1)
    (hhiSmall : |-(b.lower * s.lower) / (k : ℚ)| ≤ 1) :
    p4Q2PZ37AFV_verifiedInterval (Real.exp (-beta * action)) := by
  have hbR : (0 : ℝ) ≤ (b.lower : ℝ) := by exact_mod_cast hb
  have hsR : (0 : ℝ) ≤ (s.lower : ℝ) := by exact_mod_cast hs
  have hBeta : 0 ≤ beta := hbR.trans b.hLower
  have hAction : 0 ≤ action := hsR.trans s.hLower
  have hLow := mul_le_mul b.hLower s.hLower hsR hBeta
  have hHigh := mul_le_mul b.hUpper s.hUpper hAction (hBeta.trans b.hUpper)
  apply p4Q2PZ37AGJ_scaledExpInterval
    (-(b.upper * s.upper)) (-(b.lower * s.lower)) k n hk hn hloSmall hhiSmall
  · push_cast
    linarith only [hHigh]
  · push_cast
    linarith only [hLow]

namespace GroundStatePosteriorJoint

/-- Unconditional, explicitly rational enclosure of the ORIGINAL beta0. -/
theorem p4Q2PZ37AGJ_fixedCoupling_bounds :
    (1 / 160 : ℝ) < p4Q2PZ37ADC_fixedCoupling ∧
      p4Q2PZ37ADC_fixedCoupling < (13 / 2048 : ℝ) := by
  have hL := p4Q2PZ37AGJ_smallExpInterval (2 / 5) 5 (by norm_num) (by norm_num)
  have hU := p4Q2PZ37AGJ_smallExpInterval (13 / 32) 5 (by norm_num) (by norm_num)
  have hExpL : Real.exp (2 / 5 : ℝ) < 3 / 2 := by
    calc
      Real.exp (2 / 5 : ℝ) ≤
        ((p4Q2PZ37AGJ_taylorSum (2 / 5) 5 + p4Q2PZ37AGJ_taylorError (2 / 5) 5 : ℚ) : ℝ) := by
          simpa [hL, p4Q2PZ37AGJ_smallExpInterval] using hL.hUpper
      _ < 3 / 2 := by exact_mod_cast p4Q2PZ37AGJ_couplingArithmetic_checked.1
  have hExpU : (3 / 2 : ℝ) < Real.exp (13 / 32 : ℝ) := by
    calc
      (3 / 2 : ℝ) <
        ((p4Q2PZ37AGJ_taylorSum (13 / 32) 5 - p4Q2PZ37AGJ_taylorError (13 / 32) 5 : ℚ) : ℝ) := by
          exact_mod_cast p4Q2PZ37AGJ_couplingArithmetic_checked.2
      _ ≤ Real.exp (13 / 32 : ℝ) := by
        simpa [hU, p4Q2PZ37AGJ_smallExpInterval] using hU.hLower
  have hLo : (2 / 5 : ℝ) < 64 * p4Q2PZ37ADC_fixedCoupling := by
    apply Real.exp_lt_exp.mp
    rw [p4Q2PZ37ADC_fixedCoupling_exp_eq]
    exact hExpL
  have hHi : 64 * p4Q2PZ37ADC_fixedCoupling < (13 / 32 : ℝ) := by
    apply Real.exp_lt_exp.mp
    rw [p4Q2PZ37ADC_fixedCoupling_exp_eq]
    exact hExpU
  constructor <;> linarith only [hLo, hHi]

def p4Q2PZ37AGJ_fixedCouplingInterval :
    p4Q2PZ37AFV_verifiedInterval p4Q2PZ37ADC_fixedCoupling where
  lower := 1 / 160
  upper := 13 / 2048
  hLower := by exact_mod_cast p4Q2PZ37AGJ_fixedCoupling_bounds.1.le
  hUpper := by exact_mod_cast p4Q2PZ37AGJ_fixedCoupling_bounds.2.le

variable (H : ℕ)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "b0" => p4Q2PZ37ADC_fixedCoupling
local notation "S" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2
local notation "K" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 b0

/-- A certified ORIGINAL one-slab action interval now determines a kernel
interval by finite rational operations, without a kernel-value oracle. -/
def p4Q2PZ37AGJ_originalKernelInterval (A B : Cfg)
    (s : p4Q2PZ37AFV_verifiedInterval (S A B)) (hs : 0 ≤ s.lower)
    (k n : ℕ) (hk : 0 < k) (hn : 0 < n)
    (hloSmall : |-((13 / 2048 : ℚ) * s.upper) / (k : ℚ)| ≤ 1)
    (hhiSmall : |-((1 / 160 : ℚ) * s.lower) / (k : ℚ)| ≤ 1) :
    p4Q2PZ37AFV_verifiedInterval (K A B) := by
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann]
  exact p4Q2PZ37AGJ_boltzmannInterval p4Q2PZ37AGJ_fixedCouplingInterval s
    (by norm_num [p4Q2PZ37AGJ_fixedCouplingInterval]) hs k n hk hn hloSmall hhiSmall

/-- Preserve the established AGA rational-ball interface. -/
def p4Q2PZ37AGJ_originalKernelBall (A B : Cfg)
    (s : p4Q2PZ37AFV_verifiedInterval (S A B)) (hs : 0 ≤ s.lower)
    (k n : ℕ) (hk : 0 < k) (hn : 0 < n)
    (hloSmall : |-((13 / 2048 : ℚ) * s.upper) / (k : ℚ)| ≤ 1)
    (hhiSmall : |-((1 / 160 : ℚ) * s.lower) / (k : ℚ)| ≤ 1) :
    p4Q2PZ37AGA_rationalBall (K A B) :=
  p4Q2PZ37AGA_fromVerifiedInterval
    (p4Q2PZ37AGJ_originalKernelInterval H A B s hs k n hk hn hloSmall hhiSmall)

/-- Exact original zero-action check, conditional only on actual action. -/
theorem p4Q2PZ37AGJ_originalKernel_of_zeroAction
    (A B : Cfg) (hS : S A B = 0) : K A B = 1 := by
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann,
    hS, mul_zero, Real.exp_zero]

/-- Exact coupling calibration, not a claim that a chosen configuration
has action 64: that equality remains explicit input. -/
theorem p4Q2PZ37AGJ_originalKernel_of_action64
    (A B : Cfg) (hS : S A B = 64) : K A B = (2 / 3 : ℝ) := by
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann, hS]
  have he : -b0 * 64 = -(64 * b0) := by ring
  rw [he, Real.exp_neg, p4Q2PZ37ADC_fixedCoupling_exp_eq]
  norm_num

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGJ_couplingArithmetic_checked
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGJ_negativeClipping_checked
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGJ_zeroExponent_checked
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGJ_taylor_accuracy
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGJ_smallExpInterval
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGJ_exp_scale_identity
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGJ_scaledExpInterval
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGJ_boltzmannInterval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGJ_fixedCoupling_bounds
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGJ_fixedCouplingInterval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGJ_originalKernelInterval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGJ_originalKernelBall
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGJ_originalKernel_of_zeroAction
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGJ_originalKernel_of_action64
