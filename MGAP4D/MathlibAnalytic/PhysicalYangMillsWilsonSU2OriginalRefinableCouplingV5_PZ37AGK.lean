import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalKernelTaylorIntervalV5_PZ37AGJ
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AGK — refinable rational intervals for the ORIGINAL fixed coupling

AGJ's Taylor approximation does not remove the fixed width of its coupling
bracket. AGK preserves the actual beta0 and refines its enclosure itself.
At x=1/5, (1+x)/(1-x)=3/2. The pinned real logarithm remainder proves

  a_n <= beta0 <= a_n + e_n,
  a_n = (sum_{j<n} (1/5)^(2*j+1)/(2*j+1))/32,
  e_n = (5/768)*(1/25)^n.

The computable rational endpoints are intersected with AGJ's original
[1/160,13/2048], so the established enclosure is never weakened. Their
width is bounded by e_n and tends to zero. For any requested positive
precision some finite n suffices; a supplied n is checked by exact rational
arithmetic, without evaluating an unknown logarithm or choosing a rational
approximation to it as an oracle.

These refined intervals feed AGJ's rational Taylor Boltzmann construction
for the same actual Wilson one-slab kernel. Coupling precision and Taylor
order are independent. Actual action intervals, spatial Haar cell masses
and centered source means remain separate physical evaluation obligations.
No actual transfer sign, shell, volume-uniform coercivity, Hamiltonian or
continuum Yang--Mills mass gap is asserted.
-/

namespace MGAP4D.MathlibAnalytic

open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Positive finite logarithm series, scaled to the original beta0. -/
def p4Q2PZ37AGK_rawLower (n : ℕ) : ℚ :=
  (∑ j ∈ Finset.range n, (1 / 5 : ℚ) ^ (2 * j + 1) /
    ((2 * j + 1 : ℕ) : ℚ)) / 32

/-- Exact rational error rate, including n=0. -/
def p4Q2PZ37AGK_tail (n : ℕ) : ℚ := (5 / 768 : ℚ) * (1 / 25 : ℚ) ^ n

def p4Q2PZ37AGK_rawUpper (n : ℕ) : ℚ :=
  p4Q2PZ37AGK_rawLower n + p4Q2PZ37AGK_tail n

/-- Retain the already established AGJ lower bound. -/
def p4Q2PZ37AGK_lower (n : ℕ) : ℚ := max (1 / 160) (p4Q2PZ37AGK_rawLower n)

/-- Retain the already established AGJ upper bound. -/
def p4Q2PZ37AGK_upper (n : ℕ) : ℚ := min (13 / 2048) (p4Q2PZ37AGK_rawUpper n)

theorem p4Q2PZ37AGK_tail_identity (n : ℕ) :
    ((1 / 5 : ℚ) ^ (2 * n + 1) / (1 - (1 / 5 : ℚ) ^ 2)) / 32 =
      p4Q2PZ37AGK_tail n := by
  simp only [pow_add, pow_mul, pow_one]
  norm_num [p4Q2PZ37AGK_tail] <;> ring

theorem p4Q2PZ37AGK_tail_nonneg (n : ℕ) : 0 ≤ p4Q2PZ37AGK_tail n := by
  unfold p4Q2PZ37AGK_tail
  positivity

/-- Regression: the coarse n=0 series does not lose the prior bracket. -/
theorem p4Q2PZ37AGK_zeroOrder_checked :
    p4Q2PZ37AGK_lower 0 = 1 / 160 ∧ p4Q2PZ37AGK_upper 0 = 13 / 2048 := by
  norm_num [p4Q2PZ37AGK_lower, p4Q2PZ37AGK_upper,
    p4Q2PZ37AGK_rawUpper, p4Q2PZ37AGK_rawLower, p4Q2PZ37AGK_tail]

/-- Genuine computable coupling bounds, not an assumed floating value. -/
theorem p4Q2PZ37AGK_fourTerms_checked :
    p4Q2PZ37AGK_lower 4 = 10394 / 1640625 ∧
    p4Q2PZ37AGK_upper 4 = 886957 / 140000000 ∧
    p4Q2PZ37AGK_upper 4 - p4Q2PZ37AGK_lower 4 = 1 / 60000000 := by
  norm_num [p4Q2PZ37AGK_lower, p4Q2PZ37AGK_upper,
    p4Q2PZ37AGK_rawUpper, p4Q2PZ37AGK_rawLower, p4Q2PZ37AGK_tail,
    Finset.sum_range_succ]

theorem p4Q2PZ37AGK_eightTermsError_checked :
    p4Q2PZ37AGK_tail 8 = 1 / 23437500000000 := by
  norm_num [p4Q2PZ37AGK_tail]

theorem p4Q2PZ37AGK_lower_nonneg (n : ℕ) : 0 ≤ p4Q2PZ37AGK_lower n :=
  (by norm_num : (0 : ℚ) ≤ 1 / 160).trans (le_max_left _ _)

noncomputable section
open Filter
open scoped Topology

namespace GroundStatePosteriorJoint

local notation "b0" => p4Q2PZ37ADC_fixedCoupling

/-- Derive the logarithm identity from the existing ORIGINAL coupling
exponential calibration, rather than redefining the coupling. -/
theorem p4Q2PZ37AGK_originalLog_identity : Real.log (3 / 2 : ℝ) = 64 * b0 := by
  have h := congrArg Real.log p4Q2PZ37ADC_fixedCoupling_exp_eq
  rw [Real.log_exp] at h
  exact h.symm

/-- Positive partial sums and the pinned logarithm remainder bracket
actual beta0 for EVERY n, including the empty partial sum. -/
theorem p4Q2PZ37AGK_originalCoupling_rawBounds (n : ℕ) :
    (p4Q2PZ37AGK_rawLower n : ℝ) ≤ b0 ∧
      b0 ≤ (p4Q2PZ37AGK_rawUpper n : ℝ) := by
  have hL := Real.sum_range_le_log_div (x := (1 / 5 : ℝ))
    (by norm_num) (by norm_num) n
  have hU := Real.log_div_le_sum_range_add (x := (1 / 5 : ℝ))
    (by norm_num) (by norm_num) n
  have hRatio : (1 + (1 / 5 : ℝ)) / (1 - (1 / 5 : ℝ)) = 3 / 2 := by norm_num
  rw [hRatio, p4Q2PZ37AGK_originalLog_identity] at hL hU
  have hCast : (p4Q2PZ37AGK_rawLower n : ℝ) =
      (∑ j ∈ Finset.range n, (1 / 5 : ℝ) ^ (2 * j + 1) /
        (2 * (j : ℝ) + 1)) / 32 := by
    simp [p4Q2PZ37AGK_rawLower]
  have hTail : ((1 / 5 : ℝ) ^ (2 * n + 1) / (1 - (1 / 5 : ℝ) ^ 2)) / 32 =
      (p4Q2PZ37AGK_tail n : ℝ) := by
    exact_mod_cast p4Q2PZ37AGK_tail_identity n
  constructor
  · rw [hCast]
    linarith only [hL]
  · simp only [p4Q2PZ37AGK_rawUpper, Rat.cast_add]
    rw [hCast, ← hTail]
    linarith only [hU]

/-- Intersecting two proved enclosures is unconditional and tighten-only. -/
theorem p4Q2PZ37AGK_originalCoupling_bounds (n : ℕ) :
    (p4Q2PZ37AGK_lower n : ℝ) ≤ b0 ∧ b0 ≤ (p4Q2PZ37AGK_upper n : ℝ) := by
  have h := p4Q2PZ37AGK_originalCoupling_rawBounds n
  constructor
  · have hl := max_le p4Q2PZ37AGJ_fixedCoupling_bounds.1.le h.1
    simpa [p4Q2PZ37AGK_lower] using hl
  · have hu := le_min p4Q2PZ37AGJ_fixedCoupling_bounds.2.le h.2
    simpa [p4Q2PZ37AGK_upper] using hu

def p4Q2PZ37AGK_originalCouplingInterval (n : ℕ) :
    p4Q2PZ37AFV_verifiedInterval b0 where
  lower := p4Q2PZ37AGK_lower n
  upper := p4Q2PZ37AGK_upper n
  hLower := (p4Q2PZ37AGK_originalCoupling_bounds n).1
  hUpper := (p4Q2PZ37AGK_originalCoupling_bounds n).2

/-- The rational width has an explicit geometric majorant; no oracle or
cancellation of independently bounded uncertainties is used. -/
theorem p4Q2PZ37AGK_originalCoupling_width (n : ℕ) :
    0 ≤ p4Q2PZ37AGK_upper n - p4Q2PZ37AGK_lower n ∧
    p4Q2PZ37AGK_upper n - p4Q2PZ37AGK_lower n ≤ p4Q2PZ37AGK_tail n := by
  have h := p4Q2PZ37AGK_originalCoupling_bounds n
  have hOrder : p4Q2PZ37AGK_lower n ≤ p4Q2PZ37AGK_upper n := by
    exact_mod_cast h.1.trans h.2
  have hLower : p4Q2PZ37AGK_rawLower n ≤ p4Q2PZ37AGK_lower n := le_max_right _ _
  have hUpper : p4Q2PZ37AGK_upper n ≤
      p4Q2PZ37AGK_rawLower n + p4Q2PZ37AGK_tail n := min_le_right _ _
  exact ⟨sub_nonneg.mpr hOrder, by linarith only [hLower, hUpper]⟩

/-- The quantitative error itself tends to zero in the original real field. -/
theorem p4Q2PZ37AGK_tail_tendsto_zero :
    Tendsto (fun n : ℕ => (p4Q2PZ37AGK_tail n : ℝ)) atTop (𝓝 0) := by
  have hp : Tendsto (fun n : ℕ => (1 / 25 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hm := hp.const_mul (5 / 768 : ℝ)
  simpa [p4Q2PZ37AGK_tail] using hm

/-- No fixed coupling precision floor remains. This is not a claim about
any remaining action-interval or Taylor truncation width. -/
theorem p4Q2PZ37AGK_originalCoupling_width_tendsto_zero :
    Tendsto (fun n : ℕ => ((p4Q2PZ37AGK_upper n -
      p4Q2PZ37AGK_lower n : ℚ) : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero
    (fun n => by exact_mod_cast (p4Q2PZ37AGK_originalCoupling_width n).1)
    (fun n => by exact_mod_cast (p4Q2PZ37AGK_originalCoupling_width n).2)
  exact p4Q2PZ37AGK_tail_tendsto_zero

/-- Every positive requested real precision is met at a finite order. -/
theorem p4Q2PZ37AGK_exists_originalCoupling_precision
    (eps : ℝ) (heps : 0 < eps) :
    ∃ n : ℕ, ((p4Q2PZ37AGK_upper n - p4Q2PZ37AGK_lower n : ℚ) : ℝ) < eps := by
  have h := (tendsto_order.mp p4Q2PZ37AGK_originalCoupling_width_tendsto_zero).2 eps heps
  exact h.exists

/-- A finite rational tail check is enough to certify the requested width. -/
theorem p4Q2PZ37AGK_precision_of_rational_check (n : ℕ) (eps : ℚ)
    (h : p4Q2PZ37AGK_tail n < eps) :
    p4Q2PZ37AGK_upper n - p4Q2PZ37AGK_lower n < eps :=
  (p4Q2PZ37AGK_originalCoupling_width n).2.trans_lt h

variable (H : ℕ)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "S" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction H 2
local notation "K" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel H 2 b0

/-- Feed arbitrary coupling precision and independent Taylor order into
AGJ's verified construction for the SAME actual original Wilson kernel. -/
def p4Q2PZ37AGK_originalRefinedKernelInterval (A B : Cfg)
    (s : p4Q2PZ37AFV_verifiedInterval (S A B)) (hs : 0 ≤ s.lower)
    (m k n : ℕ) (hk : 0 < k) (hn : 0 < n)
    (hloSmall : |-(p4Q2PZ37AGK_upper m * s.upper) / (k : ℚ)| ≤ 1)
    (hhiSmall : |-(p4Q2PZ37AGK_lower m * s.lower) / (k : ℚ)| ≤ 1) :
    p4Q2PZ37AFV_verifiedInterval (K A B) := by
  rw [periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_eq_boltzmann]
  exact p4Q2PZ37AGJ_boltzmannInterval
    (p4Q2PZ37AGK_originalCouplingInterval m) s
    (p4Q2PZ37AGK_lower_nonneg m) hs k n hk hn hloSmall hhiSmall

/-- Keep the established original-value rational-ball interface. -/
def p4Q2PZ37AGK_originalRefinedKernelBall (A B : Cfg)
    (s : p4Q2PZ37AFV_verifiedInterval (S A B)) (hs : 0 ≤ s.lower)
    (m k n : ℕ) (hk : 0 < k) (hn : 0 < n)
    (hloSmall : |-(p4Q2PZ37AGK_upper m * s.upper) / (k : ℚ)| ≤ 1)
    (hhiSmall : |-(p4Q2PZ37AGK_lower m * s.lower) / (k : ℚ)| ≤ 1) :
    p4Q2PZ37AGA_rationalBall (K A B) :=
  p4Q2PZ37AGA_fromVerifiedInterval
    (p4Q2PZ37AGK_originalRefinedKernelInterval H A B s hs m k n hk hn hloSmall hhiSmall)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGK_tail_identity
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGK_tail_nonneg
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGK_zeroOrder_checked
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGK_fourTerms_checked
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGK_eightTermsError_checked
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AGK_lower_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGK_originalLog_identity
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGK_originalCoupling_rawBounds
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGK_originalCoupling_bounds
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGK_originalCouplingInterval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGK_originalCoupling_width
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGK_tail_tendsto_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGK_originalCoupling_width_tendsto_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGK_exists_originalCoupling_precision
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGK_precision_of_rational_check
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGK_originalRefinedKernelInterval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AGK_originalRefinedKernelBall
