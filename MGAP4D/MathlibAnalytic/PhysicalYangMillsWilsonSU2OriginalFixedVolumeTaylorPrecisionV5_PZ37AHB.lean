import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalTaylorOutputWidthV5_PZ37AHA
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AHB — original finite-volume uniform rational output precision

AHA bounded the ACTUAL original clipped AGJ exponential output intervals by
B(S,m,n)=(b+S*AGK_tail(m)/k+4*E_n)^k-b^k. In AHB the underlying original
one-slab action S is uniformly bounded by the already proved genuine global
combinatorial Wilson action V_H, and the genuine AGM autoScale
k=ceil(max |lo| |hi|)+1 has a single bound ceil(V_H)+1, independent of
center, right boundary, coupling order or Taylor order.

For n>0, the literal factorial Taylor envelope E_n is bounded by 2/n.
Consequently every positive rational target permits one pair of orders
(m,n) with V_H*AGK_tail(m)+4*E_n smaller than that target.

For all 0<=S<=V_H the actual AGJ lower Taylor base b satisfies 0<=b<=1.
The pinned mathlib abs_pow_sub_pow_le gives a FIXED-volume Lipschitz
coefficient (ceil(V_H)+1)*2^(ceil(V_H)+1) for the actual powered width
when the common error is <=1. This proves a uniform-in-the-original-
configurations arbitrarily fine rational certificate without replacing
any original physical scalar, kernel, floor, grid or Haar probability.

The bound is for every FIXED H; no volume-uniform coefficient or positivity
of the original centered transfer or continuum mass gap is asserted.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open Filter
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- A literal formula for the same actual clipped AGJ small-exponential
lower base that occurs in AHA's original output-width certificate. -/
def p4Q2PZ37AHB_lowerBase (S : ℚ) (m n : ℕ) : ℚ :=
  let lo := p4Q2PZ37AGZ_exponentLower S m
  let hi := p4Q2PZ37AGZ_exponentUpper S m
  let k := p4Q2PZ37AGM_autoScale lo hi
  max 0 (p4Q2PZ37AGJ_taylorSum (lo / (k : ℚ)) n -
    p4Q2PZ37AGJ_taylorError (lo / (k : ℚ)) n)

/-- Both original width contributors remain separate:
geometric fixed-coupling uncertainty and the literal Taylor remainder. -/
def p4Q2PZ37AHB_totalBaseError (S : ℚ) (m n : ℕ) : ℚ :=
  let k := p4Q2PZ37AGZ_autoScale S m
  S * p4Q2PZ37AGK_tail m / (k : ℚ) +
    4 * p4Q2PZ37AHA_factorialEnvelope n

/-- Existing AHA budget is EXACTLY the power difference using the same
AGM scale, true clipped AGJ lower base and original Taylor errors. -/
theorem p4Q2PZ37AHB_budget_exact (S : ℚ) (m n : ℕ) :
    p4Q2PZ37AHA_couplingTaylorBudget S m n =
      (p4Q2PZ37AHB_lowerBase S m n +
        p4Q2PZ37AHB_totalBaseError S m n) ^
        p4Q2PZ37AGZ_autoScale S m -
      (p4Q2PZ37AHB_lowerBase S m n) ^
        p4Q2PZ37AGZ_autoScale S m := by
  dsimp [p4Q2PZ37AHA_couplingTaylorBudget, p4Q2PZ37AHB_lowerBase,
    p4Q2PZ37AHB_totalBaseError, p4Q2PZ37AGZ_autoScale]
  ring

/-- The existing AGJ factorial remainder is at most 2/n, with no
asymptotic or external estimate; n>=1 is essential. -/
theorem p4Q2PZ37AHB_factorialEnvelope_le_two_div
    (n : ℕ) (hn : 0 < n) :
    p4Q2PZ37AHA_factorialEnvelope n ≤ (2 : ℚ) / n := by
  have hnq : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hn
  have hn1 : (1 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  have hF : (n : ℚ) ≤ (n.factorial : ℚ) := by
    exact_mod_cast Nat.self_le_factorial n
  have hFpos : (0 : ℚ) < (n.factorial : ℚ) := by
    exact_mod_cast Nat.factorial_pos n
  have hNum : (((n + 1 : ℕ) : ℚ)) ≤ 2 * (n.factorial : ℚ) := by
    push_cast
    linarith only [hn1, hF]
  have hRat : (((n + 1 : ℕ) : ℚ)) / (n.factorial : ℚ) ≤ 2 :=
    (div_le_iff₀ hFpos).2 hNum
  calc
    p4Q2PZ37AHA_factorialEnvelope n =
        ((((n + 1 : ℕ) : ℚ)) / (n.factorial : ℚ)) / (n : ℚ) := by
          unfold p4Q2PZ37AHA_factorialEnvelope
          ring
    _ ≤ 2 / (n : ℚ) := div_le_div_of_nonneg_right hRat hnq.le

/-- For every rational threshold, a genuine positive Taylor order has
a smaller AGJ factorial envelope. This is a proved finite-order witness. -/
theorem p4Q2PZ37AHB_exists_factorial_precision
    (eps : ℚ) (heps : 0 < eps) :
    ∃ n : ℕ, 0 < n ∧ p4Q2PZ37AHA_factorialEnvelope n < eps := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((2 : ℚ) / eps)
  have hnPos : 0 < n := by
    by_contra h
    have hzero : n = 0 := Nat.eq_zero_of_not_pos h
    subst n
    have hd : (0 : ℚ) < 2 / eps := div_pos (by norm_num) heps
    exact lt_asymm hd hn
  have hnq : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hnPos
  have hnProduct : (2 : ℚ) < eps * (n : ℚ) := by
    have h := (div_lt_iff₀ heps).mp hn
    simpa [mul_comm] using h
  have hDiv : (2 : ℚ) / n < eps :=
    (div_lt_iff₀ hnq).2 (by simpa [mul_comm] using hnProduct)
  exact ⟨n, hnPos,
    (p4Q2PZ37AHB_factorialEnvelope_le_two_div n hnPos).trans_lt hDiv⟩

/-- AGK's already proved convergence supplies an exact finite rational
coupling order with the ORIGINAL geometric tail below any target. -/
theorem p4Q2PZ37AHB_exists_couplingTail_precision
    (eps : ℚ) (heps : 0 < eps) :
    ∃ m : ℕ, p4Q2PZ37AGK_tail m < eps := by
  have hReal : (0 : ℝ) < (eps : ℝ) := by exact_mod_cast heps
  have h := (tendsto_order.mp
    GroundStatePosteriorJoint.p4Q2PZ37AGK_tail_tendsto_zero).2 (eps : ℝ) hReal
  obtain ⟨m, hm⟩ := h.exists
  exact ⟨m, by exact_mod_cast hm⟩

namespace GroundStatePosteriorJoint

/-- One explicit uniform upper bound for the original AGK fixed-coupling
endpoints: the intersection with AGJ's proved upper bound never weakens. -/
theorem p4Q2PZ37AHB_couplingBracket_unit (m : ℕ) :
    0 ≤ p4Q2PZ37AGK_lower m ∧
      p4Q2PZ37AGK_lower m ≤ p4Q2PZ37AGK_upper m ∧
      p4Q2PZ37AGK_upper m ≤ (1 : ℚ) := by
  have hl := p4Q2PZ37AGK_lower_nonneg m
  have hw := (p4Q2PZ37AGK_originalCoupling_width m).1
  have hu : p4Q2PZ37AGK_upper m ≤ (1 : ℚ) := by
    calc
      p4Q2PZ37AGK_upper m ≤ (13 / 2048 : ℚ) := by
        unfold p4Q2PZ37AGK_upper
        exact min_le_left _ _
      _ ≤ 1 := by norm_num
  exact ⟨hl, sub_nonneg.mp hw, hu⟩

/-- All original AGM autoScales have ONE finite upper bound whenever
the genuine rational action is bounded by C. No evaluated grid needed. -/
theorem p4Q2PZ37AHB_autoScale_le
    (S C : ℚ) (hS : 0 ≤ S) (hSC : S ≤ C) (m : ℕ) :
    p4Q2PZ37AGZ_autoScale S m ≤ Nat.ceil C + 1 := by
  let lo := p4Q2PZ37AGZ_exponentLower S m
  let hi := p4Q2PZ37AGZ_exponentUpper S m
  obtain ⟨hbl, hblu, hbu⟩ := p4Q2PZ37AHB_couplingBracket_unit m
  have hbu0 : 0 ≤ p4Q2PZ37AGK_upper m := hbl.trans hblu
  have hbl1 : p4Q2PZ37AGK_lower m ≤ (1 : ℚ) := hblu.trans hbu
  have hLoAbs : |lo| ≤ C := by
    have hMul := mul_le_mul_of_nonneg_right hbu hS
    have hEq : |lo| = p4Q2PZ37AGK_upper m * S := by
      dsimp [lo, p4Q2PZ37AGZ_exponentLower]
      rw [abs_neg, abs_mul, abs_of_nonneg hbu0, abs_of_nonneg hS]
    rw [hEq]
    have hMul' : p4Q2PZ37AGK_upper m * S ≤ S := by simpa using hMul
    exact hMul'.trans hSC
  have hHiAbs : |hi| ≤ C := by
    have hMul := mul_le_mul_of_nonneg_right hbl1 hS
    have hEq : |hi| = p4Q2PZ37AGK_lower m * S := by
      dsimp [hi, p4Q2PZ37AGZ_exponentUpper]
      rw [abs_neg, abs_mul, abs_of_nonneg hbl, abs_of_nonneg hS]
    rw [hEq]
    have hMul' : p4Q2PZ37AGK_lower m * S ≤ S := by simpa using hMul
    exact hMul'.trans hSC
  have hCeil : Nat.ceil (max |lo| |hi|) ≤ Nat.ceil C := by
    apply (Nat.ceil_le).2
    exact (max_le hLoAbs hHiAbs).trans (Nat.le_ceil C)
  unfold p4Q2PZ37AGZ_autoScale p4Q2PZ37AGM_autoScale
  exact Nat.add_le_add_right hCeil 1

/-- The genuine clipped small Taylor base of the ORIGINAL kernel is in
[0,1], because its lower endpoint is below exp(u) with u<=0. -/
theorem p4Q2PZ37AHB_lowerBase_unit
    (S : ℚ) (hS : 0 ≤ S) (m n : ℕ) (hn : 0 < n) :
    0 ≤ p4Q2PZ37AHB_lowerBase S m n ∧
      p4Q2PZ37AHB_lowerBase S m n ≤ 1 := by
  let lo := p4Q2PZ37AGZ_exponentLower S m
  let hi := p4Q2PZ37AGZ_exponentUpper S m
  let k := p4Q2PZ37AGM_autoScale lo hi
  let u : ℚ := lo / (k : ℚ)
  have hbUpper : 0 ≤ p4Q2PZ37AGK_upper m :=
    (p4Q2PZ37AHB_couplingBracket_unit m).1.trans
      (p4Q2PZ37AHB_couplingBracket_unit m).2.1
  have hLo : lo ≤ 0 := by
    dsimp [lo, p4Q2PZ37AGZ_exponentLower]
    exact neg_nonpos.mpr (mul_nonneg hbUpper hS)
  have hk : (0 : ℚ) < k := by
    exact_mod_cast p4Q2PZ37AGM_autoScale_pos lo hi
  have hu : u ≤ 0 := div_nonpos_of_nonpos_of_nonneg hLo hk.le
  have hScale := (p4Q2PZ37AGM_scaledEndpoints lo hi).1
  let iv := p4Q2PZ37AGJ_smallExpInterval u n hScale hn
  have hLow : ((p4Q2PZ37AHB_lowerBase S m n : ℚ) : ℝ) ≤
      Real.exp (u : ℝ) := by
    have hMax : max (0 : ℝ) (iv.lower : ℝ) ≤ Real.exp (u : ℝ) :=
      max_le (Real.exp_pos _).le iv.hLower
    simpa [p4Q2PZ37AHB_lowerBase, iv,
      p4Q2PZ37AGJ_smallExpInterval, u, lo, hi, k] using hMax
  have hExp : Real.exp (u : ℝ) ≤ 1 := by
    calc
      Real.exp (u : ℝ) ≤ Real.exp (0 : ℝ) :=
        Real.exp_le_exp.mpr (by exact_mod_cast hu)
      _ = 1 := Real.exp_zero
  have hBound : p4Q2PZ37AHB_lowerBase S m n ≤ (1 : ℚ) := by
    exact_mod_cast hLow.trans hExp
  exact ⟨le_max_left _ _, hBound⟩

/-- The ORIGINAL AHA base error is nonnegative and is bounded by a
single configuration-independent rational geometric/factorial budget. -/
theorem p4Q2PZ37AHB_totalBaseError_le
    (S C : ℚ) (hS : 0 ≤ S) (hSC : S ≤ C)
    (m n : ℕ) (hn : 0 < n) :
    0 ≤ p4Q2PZ37AHB_totalBaseError S m n ∧
    p4Q2PZ37AHB_totalBaseError S m n ≤
      C * p4Q2PZ37AGK_tail m +
        4 * p4Q2PZ37AHA_factorialEnvelope n := by
  let k := p4Q2PZ37AGZ_autoScale S m
  have hk : (0 : ℚ) < k := by
    unfold k p4Q2PZ37AGZ_autoScale
    exact_mod_cast p4Q2PZ37AGM_autoScale_pos
      (p4Q2PZ37AGZ_exponentLower S m)
      (p4Q2PZ37AGZ_exponentUpper S m)
  have hk1 : (1 : ℚ) ≤ k := by exact_mod_cast
    (p4Q2PZ37AGM_autoScale_pos
      (p4Q2PZ37AGZ_exponentLower S m)
      (p4Q2PZ37AGZ_exponentUpper S m))
  have ht : 0 ≤ p4Q2PZ37AGK_tail m := p4Q2PZ37AGK_tail_nonneg m
  have he : 0 ≤ p4Q2PZ37AHA_factorialEnvelope n :=
    p4Q2PZ37AHA_factorialEnvelope_nonneg n hn
  have hnum : 0 ≤ S * p4Q2PZ37AGK_tail m := mul_nonneg hS ht
  have hdiv : S * p4Q2PZ37AGK_tail m / (k : ℚ) ≤
      S * p4Q2PZ37AGK_tail m := by
    apply (div_le_iff₀ hk).2
    have h := mul_le_mul_of_nonneg_left hk1 hnum
    nlinarith only [h]
  have hSCmul : S * p4Q2PZ37AGK_tail m ≤
      C * p4Q2PZ37AGK_tail m :=
    mul_le_mul_of_nonneg_right hSC ht
  constructor
  · unfold p4Q2PZ37AHB_totalBaseError
    exact add_nonneg (div_nonneg hnum hk.le)
      (mul_nonneg (by norm_num) he)
  · unfold p4Q2PZ37AHB_totalBaseError
    linarith only [hdiv, hSCmul]

/-- Genuine original slab action is <= the literal global action budget.
The exact rational AGL action and exact AGN budget are not approximated. -/
theorem p4Q2PZ37AHB_originalAction_le_globalBudget
    (H : ℕ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (a : ∀ e : PeriodicHypercubicEvenSpatialSliceLink H,
      p4Q2PZ37AGL_rationalCoordinates (A e))
    (b : ∀ e : PeriodicHypercubicEvenSpatialSliceLink H,
      p4Q2PZ37AGL_rationalCoordinates (B e)) :
    p4Q2PZ37AGL_slabActionRational H A B a b ≤
      p4Q2PZ37AGZ_originalFloorAction H := by
  have h := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabAction_le_globalBudget
    H 2 (by norm_num) A B
  rw [p4Q2PZ37AGL_originalSlabAction_exact H A B a b] at h
  have hBudget :
      (p4Q2PZ37AGZ_originalFloorAction H : ℝ) =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H := by
    simp [p4Q2PZ37AGZ_originalFloorAction,
      p4Q2PZ37AGN_actionBudgetInterval,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabCombinatorialVolume]
  rw [← hBudget] at h
  exact_mod_cast h

end GroundStatePosteriorJoint

/-- Fixed exponent power is quantitatively Lipschitz on the TRUE compact
interval 0<=b<=1, 0<=delta<=1, uniformly for k<=K. Uses the pinned
mathlib factorization estimate rather than assuming continuity of an
unknown physical kernel. -/
theorem p4Q2PZ37AHB_powerGap_le_linear
    (b delta : ℚ) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (hd : 0 ≤ delta) (hd1 : delta ≤ 1)
    (k K : ℕ) (hk : k ≤ K) :
    (b + delta) ^ k - b ^ k ≤
      delta * (K : ℚ) * (2 : ℚ) ^ K := by
  have hbAdd : 0 ≤ b + delta := add_nonneg hb hd
  have hB2 : b + delta ≤ (2 : ℚ) := by linarith only [hb1, hd1]
  have hMax : max |b + delta| |b| ≤ (2 : ℚ) := by
    rw [abs_of_nonneg hbAdd, abs_of_nonneg hb]
    exact max_le hB2 (hb1.trans (by norm_num))
  have hPower :
      (max |b + delta| |b|) ^ (k - 1) ≤ (2 : ℚ) ^ K := by
    calc
      (max |b + delta| |b|) ^ (k - 1) ≤ (2 : ℚ) ^ (k - 1) :=
        pow_le_pow_left₀ (le_max_of_le_left (abs_nonneg _)) hMax _
      _ ≤ (2 : ℚ) ^ K :=
        pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2)
          ((Nat.sub_le k 1).trans hk)
  have hAbs :
      |(b + delta) ^ k - b ^ k| ≤
        |(b + delta) - b| * (k : ℚ) *
          (max |b + delta| |b|) ^ (k - 1) :=
      abs_pow_sub_pow_le (b + delta) b k
  have hCast : (k : ℚ) ≤ (K : ℚ) := by exact_mod_cast hk
  have hPowNonneg : 0 ≤ (max |b + delta| |b|) ^ (k - 1) := by
    positivity
  have hMul1 : delta * (k : ℚ) * (max |b + delta| |b|) ^ (k - 1) ≤
      delta * (K : ℚ) * (max |b + delta| |b|) ^ (k - 1) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hCast hd) hPowNonneg
  have hMul2 : delta * (K : ℚ) * (max |b + delta| |b|) ^ (k - 1) ≤
      delta * (K : ℚ) * (2 : ℚ) ^ K :=
    mul_le_mul_of_nonneg_left hPower
      (mul_nonneg hd (Nat.cast_nonneg K))
  calc
    (b + delta) ^ k - b ^ k ≤ |(b + delta) ^ k - b ^ k| := le_abs_self _
    _ ≤ |(b + delta) - b| * (k : ℚ) * (max |b + delta| |b|) ^ (k - 1) :=
      hAbs
    _ = delta * (k : ℚ) * (max |b + delta| |b|) ^ (k - 1) := by
      rw [show (b + delta) - b = delta by ring, abs_of_nonneg hd]
    _ ≤ delta * (K : ℚ) * (max |b + delta| |b|) ^ (k - 1) := hMul1
    _ ≤ delta * (K : ℚ) * (2 : ℚ) ^ K := hMul2

namespace GroundStatePosteriorJoint

/-- For any uniform nonnegative upper bound C on ORIGINAL action S, one
finite integer K controls every AGM exponent scale, including both
positive Taylor order and coupling order. -/
def p4Q2PZ37AHB_globalScaleCap (C : ℚ) : ℕ := Nat.ceil C + 1

def p4Q2PZ37AHB_globalPrecisionError (C : ℚ) (m n : ℕ) : ℚ :=
  C * p4Q2PZ37AGK_tail m +
    4 * p4Q2PZ37AHA_factorialEnvelope n

/-- Explicit bounded-power control of actual AHA original output widths.
This is the quantitatively useful uniform compactness statement. -/
theorem p4Q2PZ37AHB_budget_le_globalPrecisionError
    (S C : ℚ) (hS : 0 ≤ S) (hSC : S ≤ C)
    (m n : ℕ) (hn : 0 < n)
    (hPrec : p4Q2PZ37AHB_globalPrecisionError C m n ≤ 1) :
    p4Q2PZ37AHA_couplingTaylorBudget S m n ≤
      p4Q2PZ37AHB_globalPrecisionError C m n *
        (p4Q2PZ37AHB_globalScaleCap C : ℚ) *
        (2 : ℚ) ^ p4Q2PZ37AHB_globalScaleCap C := by
  let b := p4Q2PZ37AHB_lowerBase S m n
  let d := p4Q2PZ37AHB_totalBaseError S m n
  let k := p4Q2PZ37AGZ_autoScale S m
  let K := p4Q2PZ37AHB_globalScaleCap C
  obtain ⟨hb, hb1⟩ := p4Q2PZ37AHB_lowerBase_unit S hS m n hn
  obtain ⟨hd, hdBound⟩ := p4Q2PZ37AHB_totalBaseError_le S C hS hSC m n hn
  have hd1 : d ≤ 1 := hdBound.trans hPrec
  have hk : k ≤ K := p4Q2PZ37AHB_autoScale_le S C hS hSC m
  have hPow := p4Q2PZ37AHB_powerGap_le_linear b d hb hb1 hd hd1 k K hk
  have hReplace :
      d * (K : ℚ) * (2 : ℚ) ^ K ≤
      p4Q2PZ37AHB_globalPrecisionError C m n *
        (K : ℚ) * (2 : ℚ) ^ K := by
    have h1 := mul_le_mul_of_nonneg_right hdBound
      (Nat.cast_nonneg K)
    have h2 := mul_le_mul_of_nonneg_right h1
      (pow_nonneg (by norm_num : (0 : ℚ) ≤ 2) K)
    exact h2
  rw [p4Q2PZ37AHB_budget_exact S m n]
  exact hPow.trans hReplace

/-- AGK geometric precision and the literal AGJ factorial precision can
be requested SIMULTANEOUSLY using one pair of finite rational orders. -/
theorem p4Q2PZ37AHB_exists_jointPrecision
    (C eps : ℚ) (hC : 0 ≤ C) (heps : 0 < eps) :
    ∃ m n : ℕ, 0 < n ∧
      p4Q2PZ37AHB_globalPrecisionError C m n < eps := by
  let em : ℚ := eps / (2 * (C + 1))
  let en : ℚ := eps / 8
  have hCp : (0 : ℚ) < C + 1 := by linarith only [hC]
  have hem : 0 < em := by
    dsimp [em]
    positivity
  have hen : 0 < en := by
    dsimp [en]
    positivity
  obtain ⟨m, hm⟩ := p4Q2PZ37AHB_exists_couplingTail_precision em hem
  obtain ⟨n, hn, hE⟩ := p4Q2PZ37AHB_exists_factorial_precision en hen
  have hTnonneg := p4Q2PZ37AGK_tail_nonneg m
  have hCmp : C * p4Q2PZ37AGK_tail m ≤
      (C + 1) * p4Q2PZ37AGK_tail m :=
    mul_le_mul_of_nonneg_right (by linarith : C ≤ C + 1) hTnonneg
  have hMul := mul_lt_mul_of_pos_left hm hCp
  have hEq : (C + 1) * em = eps / 2 := by
    dsimp [em]
    field_simp
  have hFirst : C * p4Q2PZ37AGK_tail m < eps / 2 :=
    hCmp.trans_lt (hMul.trans_eq hEq)
  have hSecond : 4 * p4Q2PZ37AHA_factorialEnvelope n < eps / 2 := by
    have h := mul_lt_mul_of_pos_left hE (by norm_num : (0 : ℚ) < 4)
    dsimp [en] at h
    linarith only [h]
  refine ⟨m, n, hn, ?_⟩
  unfold p4Q2PZ37AHB_globalPrecisionError
  linarith only [hFirst, hSecond]

/-- A UNIFORM precision choice for all rational original action samples
within the genuine fixed-volume budget. Neither m nor n depends on the
particular center, right boundary, or Borel partition cell. -/
theorem p4Q2PZ37AHB_exists_uniformOriginalOutputPrecision
    (C eta : ℚ) (hC : 0 ≤ C) (heta : 0 < eta) :
    ∃ m n : ℕ, 0 < n ∧
      ∀ S : ℚ, 0 ≤ S → S ≤ C →
        p4Q2PZ37AHA_couplingTaylorBudget S m n < eta := by
  let K := p4Q2PZ37AHB_globalScaleCap C
  let factor : ℚ := (K : ℚ) * (2 : ℚ) ^ K
  have hFactor : 0 ≤ factor := by
    dsimp [factor]
    positivity
  let target : ℚ := min 1 (eta / (factor + 1))
  have hTarget : 0 < target := by
    dsimp [target]
    apply lt_min (by norm_num)
    exact div_pos heta (by linarith only [hFactor])
  obtain ⟨m, n, hn, hPrec⟩ :=
    p4Q2PZ37AHB_exists_jointPrecision C target hC hTarget
  have hOne : p4Q2PZ37AHB_globalPrecisionError C m n ≤ 1 :=
    hPrec.le.trans (min_le_left _ _)
  have hLimit : p4Q2PZ37AHB_globalPrecisionError C m n < eta / (factor + 1) :=
    hPrec.trans_le (min_le_right _ _)
  have hFactorPos : 0 < factor + 1 := by linarith only [hFactor]
  have hStrict :
      p4Q2PZ37AHB_globalPrecisionError C m n * factor < eta := by
    have hMul := mul_lt_mul_of_pos_right hLimit hFactorPos
    have hPrecNonneg : 0 ≤ p4Q2PZ37AHB_globalPrecisionError C m n := by
      unfold p4Q2PZ37AHB_globalPrecisionError
      exact add_nonneg (mul_nonneg hC (p4Q2PZ37AGK_tail_nonneg m))
        (mul_nonneg (by norm_num)
          (p4Q2PZ37AHA_factorialEnvelope_nonneg n hn))
    have hProd : p4Q2PZ37AHB_globalPrecisionError C m n * factor ≤
        p4Q2PZ37AHB_globalPrecisionError C m n * (factor + 1) :=
      mul_le_mul_of_nonneg_left (by linarith : factor ≤ factor + 1) hPrecNonneg
    have hEq : eta / (factor + 1) * (factor + 1) = eta := by
      field_simp
    exact hProd.trans_lt (hMul.trans_eq hEq)
  refine ⟨m, n, hn, ?_⟩
  intro S hS hSC
  have hB := p4Q2PZ37AHB_budget_le_globalPrecisionError
    S C hS hSC m n hn hOne
  have hB' : p4Q2PZ37AHA_couplingTaylorBudget S m n ≤
      p4Q2PZ37AHB_globalPrecisionError C m n * factor := by
    simpa only [factor, K, mul_assoc] using hB
  exact hB'.trans_lt hStrict

/-- All ORIGINAL kernel/floor physical Taylor gaps, on the same AGU
grid as AGY, admit arbitrary precision for each FIXED finite H.
The orders m,n do not depend on the right boundary or chosen AGU grid. -/
theorem p4Q2PZ37AHB_exists_originalKernelFloor_precision
    (H : ℕ) (eta : ℚ) (heta : 0 < eta) :
    ∃ m n : ℕ, ∃ hn : 0 < n,
      ∀ {R eps : ℚ} (d : p4Q2PZ37AGU_precisionGridData H R eps)
        (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
        (b : ∀ e : PeriodicHypercubicEvenSpatialSliceLink H,
          p4Q2PZ37AGL_rationalCoordinates (B e)),
        p4Q2PZ37AGY_originalKernelMax H d B b m n hn < eta ∧
        p4Q2PZ37AGY_originalFloorWidth H m n hn < eta := by
  let C := p4Q2PZ37AGZ_originalFloorAction H
  have hC := p4Q2PZ37AGZ_originalFloorAction_nonneg H
  have hHalf : (0 : ℚ) < eta / 2 := by linarith only [heta]
  obtain ⟨m, n, hn, hUniform⟩ :=
    p4Q2PZ37AHB_exists_uniformOriginalOutputPrecision C (eta / 2) hC hHalf
  refine ⟨m, n, hn, ?_⟩
  intro R eps d B b
  have hKernelBound : p4Q2PZ37AHA_originalKernelBudgetMax H d B b m n ≤ eta / 2 := by
    unfold p4Q2PZ37AHA_originalKernelBudgetMax
    apply Finset.sup'_le
    intro i _hi
    have hNonneg := p4Q2PZ37AGM_originalActionRational_nonneg H
      (d.data.grid.center i) B (d.data.centerCoordinates i) b
    have hUpper := p4Q2PZ37AHB_originalAction_le_globalBudget H
      (d.data.grid.center i) B (d.data.centerCoordinates i) b
    exact (hUniform _ hNonneg hUpper).le
  have hKT := p4Q2PZ37AGZ_originalKernelMax_le_TaylorMax H d B b m n hn
  have hKB := p4Q2PZ37AHA_originalKernelTaylorMax_le_budgetMax H d B b m n hn
  have hF := (p4Q2PZ37AGZ_originalFloorWidth_le_TaylorGap H m n hn).trans
    (p4Q2PZ37AHA_originalFloorTaylorGap_le_budget H m n hn)
  have hFloor : p4Q2PZ37AHA_couplingTaylorBudget C m n < eta / 2 :=
    hUniform C hC le_rfl
  have hHalfEta : eta / 2 < eta := by linarith only [heta]
  exact ⟨(hKT.trans (hKB.trans hKernelBound)).trans_lt hHalfEta,
    (hF.trans_lt hFloor).trans hHalfEta⟩

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AHB_budget_exact
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AHB_factorialEnvelope_le_two_div
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AHB_exists_factorial_precision
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AHB_exists_couplingTail_precision
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHB_couplingBracket_unit
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHB_autoScale_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHB_lowerBase_unit
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHB_totalBaseError_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHB_originalAction_le_globalBudget
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AHB_powerGap_le_linear
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHB_budget_le_globalPrecisionError
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHB_exists_jointPrecision
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHB_exists_uniformOriginalOutputPrecision
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHB_exists_originalKernelFloor_precision
