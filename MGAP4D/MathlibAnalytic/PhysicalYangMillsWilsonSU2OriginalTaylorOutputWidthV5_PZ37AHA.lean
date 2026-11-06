import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalTaylorWidthBridgeV5_PZ37AGZ
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AHA — original exponential output-width coupling/Taylor budget

AGZ proved the exact original coupling input width rate but did NOT infer
the output width of AGJ's clipped powered Taylor interval from it. AHA
uses a genuine exp Lipschitz inequality ON THE NONPOSITIVE HALF-LINE,
an explicit factorial Taylor remainder, the necessary clipping at zero,
and an elementary monotonicity argument for nonnegative integer powers.

For original action S >= 0, AGK's rational coupling bracket gives
  lo = -(betaUpper(m) * S), hi = -(betaLower(m) * S).
AGM selects the actual rational scale k = ceil(max |lo| |hi|) + 1.
With u=lo/k, v=hi/k and P_n the actual AGJ polynomial, define
  E_n = (n+1)/(n! * n)  (n>0),
  b = max 0 (P_n(u) - TaylorError(u,n)).
The ACTUAL AGJ rational exponential endpoints satisfy
  expUpper(hi,k,n) - expLower(lo,k,n)
    <= (b + S*AGK_tail(m)/k + 4*E_n)^k - b^k.

This is an exact, finite, purely rational upper budget for the original
kernel/floor output width, not a claim about Taylor order chosen or actual
bulk spectral positivity. The term 4*E_n is deliberately conservative;
no fake source/measure/kernel or independent interval oracle enters.

Every original action/kernel/floor, the AGU same-grid finite maximum,
and AGZ signed-transfer width retain their previous physical meaning.
No uniform-in-H convergence, actual nonzero transfer, coercivity or
continuum mass gap is claimed by these finite-order inequalities.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Universal rational AGJ truncation envelope on |q| <= 1, n>0. -/
def p4Q2PZ37AHA_factorialEnvelope (n : ℕ) : ℚ :=
  ((n + 1 : ℕ) : ℚ) / ((n.factorial : ℚ) * (n : ℚ))

theorem p4Q2PZ37AHA_factorialEnvelope_nonneg (n : ℕ) (hn : 0 < n) :
    0 ≤ p4Q2PZ37AHA_factorialEnvelope n := by
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn
  unfold p4Q2PZ37AHA_factorialEnvelope
  positivity

/-- Derive a computable uniform truncation bound from AGJ's LITERAL
TaylorError formula, without replacing it by an unknown real error. -/
theorem p4Q2PZ37AHA_taylorError_le_envelope
    (q : ℚ) (n : ℕ) (hn : 0 < n) (hq : |q| ≤ 1) :
    p4Q2PZ37AGJ_taylorError q n ≤ p4Q2PZ37AHA_factorialEnvelope n := by
  have hpow : |q| ^ n ≤ (1 : ℚ) := by
    simpa using pow_le_pow_left₀ (abs_nonneg q) hq n
  have henv : 0 ≤ p4Q2PZ37AHA_factorialEnvelope n :=
    p4Q2PZ37AHA_factorialEnvelope_nonneg n hn
  calc
    p4Q2PZ37AGJ_taylorError q n =
        |q| ^ n * p4Q2PZ37AHA_factorialEnvelope n := by
          unfold p4Q2PZ37AGJ_taylorError p4Q2PZ37AHA_factorialEnvelope
          ring
    _ ≤ 1 * p4Q2PZ37AHA_factorialEnvelope n :=
      mul_le_mul_of_nonneg_right hpow henv
    _ = p4Q2PZ37AHA_factorialEnvelope n := one_mul _

theorem p4Q2PZ37AHA_taylorError_nonneg
    (q : ℚ) (n : ℕ) (hn : 0 < n) :
    0 ≤ p4Q2PZ37AGJ_taylorError q n := by
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn
  unfold p4Q2PZ37AGJ_taylorError
  positivity

/-- The original Wilson negative exponent lives in the interval where
exp is 1-Lipschitz. This follows directly from exp(z) >= 1+z and
exp(y) <= 1, without an unverified global Lipschitz assumption. -/
theorem p4Q2PZ37AHA_exp_diff_le_diff_of_nonpos
    (x y : ℝ) (hxy : x ≤ y) (hy : y ≤ 0) :
    Real.exp y - Real.exp x ≤ y - x := by
  have hDiff : x - y ≤ 0 := by linarith only [hxy]
  have hExpDiff : Real.exp (x - y) ≤ 1 := by
    calc
      Real.exp (x - y) ≤ Real.exp (0 : ℝ) := Real.exp_monotone hDiff
      _ = 1 := Real.exp_zero
  have hExpY : Real.exp y ≤ 1 := by
    calc
      Real.exp y ≤ Real.exp (0 : ℝ) := Real.exp_monotone hy
      _ = 1 := Real.exp_zero
  have hPos : 0 ≤ 1 - Real.exp (x - y) := by linarith only [hExpDiff]
  have hLinear : 1 - Real.exp (x - y) ≤ y - x := by
    have h := Real.add_one_le_exp (x - y)
    linarith only [h]
  have hRearrange : Real.exp x = Real.exp y * Real.exp (x - y) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    Real.exp y - Real.exp x = Real.exp y * (1 - Real.exp (x - y)) := by
      rw [hRearrange]
      ring
    _ ≤ 1 * (1 - Real.exp (x - y)) :=
      mul_le_mul_of_nonneg_right hExpY hPos
    _ ≤ y - x := by simpa using hLinear

/-- Clipping at zero is 1-Lipschitz from above on the rational line.
This avoids the erroneous even-power lower endpoint from an unclipped
negative Taylor approximation. -/
theorem p4Q2PZ37AHA_maxZero_sub_le
    (x y budget : ℚ) (hb : 0 ≤ budget) (hxy : y - x ≤ budget) :
    max 0 y - max 0 x ≤ budget := by
  have hMax : max 0 y ≤ max 0 x + budget := by
    apply max_le
    · have hx : (0 : ℚ) ≤ max 0 x := le_max_left _ _
      linarith only [hx, hb]
    · have hx : x ≤ max 0 x := le_max_right _ _
      linarith only [hx, hxy]
  linarith only [hMax]

/-- Quantitative AGJ base-gap: source exponent-input span plus twice
each genuine AGJ error. Both exponent arguments are scaled and nonpositive. -/
theorem p4Q2PZ37AHA_scaledTaylorBaseGap_le
    (lo hi : ℚ) (k n : ℕ) (hk : 0 < k) (hn : 0 < n)
    (hlohi : lo ≤ hi) (hhi : hi ≤ 0)
    (hloSmall : |lo / (k : ℚ)| ≤ 1)
    (hhiSmall : |hi / (k : ℚ)| ≤ 1) :
    max (0 : ℚ) (p4Q2PZ37AGJ_taylorSum (hi / (k : ℚ)) n +
      p4Q2PZ37AGJ_taylorError (hi / (k : ℚ)) n) -
    max (0 : ℚ) (p4Q2PZ37AGJ_taylorSum (lo / (k : ℚ)) n -
      p4Q2PZ37AGJ_taylorError (lo / (k : ℚ)) n) ≤
    (hi / (k : ℚ) - lo / (k : ℚ)) +
      2 * (p4Q2PZ37AGJ_taylorError (lo / (k : ℚ)) n +
        p4Q2PZ37AGJ_taylorError (hi / (k : ℚ)) n) := by
  let u : ℚ := lo / (k : ℚ)
  let v : ℚ := hi / (k : ℚ)
  let eu := p4Q2PZ37AGJ_taylorError u n
  let ev := p4Q2PZ37AGJ_taylorError v n
  let tu := p4Q2PZ37AGJ_taylorSum u n
  let tv := p4Q2PZ37AGJ_taylorSum v n
  have hkq : (0 : ℚ) < k := by exact_mod_cast hk
  have huv : u ≤ v := div_le_div_of_nonneg_right hlohi hkq.le
  have hv : v ≤ 0 := div_nonpos_of_nonpos_of_nonneg hhi hkq.le
  have hReal : Real.exp (v : ℝ) - Real.exp (u : ℝ) ≤
      (v : ℝ) - (u : ℝ) :=
    p4Q2PZ37AHA_exp_diff_le_diff_of_nonpos
      (u : ℝ) (v : ℝ) (by exact_mod_cast huv) (by exact_mod_cast hv)
  have hAccU := abs_le.mp
    (p4Q2PZ37AGJ_taylor_accuracy u n hloSmall hn)
  have hAccV := abs_le.mp
    (p4Q2PZ37AGJ_taylor_accuracy v n hhiSmall hn)
  have hPolyR :
      ((tv - tu : ℚ) : ℝ) ≤ ((v - u + ev + eu : ℚ) : ℝ) := by
    dsimp [tv, tu, ev, eu]
    push_cast
    linarith only [hReal, hAccU.2, hAccV.1]
  have hPoly : tv - tu ≤ v - u + ev + eu := by
    exact_mod_cast hPolyR
  have heu : 0 ≤ eu := p4Q2PZ37AHA_taylorError_nonneg u n hn
  have hev : 0 ≤ ev := p4Q2PZ37AHA_taylorError_nonneg v n hn
  have hBudgetNonneg : 0 ≤ (v - u) + 2 * (eu + ev) := by
    linarith only [huv, heu, hev]
  have hPolySpan : (tv + ev) - (tu - eu) ≤
      (v - u) + 2 * (eu + ev) := by
    linarith only [hPoly]
  have hClip := p4Q2PZ37AHA_maxZero_sub_le
    (tu - eu) (tv + ev) ((v - u) + 2 * (eu + ev))
    hBudgetNonneg hPolySpan
  simpa only [u, v, eu, ev, tu, tv] using hClip

/-- A checkable rational upper bound for the WHOLE powered AGJ output,
not merely the coupling-input span or the unpowered Taylor polynomial. -/
def p4Q2PZ37AHA_scaledOutputBudget
    (lo hi : ℚ) (k n : ℕ) : ℚ :=
  let u := lo / (k : ℚ)
  let v := hi / (k : ℚ)
  let b := max (0 : ℚ)
    (p4Q2PZ37AGJ_taylorSum u n - p4Q2PZ37AGJ_taylorError u n)
  (b + (v - u) +
      2 * (p4Q2PZ37AGJ_taylorError u n +
        p4Q2PZ37AGJ_taylorError v n)) ^ k - b ^ k

/-- The ACTUAL AGJ upper-lower powered Taylor width never exceeds its
explicit polynomial budget. Zero clipping is retained before exponentiation. -/
theorem p4Q2PZ37AHA_scaledExpGap_le_budget
    (lo hi : ℚ) (k n : ℕ) (hk : 0 < k) (hn : 0 < n)
    (hlohi : lo ≤ hi) (hhi : hi ≤ 0)
    (hloSmall : |lo / (k : ℚ)| ≤ 1)
    (hhiSmall : |hi / (k : ℚ)| ≤ 1) :
    p4Q2PZ37AGJ_expUpper hi k n - p4Q2PZ37AGJ_expLower lo k n ≤
      p4Q2PZ37AHA_scaledOutputBudget lo hi k n := by
  let u : ℚ := lo / (k : ℚ)
  let v : ℚ := hi / (k : ℚ)
  let b : ℚ := max 0
    (p4Q2PZ37AGJ_taylorSum u n - p4Q2PZ37AGJ_taylorError u n)
  let c : ℚ := max 0
    (p4Q2PZ37AGJ_taylorSum v n + p4Q2PZ37AGJ_taylorError v n)
  let d : ℚ := (v - u) +
    2 * (p4Q2PZ37AGJ_taylorError u n + p4Q2PZ37AGJ_taylorError v n)
  have hGap : c - b ≤ d := by
    simpa only [u, v, b, c, d] using
      p4Q2PZ37AHA_scaledTaylorBaseGap_le
        lo hi k n hk hn hlohi hhi hloSmall hhiSmall
  have hBd : c ≤ b + d := by linarith only [hGap]
  have hCNonneg : 0 ≤ c := le_max_left _ _
  have hPow : c ^ k ≤ (b + d) ^ k :=
    pow_le_pow_left₀ hCNonneg hBd k
  have hEndpoint :
      p4Q2PZ37AGJ_expUpper hi k n - p4Q2PZ37AGJ_expLower lo k n =
        c ^ k - b ^ k := rfl
  have hBudgetEq : (b + d) ^ k - b ^ k =
      p4Q2PZ37AHA_scaledOutputBudget lo hi k n := by
    dsimp [p4Q2PZ37AHA_scaledOutputBudget, b, d, u, v]
    ring
  calc
    p4Q2PZ37AGJ_expUpper hi k n - p4Q2PZ37AGJ_expLower lo k n =
        c ^ k - b ^ k := hEndpoint
    _ ≤ (b + d) ^ k - b ^ k := sub_le_sub_right hPow _
    _ = p4Q2PZ37AHA_scaledOutputBudget lo hi k n := hBudgetEq

/-- Pull both actual AGJ errors under the same factorial majorant and
the same AGK geometric coupling-rate certificate. This is a genuine
source-action-dependent rational power budget with no unknown reals. -/
def p4Q2PZ37AHA_couplingTaylorBudget (action : ℚ) (m n : ℕ) : ℚ :=
  let lo := p4Q2PZ37AGZ_exponentLower action m
  let hi := p4Q2PZ37AGZ_exponentUpper action m
  let k := p4Q2PZ37AGM_autoScale lo hi
  let u := lo / (k : ℚ)
  let b := max (0 : ℚ)
    (p4Q2PZ37AGJ_taylorSum u n - p4Q2PZ37AGJ_taylorError u n)
  (b + action * p4Q2PZ37AGK_tail m / (k : ℚ) +
    4 * p4Q2PZ37AHA_factorialEnvelope n) ^ k - b ^ k

/-- A dependent-value transport of a verified physical real interval
never changes its rational lower/upper data. The transported proof fields
retain their original containment evidence. -/
@[simp] theorem p4Q2PZ37AHA_verifiedInterval_cast_lower
    {x y : ℝ} (h : x = y) (iv : p4Q2PZ37AFV_verifiedInterval x) :
    (cast (congrArg p4Q2PZ37AFV_verifiedInterval h) iv).lower = iv.lower := by
  cases h
  rfl

@[simp] theorem p4Q2PZ37AHA_verifiedInterval_cast_upper
    {x y : ℝ} (h : x = y) (iv : p4Q2PZ37AFV_verifiedInterval x) :
    (cast (congrArg p4Q2PZ37AFV_verifiedInterval h) iv).upper = iv.upper := by
  cases h
  rfl

namespace GroundStatePosteriorJoint

/-- Fully explicit rational output-width bound for the SAME original
fixed-coupling exponent of any nonnegative rational Wilson action. -/
theorem p4Q2PZ37AHA_originalExponentGap_le_couplingTaylor
    (action : ℚ) (ha : 0 ≤ action) (m n : ℕ) (hn : 0 < n) :
    let lo := p4Q2PZ37AGZ_exponentLower action m
    let hi := p4Q2PZ37AGZ_exponentUpper action m
    let k := p4Q2PZ37AGM_autoScale lo hi
    p4Q2PZ37AGJ_expUpper hi k n - p4Q2PZ37AGJ_expLower lo k n ≤
      p4Q2PZ37AHA_couplingTaylorBudget action m n := by
  dsimp only
  let lo := p4Q2PZ37AGZ_exponentLower action m
  let hi := p4Q2PZ37AGZ_exponentUpper action m
  let k := p4Q2PZ37AGM_autoScale lo hi
  let u : ℚ := lo / (k : ℚ)
  let v : ℚ := hi / (k : ℚ)
  let b : ℚ := max 0
    (p4Q2PZ37AGJ_taylorSum u n - p4Q2PZ37AGJ_taylorError u n)
  let d : ℚ := (v - u) +
    2 * (p4Q2PZ37AGJ_taylorError u n + p4Q2PZ37AGJ_taylorError v n)
  let D : ℚ := action * p4Q2PZ37AGK_tail m / (k : ℚ) +
    4 * p4Q2PZ37AHA_factorialEnvelope n
  have hSpan := p4Q2PZ37AGZ_exponentSpan_le_couplingTail action ha m
  have hlohi : lo ≤ hi := sub_nonneg.mp hSpan.1
  have hhi : hi ≤ 0 := by
    have hb : 0 ≤ p4Q2PZ37AGK_lower m :=
      p4Q2PZ37AGK_lower_nonneg m
    dsimp [hi, p4Q2PZ37AGZ_exponentUpper]
    exact neg_nonpos.mpr (mul_nonneg hb ha)
  have hk : 0 < k := p4Q2PZ37AGM_autoScale_pos lo hi
  have hkq : (0 : ℚ) < k := by exact_mod_cast hk
  have hSmall := p4Q2PZ37AGM_scaledEndpoints lo hi
  have hGap := p4Q2PZ37AHA_scaledExpGap_le_budget
    lo hi k n hk hn hlohi hhi hSmall.1 hSmall.2
  have hEu : p4Q2PZ37AGJ_taylorError u n ≤
      p4Q2PZ37AHA_factorialEnvelope n :=
    p4Q2PZ37AHA_taylorError_le_envelope u n hn hSmall.1
  have hEv : p4Q2PZ37AGJ_taylorError v n ≤
      p4Q2PZ37AHA_factorialEnvelope n :=
    p4Q2PZ37AHA_taylorError_le_envelope v n hn hSmall.2
  have hDiv : v - u ≤ action * p4Q2PZ37AGK_tail m / (k : ℚ) := by
    have h := div_le_div_of_nonneg_right hSpan.2 hkq.le
    have heq : (hi - lo) / (k : ℚ) = v - u := by
      dsimp [u, v]
      ring
    rw [heq] at h
    exact h
  have hDelta : d ≤ D := by
    dsimp [d, D]
    linarith only [hDiv, hEu, hEv]
  have hbase : 0 ≤ b := le_max_left _ _
  have hdiff : 0 ≤ d := by
    have huv : u ≤ v := div_le_div_of_nonneg_right hlohi hkq.le
    have heu : 0 ≤ p4Q2PZ37AGJ_taylorError u n :=
      p4Q2PZ37AHA_taylorError_nonneg u n hn
    have hev : 0 ≤ p4Q2PZ37AGJ_taylorError v n :=
      p4Q2PZ37AHA_taylorError_nonneg v n hn
    dsimp [d]
    linarith only [huv, heu, hev]
  have hpow : (b + d) ^ k ≤ (b + D) ^ k :=
    pow_le_pow_left₀ (add_nonneg hbase hdiff)
      (by linarith only [hDelta]) k
  have hBudgetEq : p4Q2PZ37AHA_scaledOutputBudget lo hi k n =
      (b + d) ^ k - b ^ k := by
    dsimp [p4Q2PZ37AHA_scaledOutputBudget, b, d, u, v]
    ring
  have hGap' : p4Q2PZ37AGJ_expUpper hi k n -
      p4Q2PZ37AGJ_expLower lo k n ≤ (b + d) ^ k - b ^ k :=
    hGap.trans_eq hBudgetEq
  have hOutput : p4Q2PZ37AGJ_expUpper hi k n -
      p4Q2PZ37AGJ_expLower lo k n ≤ (b + D) ^ k - b ^ k := by
    linarith only [hGap', hpow]
  have hTargetEq : (b + D) ^ k - b ^ k =
      p4Q2PZ37AHA_couplingTaylorBudget action m n := by
    dsimp [p4Q2PZ37AHA_couplingTaylorBudget, b, D, u, k, lo, hi]
    ring
  exact hOutput.trans_eq hTargetEq

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2

local instance p4Q2PZ37AHA_links : Fintype Link := Fintype.ofFinite _

/-- The actual AGZ raw Taylor kernel gap is bounded by the explicitly
bounded original AGL action, AGK geometric tail, and AGJ factorial tail. -/
theorem p4Q2PZ37AHA_originalKernelTaylorGap_le_budget
    (A B : Cfg)
    (a : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (A e))
    (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) :
    p4Q2PZ37AGZ_originalKernelTaylorGap H A B a b m n hn ≤
      p4Q2PZ37AHA_couplingTaylorBudget
        (p4Q2PZ37AGL_slabActionRational H A B a b) m n := by
  let action := p4Q2PZ37AGL_slabActionRational H A B a b
  let lo := p4Q2PZ37AGZ_exponentLower action m
  let hi := p4Q2PZ37AGZ_exponentUpper action m
  let k := p4Q2PZ37AGM_autoScale lo hi
  have ha := p4Q2PZ37AGM_originalActionRational_nonneg H A B a b
  have h := p4Q2PZ37AHA_originalExponentGap_le_couplingTaylor action ha m n hn
  simpa [p4Q2PZ37AHA_verifiedInterval_cast_lower,
    p4Q2PZ37AHA_verifiedInterval_cast_upper,
p4Q2PZ37AGZ_originalKernelTaylorGap,
    p4Q2PZ37AGM_originalRationalKernelInterval,
    p4Q2PZ37AGK_originalRefinedKernelInterval,
    p4Q2PZ37AGJ_boltzmannInterval,
    p4Q2PZ37AGJ_scaledExpInterval,
    p4Q2PZ37AGL_originalSlabActionSingleton,
    p4Q2PZ37AGZ_exponentLower, p4Q2PZ37AGZ_exponentUpper] using h

/-- The same physical floor's raw AGJ output is controlled by its exact
AGN combinatorial action, not by a hypothetical floor-value oracle. -/
theorem p4Q2PZ37AHA_originalFloorTaylorGap_le_budget
    (m n : ℕ) (hn : 0 < n) :
    p4Q2PZ37AGZ_originalFloorTaylorGap H m n hn ≤
      p4Q2PZ37AHA_couplingTaylorBudget
        (p4Q2PZ37AGZ_originalFloorAction H) m n := by
  let action := p4Q2PZ37AGZ_originalFloorAction H
  let lo := p4Q2PZ37AGZ_exponentLower action m
  let hi := p4Q2PZ37AGZ_exponentUpper action m
  let k := p4Q2PZ37AGM_autoScale lo hi
  have ha := p4Q2PZ37AGZ_originalFloorAction_nonneg H
  have h := p4Q2PZ37AHA_originalExponentGap_le_couplingTaylor action ha m n hn
  simpa [p4Q2PZ37AGZ_originalFloorTaylorGap,
    p4Q2PZ37AGN_originalFloorRawInterval,
    p4Q2PZ37AGJ_boltzmannInterval,
    p4Q2PZ37AGJ_scaledExpInterval,
    p4Q2PZ37AGN_actionBudgetInterval,
    p4Q2PZ37AGZ_originalFloorAction,
    p4Q2PZ37AGZ_exponentLower, p4Q2PZ37AGZ_exponentUpper] using h

/-- Finite genuine spatial AGU center maximum of the new computed
coupling/factorial output budgets, retaining its nonempty true grid. -/
def p4Q2PZ37AHA_originalKernelBudgetMax
    {R eps : ℚ} (d : p4Q2PZ37AGU_precisionGridData H R eps)
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) : ℚ :=
  (Finset.univ : Finset (Fin d.data.grid.n)).sup'
    (p4Q2PZ37AGX_univNonempty H d)
    (fun i => p4Q2PZ37AHA_couplingTaylorBudget
      (p4Q2PZ37AGL_slabActionRational H
        (d.data.grid.center i) B (d.data.centerCoordinates i) b) m n)

/-- No extra factor proportional to the number of true Haar cells:
the ACTUAL AGZ kernel raw gap maximum is bounded by the same-grid
maximum of the explicit AGK/AGJ rational budgets. -/
theorem p4Q2PZ37AHA_originalKernelTaylorMax_le_budgetMax
    {R eps : ℚ} (d : p4Q2PZ37AGU_precisionGridData H R eps)
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) :
    p4Q2PZ37AGZ_originalKernelTaylorMax H d B b m n hn ≤
      p4Q2PZ37AHA_originalKernelBudgetMax H d B b m n := by
  unfold p4Q2PZ37AGZ_originalKernelTaylorMax
  apply Finset.sup'_le
  intro i _hi
  have h := p4Q2PZ37AHA_originalKernelTaylorGap_le_budget H
    (d.data.grid.center i) B (d.data.centerCoordinates i) b m n hn
  exact h.trans
    (Finset.le_sup'
      (s := (Finset.univ : Finset (Fin d.data.grid.n)))
      (f := fun j => p4Q2PZ37AHA_couplingTaylorBudget
        (p4Q2PZ37AGL_slabActionRational H
          (d.data.grid.center j) B (d.data.centerCoordinates j) b) m n)
      (Finset.mem_univ i))

/-- The actual signed-transfer interval width now has ONLY explicit
coupling geometric rate, Taylor factorial envelope, and original
AGU geometric/Haar-mass precision certificates. -/
theorem p4Q2PZ37AHA_fineOriginalTransferWidth_le_budget
    (R eps : ℚ) (hR : 0 < R) (heps : 0 < eps)
    (B : Cfg) (b : ∀ e : Link, p4Q2PZ37AGL_rationalCoordinates (B e))
    (m n : ℕ) (hn : 0 < n) :
    (p4Q2PZ37AGU_fineOriginalTransferInterval H R eps hR heps B b m n hn).upper -
      (p4Q2PZ37AGU_fineOriginalTransferInterval H R eps hR heps B b m n hn).lower ≤
      (p4Q2PZ37AGN_countRational H / 2) *
        (p4Q2PZ37AHA_originalKernelBudgetMax H
          (p4Q2PZ37AGU_fineOriginalGridData H R eps hR heps) B b m n +
          p4Q2PZ37AHA_couplingTaylorBudget
            (p4Q2PZ37AGZ_originalFloorAction H) m n / 2) +
        2 * p4Q2PZ37AGV_uniformSlope H m * R +
        2 * p4Q2PZ37AGN_transferRadius H m n hn * eps := by
  let d := p4Q2PZ37AGU_fineOriginalGridData H R eps hR heps
  have hOld := p4Q2PZ37AGZ_fineOriginalTransferWidth_le_Taylor
    H R eps hR heps B b m n hn
  have hK := p4Q2PZ37AHA_originalKernelTaylorMax_le_budgetMax H d B b m n hn
  have hF := p4Q2PZ37AHA_originalFloorTaylorGap_le_budget H m n hn
  have hp := p4Q2PZ37AGY_sourceEnvelope_nonneg H
  have hSum :
      p4Q2PZ37AGZ_originalKernelTaylorMax H d B b m n hn +
        p4Q2PZ37AGZ_originalFloorTaylorGap H m n hn / 2 ≤
      p4Q2PZ37AHA_originalKernelBudgetMax H d B b m n +
        p4Q2PZ37AHA_couplingTaylorBudget
          (p4Q2PZ37AGZ_originalFloorAction H) m n / 2 := by
    linarith only [hK, hF]
  have hMul := mul_le_mul_of_nonneg_left hSum hp
  linarith only [hOld, hMul]

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AHA_factorialEnvelope_nonneg
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AHA_taylorError_le_envelope
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AHA_taylorError_nonneg
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AHA_exp_diff_le_diff_of_nonpos
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AHA_maxZero_sub_le
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AHA_scaledTaylorBaseGap_le
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AHA_scaledExpGap_le_budget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHA_originalExponentGap_le_couplingTaylor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHA_originalKernelTaylorGap_le_budget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHA_originalFloorTaylorGap_le_budget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHA_originalKernelTaylorMax_le_budgetMax
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AHA_fineOriginalTransferWidth_le_budget
