import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianResolventTaylorExplicitLogCeilTruncationOrderBundle
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace LinearPMap ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 2400000

/-- A natural degree is admissible for a geometric envelope when the envelope is
strictly below the prescribed tolerance. -/
def geometricDecayAdmissible
    (q C epsilon : ℝ) (N : ℕ) : Prop :=
  q ^ N * C < epsilon

/-- The sharp natural truncation order for a geometric envelope `q ^ N * C`.

If the zeroth-order envelope is already below tolerance, the sharp degree is
zero.  At zero geometric rate, degree one is then the first admissible degree.
For `0 < q < 1` and `epsilon ≤ C`, the strict logarithmic threshold is the
natural floor plus one. -/
noncomputable def geometricDecaySharpTruncationOrder
    (q C epsilon : ℝ) : ℕ :=
  if C < epsilon then 0
  else if q = 0 then 1
  else Nat.floor (Real.log (epsilon / C) / Real.log q) + 1

/-- The sharp degree exactly characterizes all admissible geometric-decay
degrees. -/
theorem geometricDecaySharpTruncationOrder_le_iff
    {q C epsilon : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hC : 0 < C) (hepsilon : 0 < epsilon)
    (N : ℕ) :
    geometricDecaySharpTruncationOrder q C epsilon ≤ N ↔
      geometricDecayAdmissible q C epsilon N := by
  by_cases hCe : C < epsilon
  · constructor
    · intro _
      have hpow : q ^ N ≤ (1 : ℝ) ^ N :=
        pow_le_pow_left₀ hq0 hq1.le N
      have hmul : q ^ N * C ≤ (1 : ℝ) ^ N * C :=
        mul_le_mul_of_nonneg_right hpow hC.le
      exact lt_of_le_of_lt (by simpa using hmul) hCe
    · intro _
      simp [geometricDecaySharpTruncationOrder, hCe]
  · by_cases hq : q = 0
    · subst q
      constructor
      · intro hN
        have hN1 : 1 ≤ N := by
          simpa [geometricDecaySharpTruncationOrder, hCe] using hN
        have hN0 : N ≠ 0 := Nat.ne_of_gt hN1
        simp [geometricDecayAdmissible, hN0, hepsilon]
      · intro herror
        have hN0 : N ≠ 0 := by
          intro hzero
          subst N
          simp [geometricDecayAdmissible] at herror
          exact hCe herror
        have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
        simpa [geometricDecaySharpTruncationOrder, hCe] using hN1
    · have hqpos : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hq)
      have hlogq : Real.log q < 0 := Real.log_neg hqpos hq1
      have hratioPos : 0 < epsilon / C := div_pos hepsilon hC
      have hratioLe : epsilon / C ≤ 1 := by
        rw [div_le_iff₀ hC]
        simpa using le_of_not_gt hCe
      have hlogratio : Real.log (epsilon / C) ≤ 0 :=
        Real.log_nonpos hratioPos.le hratioLe
      have ht0 :
          0 ≤ Real.log (epsilon / C) / Real.log q := by
        rw [div_eq_mul_inv]
        exact
          mul_nonneg_of_nonpos_of_nonpos hlogratio
            (inv_nonpos.mpr hlogq.le)
      constructor
      · intro hN
        have horder :
            Nat.floor (Real.log (epsilon / C) / Real.log q) + 1 ≤ N := by
          simpa [geometricDecaySharpTruncationOrder, hCe, hq] using hN
        have htFloor :
            Real.log (epsilon / C) / Real.log q <
              ((Nat.floor (Real.log (epsilon / C) / Real.log q) + 1 : ℕ) : ℝ) := by
          simpa using
            (Nat.lt_floor_add_one
              (Real.log (epsilon / C) / Real.log q))
        have horderCast :
            ((Nat.floor (Real.log (epsilon / C) / Real.log q) + 1 : ℕ) : ℝ) ≤
              (N : ℝ) := by
          exact_mod_cast horder
        have htN :
            Real.log (epsilon / C) / Real.log q < (N : ℝ) :=
          lt_of_lt_of_le htFloor horderCast
        have hlogbound :
            (N : ℝ) * Real.log q < Real.log (epsilon / C) :=
          (div_lt_iff_of_neg hlogq).1 htN
        have hpow : q ^ N < epsilon / C :=
          (Real.pow_lt_iff_lt_log hqpos hratioPos).2 hlogbound
        have hmul : q ^ N * C < (epsilon / C) * C :=
          mul_lt_mul_of_pos_right hpow hC
        simpa [geometricDecayAdmissible, div_mul_cancel₀ epsilon (ne_of_gt hC)] using hmul
      · intro herror
        have hpow : q ^ N < epsilon / C := by
          rw [lt_div_iff₀ hC]
          exact herror
        have hlogbound :
            (N : ℝ) * Real.log q < Real.log (epsilon / C) :=
          (Real.pow_lt_iff_lt_log hqpos hratioPos).1 hpow
        have htN :
            Real.log (epsilon / C) / Real.log q < (N : ℝ) :=
          (div_lt_iff_of_neg hlogq).2 hlogbound
        have hfloor :
            Nat.floor (Real.log (epsilon / C) / Real.log q) < N :=
          (Nat.floor_lt ht0).2 htN
        have horder :
            Nat.floor (Real.log (epsilon / C) / Real.log q) + 1 ≤ N :=
          Nat.succ_le_iff.mpr hfloor
        simpa [geometricDecaySharpTruncationOrder, hCe, hq] using horder

/-- The sharp geometric degree is the least admissible natural degree. -/
theorem geometricDecaySharpTruncationOrder_isLeast
    {q C epsilon : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hC : 0 < C) (hepsilon : 0 < epsilon) :
    IsLeast
      {N : ℕ | geometricDecayAdmissible q C epsilon N}
      (geometricDecaySharpTruncationOrder q C epsilon) := by
  constructor
  · exact
      (geometricDecaySharpTruncationOrder_le_iff
        hq0 hq1 hC hepsilon
        (geometricDecaySharpTruncationOrder q C epsilon)).1 le_rfl
  · intro N hN
    exact
      (geometricDecaySharpTruncationOrder_le_iff
        hq0 hq1 hC hepsilon N).2 hN

/-- The geometric envelope is admissible at the sharp degree itself. -/
theorem geometricDecay_at_sharpTruncationOrder_lt
    {q C epsilon : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hC : 0 < C) (hepsilon : 0 < epsilon) :
    q ^ geometricDecaySharpTruncationOrder q C epsilon * C < epsilon := by
  exact
    (geometricDecaySharpTruncationOrder_le_iff
      hq0 hq1 hC hepsilon
      (geometricDecaySharpTruncationOrder q C epsilon)).1 le_rfl

/-- Every degree below the sharp threshold fails the strict tolerance test. -/
theorem geometricDecay_not_lt_before_sharpTruncationOrder
    {q C epsilon : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hC : 0 < C) (hepsilon : 0 < epsilon)
    {N : ℕ}
    (hN : N < geometricDecaySharpTruncationOrder q C epsilon) :
    epsilon ≤ q ^ N * C := by
  by_contra hnot
  have hadm : q ^ N * C < epsilon := lt_of_not_ge hnot
  have hle : geometricDecaySharpTruncationOrder q C epsilon ≤ N :=
    (geometricDecaySharpTruncationOrder_le_iff
      hq0 hq1 hC hepsilon N).2 hadm
  omega

/-- Degree zero is sharp exactly when the untruncated envelope constant is
already below tolerance. -/
theorem geometricDecaySharpTruncationOrder_eq_zero_iff
    {q C epsilon : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hC : 0 < C) (hepsilon : 0 < epsilon) :
    geometricDecaySharpTruncationOrder q C epsilon = 0 ↔ C < epsilon := by
  constructor
  · intro hzero
    have hle : geometricDecaySharpTruncationOrder q C epsilon ≤ 0 := by
      simpa [hzero]
    have herror :=
      (geometricDecaySharpTruncationOrder_le_iff
        hq0 hq1 hC hepsilon 0).1 hle
    simpa [geometricDecayAdmissible] using herror
  · intro hCe
    simp [geometricDecaySharpTruncationOrder, hCe]

/-- The sharp degree is positive exactly when the zeroth-order constant is not
below tolerance. -/
theorem geometricDecaySharpTruncationOrder_pos_iff
    {q C epsilon : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hC : 0 < C) (hepsilon : 0 < epsilon) :
    0 < geometricDecaySharpTruncationOrder q C epsilon ↔ epsilon ≤ C := by
  constructor
  · intro hpos
    exact le_of_not_gt fun hCe => by
      have hzero :=
        (geometricDecaySharpTruncationOrder_eq_zero_iff
          hq0 hq1 hC hepsilon).2 hCe
      omega
  · intro heC
    have hne : geometricDecaySharpTruncationOrder q C epsilon ≠ 0 := by
      intro hzero
      have hCe :=
        (geometricDecaySharpTruncationOrder_eq_zero_iff
          hq0 hq1 hC hepsilon).1 hzero
      exact (not_lt_of_ge heC) hCe
    exact Nat.pos_of_ne_zero hne

/-- The earlier logarithmic-ceiling order is always admissible, so the sharp
order never exceeds it. -/
theorem geometricDecaySharpTruncationOrder_le_explicitTruncationOrder
    {q C epsilon : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hC : 0 < C) (hepsilon : 0 < epsilon) :
    geometricDecaySharpTruncationOrder q C epsilon ≤
      geometricDecayExplicitTruncationOrder q C epsilon := by
  apply
    (geometricDecaySharpTruncationOrder_le_iff
      hq0 hq1 hC hepsilon
      (geometricDecayExplicitTruncationOrder q C epsilon)).2
  exact
    geometricDecay_pow_mul_lt_of_explicitTruncationOrder
      hq0 hq1 hC hepsilon le_rfl

/-- The logarithmic-ceiling order is conservative by at most one Taylor degree
relative to the sharp threshold. -/
theorem geometricDecayExplicitTruncationOrder_le_sharp_add_one
    {q C epsilon : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hC : 0 < C) (hepsilon : 0 < epsilon) :
    geometricDecayExplicitTruncationOrder q C epsilon ≤
      geometricDecaySharpTruncationOrder q C epsilon + 1 := by
  by_cases hCe : C < epsilon
  · by_cases hq : q = 0
    · simp [geometricDecayExplicitTruncationOrder,
        geometricDecaySharpTruncationOrder, hCe, hq]
    · have hqpos : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hq)
      have hlogq : Real.log q < 0 := Real.log_neg hqpos hq1
      have hratioGt : 1 < epsilon / C := by
        rw [lt_div_iff₀ hC]
        simpa using hCe
      have hlogratio : 0 < Real.log (epsilon / C) :=
        Real.log_pos hratioGt
      have htneg :
          Real.log (epsilon / C) / Real.log q < 0 :=
        div_neg_of_pos_of_neg hlogratio hlogq
      have hceil0 :
          Nat.ceil (Real.log (epsilon / C) / Real.log q) = 0 :=
        (Nat.ceil_eq_zero).2 htneg.le
      simp [geometricDecayExplicitTruncationOrder,
        geometricDecaySharpTruncationOrder, hCe, hq, hceil0]
  · by_cases hq : q = 0
    · simp [geometricDecayExplicitTruncationOrder,
        geometricDecaySharpTruncationOrder, hCe, hq]
    · have hceil :
          Nat.ceil (Real.log (epsilon / C) / Real.log q) ≤
            Nat.floor (Real.log (epsilon / C) / Real.log q) + 1 :=
        Nat.ceil_le_floor_add_one _
      have hadd := Nat.add_le_add_right hceil 1
      simpa [geometricDecayExplicitTruncationOrder,
        geometricDecaySharpTruncationOrder, hCe, hq] using hadd

/-- Increasing the tolerance cannot increase the sharp truncation degree. -/
theorem geometricDecaySharpTruncationOrder_antitone_epsilon
    {q C epsilon₁ epsilon₂ : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hC : 0 < C)
    (hepsilon₁ : 0 < epsilon₁) (hepsilon₂ : 0 < epsilon₂)
    (heps : epsilon₁ ≤ epsilon₂) :
    geometricDecaySharpTruncationOrder q C epsilon₂ ≤
      geometricDecaySharpTruncationOrder q C epsilon₁ := by
  apply
    (geometricDecaySharpTruncationOrder_le_iff
      hq0 hq1 hC hepsilon₂
      (geometricDecaySharpTruncationOrder q C epsilon₁)).2
  exact lt_of_lt_of_le
    (geometricDecay_at_sharpTruncationOrder_lt
      hq0 hq1 hC hepsilon₁) heps

/-- Increasing the envelope constant cannot decrease the sharp truncation
degree. -/
theorem geometricDecaySharpTruncationOrder_mono_constant
    {q C₁ C₂ epsilon : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (hC : C₁ ≤ C₂) (hepsilon : 0 < epsilon) :
    geometricDecaySharpTruncationOrder q C₁ epsilon ≤
      geometricDecaySharpTruncationOrder q C₂ epsilon := by
  let N := geometricDecaySharpTruncationOrder q C₂ epsilon
  apply
    (geometricDecaySharpTruncationOrder_le_iff
      hq0 hq1 hC₁ hepsilon N).2
  have hN := geometricDecay_at_sharpTruncationOrder_lt
    hq0 hq1 hC₂ hepsilon
  have hpow0 : 0 ≤ q ^ N := pow_nonneg hq0 N
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left hC hpow0) hN

/-- Increasing the geometric rate within `[0,1)` cannot decrease the sharp
truncation degree. -/
theorem geometricDecaySharpTruncationOrder_mono_rate
    {q₁ q₂ C epsilon : ℝ}
    (hq₁0 : 0 ≤ q₁) (hq₂0 : 0 ≤ q₂)
    (hq₁₂ : q₁ ≤ q₂) (hq₂1 : q₂ < 1)
    (hC : 0 < C) (hepsilon : 0 < epsilon) :
    geometricDecaySharpTruncationOrder q₁ C epsilon ≤
      geometricDecaySharpTruncationOrder q₂ C epsilon := by
  have hq₁1 : q₁ < 1 := lt_of_le_of_lt hq₁₂ hq₂1
  let N := geometricDecaySharpTruncationOrder q₂ C epsilon
  apply
    (geometricDecaySharpTruncationOrder_le_iff
      hq₁0 hq₁1 hC hepsilon N).2
  have hN := geometricDecay_at_sharpTruncationOrder_lt
    hq₂0 hq₂1 hC hepsilon
  have hpow : q₁ ^ N ≤ q₂ ^ N :=
    pow_le_pow_left₀ hq₁0 hq₁₂ N
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right hpow hC.le) hN

/-- Joint monotonicity: a larger rate, a larger envelope constant, or a smaller
tolerance can only increase the sharp truncation requirement. -/
theorem geometricDecaySharpTruncationOrder_mono_rate_constant_antitone_tolerance
    {q₁ q₂ C₁ C₂ epsilon₁ epsilon₂ : ℝ}
    (hq₁0 : 0 ≤ q₁) (hq₂0 : 0 ≤ q₂)
    (hq₁₂ : q₁ ≤ q₂) (hq₂1 : q₂ < 1)
    (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hC₁₂ : C₁ ≤ C₂)
    (hepsilon₁ : 0 < epsilon₁) (hepsilon₂ : 0 < epsilon₂)
    (hepsilon₂₁ : epsilon₂ ≤ epsilon₁) :
    geometricDecaySharpTruncationOrder q₁ C₁ epsilon₁ ≤
      geometricDecaySharpTruncationOrder q₂ C₂ epsilon₂ := by
  calc
    geometricDecaySharpTruncationOrder q₁ C₁ epsilon₁ ≤
        geometricDecaySharpTruncationOrder q₂ C₁ epsilon₁ :=
      geometricDecaySharpTruncationOrder_mono_rate
        hq₁0 hq₂0 hq₁₂ hq₂1 hC₁ hepsilon₁
    _ ≤ geometricDecaySharpTruncationOrder q₂ C₂ epsilon₁ :=
      geometricDecaySharpTruncationOrder_mono_constant
        hq₂0 hq₂1 hC₁ hC₂ hC₁₂ hepsilon₁
    _ ≤ geometricDecaySharpTruncationOrder q₂ C₂ epsilon₂ :=
      geometricDecaySharpTruncationOrder_antitone_epsilon
        hq₂0 hq₂1 hC₂ hepsilon₂ hepsilon₁ hepsilon₂₁

/-- Sharp truncation order for the standard closed-subgap resolvent envelope. -/
noncomputable def resolventTaylorClosedBall_sharpTruncationOrder
    (delta lambda r epsilon : ℝ) : ℕ :=
  geometricDecaySharpTruncationOrder
    (r * (delta - lambda)⁻¹)
    ((delta - lambda - r)⁻¹)
    epsilon

/-- The closed-ball sharp order exactly characterizes the degrees for which the
standard resolvent error envelope lies below tolerance. -/
theorem resolventTaylorClosedBall_sharpTruncationOrder_le_iff
    {delta lambda r epsilon : ℝ}
    (hlambda : lambda < delta)
    (hr0 : 0 ≤ r) (hrlt : r < delta - lambda)
    (hepsilon : 0 < epsilon)
    (N : ℕ) :
    resolventTaylorClosedBall_sharpTruncationOrder
        delta lambda r epsilon ≤ N ↔
      (r * (delta - lambda)⁻¹) ^ N *
        (delta - lambda - r)⁻¹ < epsilon := by
  have hbase : 0 < delta - lambda := sub_pos.mpr hlambda
  have hq0 : 0 ≤ r * (delta - lambda)⁻¹ :=
    mul_nonneg hr0 (inv_nonneg.mpr hbase.le)
  have hq1 : r * (delta - lambda)⁻¹ < 1 := by
    calc
      r * (delta - lambda)⁻¹ <
          (delta - lambda) * (delta - lambda)⁻¹ :=
        mul_lt_mul_of_pos_right hrlt (inv_pos.mpr hbase)
      _ = 1 := by simp [ne_of_gt hbase]
  have hC : 0 < (delta - lambda - r)⁻¹ :=
    inv_pos.mpr (sub_pos.mpr hrlt)
  simpa [resolventTaylorClosedBall_sharpTruncationOrder,
    geometricDecayAdmissible] using
    (geometricDecaySharpTruncationOrder_le_iff
      hq0 hq1 hC hepsilon N)

/-- The sharp closed-ball resolvent degree is the least natural degree making
the geometric envelope strictly smaller than tolerance. -/
theorem resolventTaylorClosedBall_sharpTruncationOrder_isLeast
    {delta lambda r epsilon : ℝ}
    (hlambda : lambda < delta)
    (hr0 : 0 ≤ r) (hrlt : r < delta - lambda)
    (hepsilon : 0 < epsilon) :
    IsLeast
      {N : ℕ |
        (r * (delta - lambda)⁻¹) ^ N *
          (delta - lambda - r)⁻¹ < epsilon}
      (resolventTaylorClosedBall_sharpTruncationOrder
        delta lambda r epsilon) := by
  constructor
  · exact
      (resolventTaylorClosedBall_sharpTruncationOrder_le_iff
        hlambda hr0 hrlt hepsilon
        (resolventTaylorClosedBall_sharpTruncationOrder
          delta lambda r epsilon)).1 le_rfl
  · intro N hN
    exact
      (resolventTaylorClosedBall_sharpTruncationOrder_le_iff
        hlambda hr0 hrlt hepsilon N).2 hN

/-- The previous explicit logarithmic-ceiling degree is within one degree of the
sharp closed-ball resolvent threshold. -/
theorem resolventTaylorClosedBall_sharp_explicit_sandwich
    {delta lambda r epsilon : ℝ}
    (hlambda : lambda < delta)
    (hr0 : 0 ≤ r) (hrlt : r < delta - lambda)
    (hepsilon : 0 < epsilon) :
    resolventTaylorClosedBall_sharpTruncationOrder delta lambda r epsilon ≤
      resolventTaylorClosedBall_explicitTruncationOrder delta lambda r epsilon ∧
    resolventTaylorClosedBall_explicitTruncationOrder delta lambda r epsilon ≤
      resolventTaylorClosedBall_sharpTruncationOrder delta lambda r epsilon + 1 := by
  have hbase : 0 < delta - lambda := sub_pos.mpr hlambda
  have hq0 : 0 ≤ r * (delta - lambda)⁻¹ :=
    mul_nonneg hr0 (inv_nonneg.mpr hbase.le)
  have hq1 : r * (delta - lambda)⁻¹ < 1 := by
    calc
      r * (delta - lambda)⁻¹ <
          (delta - lambda) * (delta - lambda)⁻¹ :=
        mul_lt_mul_of_pos_right hrlt (inv_pos.mpr hbase)
      _ = 1 := by simp [ne_of_gt hbase]
  have hC : 0 < (delta - lambda - r)⁻¹ :=
    inv_pos.mpr (sub_pos.mpr hrlt)
  constructor
  · simpa [resolventTaylorClosedBall_sharpTruncationOrder,
      resolventTaylorClosedBall_explicitTruncationOrder] using
      (geometricDecaySharpTruncationOrder_le_explicitTruncationOrder
        hq0 hq1 hC hepsilon)
  · simpa [resolventTaylorClosedBall_sharpTruncationOrder,
      resolventTaylorClosedBall_explicitTruncationOrder] using
      (geometricDecayExplicitTruncationOrder_le_sharp_add_one
        hq0 hq1 hC hepsilon)

/-- Enlarging the closed-ball radius cannot decrease the sharp Taylor degree. -/
theorem resolventTaylorClosedBall_sharpTruncationOrder_mono_radius
    {delta lambda r₁ r₂ epsilon : ℝ}
    (hlambda : lambda < delta)
    (hr₁0 : 0 ≤ r₁) (hr₁₂ : r₁ ≤ r₂)
    (hr₂lt : r₂ < delta - lambda)
    (hepsilon : 0 < epsilon) :
    resolventTaylorClosedBall_sharpTruncationOrder
        delta lambda r₁ epsilon ≤
      resolventTaylorClosedBall_sharpTruncationOrder
        delta lambda r₂ epsilon := by
  have hbase : 0 < delta - lambda := sub_pos.mpr hlambda
  have hr₂0 : 0 ≤ r₂ := le_trans hr₁0 hr₁₂
  have hq₁0 : 0 ≤ r₁ * (delta - lambda)⁻¹ :=
    mul_nonneg hr₁0 (inv_nonneg.mpr hbase.le)
  have hq₂0 : 0 ≤ r₂ * (delta - lambda)⁻¹ :=
    mul_nonneg hr₂0 (inv_nonneg.mpr hbase.le)
  have hq₁₂ :
      r₁ * (delta - lambda)⁻¹ ≤ r₂ * (delta - lambda)⁻¹ :=
    mul_le_mul_of_nonneg_right hr₁₂ (inv_nonneg.mpr hbase.le)
  have hq₂1 : r₂ * (delta - lambda)⁻¹ < 1 := by
    calc
      r₂ * (delta - lambda)⁻¹ <
          (delta - lambda) * (delta - lambda)⁻¹ :=
        mul_lt_mul_of_pos_right hr₂lt (inv_pos.mpr hbase)
      _ = 1 := by simp [ne_of_gt hbase]
  have hmargin₂ : 0 < delta - lambda - r₂ := sub_pos.mpr hr₂lt
  have hmargin₁ : 0 < delta - lambda - r₁ := by linarith
  have hC₁ : 0 < (delta - lambda - r₁)⁻¹ := inv_pos.mpr hmargin₁
  have hC₂ : 0 < (delta - lambda - r₂)⁻¹ := inv_pos.mpr hmargin₂
  have hmarginOrder : delta - lambda - r₂ ≤ delta - lambda - r₁ := by
    linarith
  have hC₁₂ :
      (delta - lambda - r₁)⁻¹ ≤ (delta - lambda - r₂)⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le hmargin₂ hmarginOrder
  simpa [resolventTaylorClosedBall_sharpTruncationOrder] using
    (geometricDecaySharpTruncationOrder_mono_rate_constant_antitone_tolerance
      hq₁0 hq₂0 hq₁₂ hq₂1 hC₁ hC₂ hC₁₂
      hepsilon hepsilon le_rfl)

/-- Moving the Taylor center toward the spectral gap cannot decrease the sharp
closed-ball truncation requirement. -/
theorem resolventTaylorClosedBall_sharpTruncationOrder_mono_center
    {delta lambda₁ lambda₂ r epsilon : ℝ}
    (hlambda₁₂ : lambda₁ ≤ lambda₂)
    (hlambda₂ : lambda₂ < delta)
    (hr0 : 0 ≤ r) (hrlt₂ : r < delta - lambda₂)
    (hepsilon : 0 < epsilon) :
    resolventTaylorClosedBall_sharpTruncationOrder
        delta lambda₁ r epsilon ≤
      resolventTaylorClosedBall_sharpTruncationOrder
        delta lambda₂ r epsilon := by
  have hbase₂ : 0 < delta - lambda₂ := sub_pos.mpr hlambda₂
  have hbase₁ : 0 < delta - lambda₁ := by linarith
  have hbaseOrder : delta - lambda₂ ≤ delta - lambda₁ := by linarith
  have hinvOrder :
      (delta - lambda₁)⁻¹ ≤ (delta - lambda₂)⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le hbase₂ hbaseOrder
  have hq₁0 : 0 ≤ r * (delta - lambda₁)⁻¹ :=
    mul_nonneg hr0 (inv_nonneg.mpr hbase₁.le)
  have hq₂0 : 0 ≤ r * (delta - lambda₂)⁻¹ :=
    mul_nonneg hr0 (inv_nonneg.mpr hbase₂.le)
  have hq₁₂ :
      r * (delta - lambda₁)⁻¹ ≤ r * (delta - lambda₂)⁻¹ :=
    mul_le_mul_of_nonneg_left hinvOrder hr0
  have hq₂1 : r * (delta - lambda₂)⁻¹ < 1 := by
    calc
      r * (delta - lambda₂)⁻¹ <
          (delta - lambda₂) * (delta - lambda₂)⁻¹ :=
        mul_lt_mul_of_pos_right hrlt₂ (inv_pos.mpr hbase₂)
      _ = 1 := by simp [ne_of_gt hbase₂]
  have hmargin₂ : 0 < delta - lambda₂ - r := sub_pos.mpr hrlt₂
  have hmargin₁ : 0 < delta - lambda₁ - r := by linarith
  have hmarginOrder :
      delta - lambda₂ - r ≤ delta - lambda₁ - r := by linarith
  have hC₁ : 0 < (delta - lambda₁ - r)⁻¹ := inv_pos.mpr hmargin₁
  have hC₂ : 0 < (delta - lambda₂ - r)⁻¹ := inv_pos.mpr hmargin₂
  have hC₁₂ :
      (delta - lambda₁ - r)⁻¹ ≤ (delta - lambda₂ - r)⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le hmargin₂ hmarginOrder
  simpa [resolventTaylorClosedBall_sharpTruncationOrder] using
    (geometricDecaySharpTruncationOrder_mono_rate_constant_antitone_tolerance
      hq₁0 hq₂0 hq₁₂ hq₂1 hC₁ hC₂ hC₁₂
      hepsilon hepsilon le_rfl)

/-- Increasing the error tolerance cannot increase the sharp closed-ball
resolvent degree. -/
theorem resolventTaylorClosedBall_sharpTruncationOrder_antitone_epsilon
    {delta lambda r epsilon₁ epsilon₂ : ℝ}
    (hlambda : lambda < delta)
    (hr0 : 0 ≤ r) (hrlt : r < delta - lambda)
    (hepsilon₁ : 0 < epsilon₁) (hepsilon₂ : 0 < epsilon₂)
    (heps : epsilon₁ ≤ epsilon₂) :
    resolventTaylorClosedBall_sharpTruncationOrder
        delta lambda r epsilon₂ ≤
      resolventTaylorClosedBall_sharpTruncationOrder
        delta lambda r epsilon₁ := by
  have hbase : 0 < delta - lambda := sub_pos.mpr hlambda
  have hq0 : 0 ≤ r * (delta - lambda)⁻¹ :=
    mul_nonneg hr0 (inv_nonneg.mpr hbase.le)
  have hq1 : r * (delta - lambda)⁻¹ < 1 := by
    calc
      r * (delta - lambda)⁻¹ <
          (delta - lambda) * (delta - lambda)⁻¹ :=
        mul_lt_mul_of_pos_right hrlt (inv_pos.mpr hbase)
      _ = 1 := by simp [ne_of_gt hbase]
  have hC : 0 < (delta - lambda - r)⁻¹ :=
    inv_pos.mpr (sub_pos.mpr hrlt)
  simpa [resolventTaylorClosedBall_sharpTruncationOrder] using
    (geometricDecaySharpTruncationOrder_antitone_epsilon
      hq0 hq1 hC hepsilon₁ hepsilon₂ heps)

/-- Every degree at or above the sharp envelope threshold controls the
operator-norm Taylor remainder throughout a common-gap family. -/
theorem orthonormalDiagonalHamiltonianResolvent_taylor_operatorNorm_error_lt_closedBall_family_of_sharpTruncationOrder
    {J ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : J → OrthonormalBasis ι ℝ E) (a : J → ι → ℝ) (delta : ℝ)
    (hdelta : ∀ j : J, ∀ i : ι, delta ≤ a j i)
    {lambda r epsilon : ℝ} (hlambda : lambda < delta)
    (hr0 : 0 ≤ r) (hrlt : r < delta - lambda)
    (hepsilon : 0 < epsilon)
    {N : ℕ}
    (hN : resolventTaylorClosedBall_sharpTruncationOrder
      delta lambda r epsilon ≤ N)
    (j : J) (mu : ℝ) (hmu : ‖mu - lambda‖ ≤ r) :
    ‖orthonormalDiagonalHamiltonianResolvent (b j) (a j) mu -
        (∑ k ∈ Finset.range N,
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
            iteratedDeriv k
              (orthonormalDiagonalHamiltonianResolvent (b j) (a j)) lambda)‖ <
      epsilon := by
  exact lt_of_le_of_lt
    (orthonormalDiagonalHamiltonianResolvent_sub_taylor_partialSum_norm_le_closedBall_family
      b a delta hdelta hlambda hr0 hrlt hmu N j)
    ((resolventTaylorClosedBall_sharpTruncationOrder_le_iff
      hlambda hr0 hrlt hepsilon N).1 hN)

/-- The same sharp degree controls every two-unit-ball real matrix element
throughout a common-gap family. -/
theorem orthonormalDiagonalHamiltonianResolvent_taylor_matrixElement_error_abs_lt_closedBall_unitBalls_family_of_sharpTruncationOrder
    {J ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : J → OrthonormalBasis ι ℝ E) (a : J → ι → ℝ) (delta : ℝ)
    (hdelta : ∀ j : J, ∀ i : ι, delta ≤ a j i)
    {lambda r epsilon : ℝ} (hlambda : lambda < delta)
    (hr0 : 0 ≤ r) (hrlt : r < delta - lambda)
    (hepsilon : 0 < epsilon)
    {N : ℕ}
    (hN : resolventTaylorClosedBall_sharpTruncationOrder
      delta lambda r epsilon ≤ N)
    (j : J) (mu : ℝ) (hmu : ‖mu - lambda‖ ≤ r)
    (x y : E) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    |inner ℝ x
      ((orthonormalDiagonalHamiltonianResolvent (b j) (a j) mu -
        ∑ k ∈ Finset.range N,
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
            iteratedDeriv k
              (orthonormalDiagonalHamiltonianResolvent (b j) (a j)) lambda) y)| <
      epsilon := by
  exact lt_of_le_of_lt
    (orthonormalDiagonalHamiltonianResolvent_taylor_matrixElement_error_abs_le_closedBall_unitBalls_family
      b a delta hdelta hlambda hr0 hrlt hmu N j x y hx hy)
    ((resolventTaylorClosedBall_sharpTruncationOrder_le_iff
      hlambda hr0 hrlt hepsilon N).1 hN)

/-- At the sharp envelope degree itself, the entire common-gap family satisfies
the operator-norm tolerance. -/
theorem orthonormalDiagonalHamiltonianResolvent_taylor_operatorNorm_error_lt_closedBall_family_at_sharpTruncationOrder
    {J ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : J → OrthonormalBasis ι ℝ E) (a : J → ι → ℝ) (delta : ℝ)
    (hdelta : ∀ j : J, ∀ i : ι, delta ≤ a j i)
    {lambda r epsilon : ℝ} (hlambda : lambda < delta)
    (hr0 : 0 ≤ r) (hrlt : r < delta - lambda)
    (hepsilon : 0 < epsilon)
    (j : J) (mu : ℝ) (hmu : ‖mu - lambda‖ ≤ r) :
    ‖orthonormalDiagonalHamiltonianResolvent (b j) (a j) mu -
        (∑ k ∈ Finset.range
          (resolventTaylorClosedBall_sharpTruncationOrder
            delta lambda r epsilon),
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
            iteratedDeriv k
              (orthonormalDiagonalHamiltonianResolvent (b j) (a j)) lambda)‖ <
      epsilon := by
  exact
    orthonormalDiagonalHamiltonianResolvent_taylor_operatorNorm_error_lt_closedBall_family_of_sharpTruncationOrder
      b a delta hdelta hlambda hr0 hrlt hepsilon le_rfl j mu hmu

/-- At the sharp envelope degree itself, all common-gap family matrix elements
on the two unit balls satisfy the tolerance. -/
theorem orthonormalDiagonalHamiltonianResolvent_taylor_matrixElement_error_abs_lt_closedBall_unitBalls_family_at_sharpTruncationOrder
    {J ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : J → OrthonormalBasis ι ℝ E) (a : J → ι → ℝ) (delta : ℝ)
    (hdelta : ∀ j : J, ∀ i : ι, delta ≤ a j i)
    {lambda r epsilon : ℝ} (hlambda : lambda < delta)
    (hr0 : 0 ≤ r) (hrlt : r < delta - lambda)
    (hepsilon : 0 < epsilon)
    (j : J) (mu : ℝ) (hmu : ‖mu - lambda‖ ≤ r)
    (x y : E) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    |inner ℝ x
      ((orthonormalDiagonalHamiltonianResolvent (b j) (a j) mu -
        ∑ k ∈ Finset.range
          (resolventTaylorClosedBall_sharpTruncationOrder
            delta lambda r epsilon),
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
            iteratedDeriv k
              (orthonormalDiagonalHamiltonianResolvent (b j) (a j)) lambda) y)| <
      epsilon := by
  exact
    orthonormalDiagonalHamiltonianResolvent_taylor_matrixElement_error_abs_lt_closedBall_unitBalls_family_of_sharpTruncationOrder
      b a delta hdelta hlambda hr0 hrlt hepsilon le_rfl
      j mu hmu x y hx hy

end MathlibAnalytic
end MGAP4D

end
