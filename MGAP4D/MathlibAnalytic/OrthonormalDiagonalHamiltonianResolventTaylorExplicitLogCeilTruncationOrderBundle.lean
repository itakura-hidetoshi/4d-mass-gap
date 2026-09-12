import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianResolventTaylorOperatorNormMatrixElementDualityBundle
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace LinearPMap ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 1600000

/-- An explicit natural truncation order for a geometric error `q ^ N * C`.
The zero-rate case is kept separate so the formula also applies to closed balls
of radius zero.  For `0 < q < 1`, the extra successor makes the resulting
error estimate strict even when the logarithmic quotient is an integer. -/
noncomputable def geometricDecayExplicitTruncationOrder
    (q C epsilon : ℝ) : ℕ :=
  if q = 0 then 1
  else Nat.ceil (Real.log (epsilon / C) / Real.log q) + 1

/-- The explicit geometric truncation order is always positive. -/
theorem geometricDecayExplicitTruncationOrder_pos
    (q C epsilon : ℝ) :
    0 < geometricDecayExplicitTruncationOrder q C epsilon := by
  unfold geometricDecayExplicitTruncationOrder
  split_ifs
  · norm_num
  · exact Nat.succ_pos _

/-- Every degree at or above the explicit logarithmic-ceiling order makes the
geometric envelope strictly smaller than `epsilon`. -/
theorem geometricDecay_pow_mul_lt_of_explicitTruncationOrder
    {q C epsilon : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hC : 0 < C) (hepsilon : 0 < epsilon)
    {N : ℕ}
    (hN : geometricDecayExplicitTruncationOrder q C epsilon ≤ N) :
    q ^ N * C < epsilon := by
  by_cases hq : q = 0
  · subst q
    have hN1 : 1 ≤ N := by
      simpa [geometricDecayExplicitTruncationOrder] using hN
    have hN0 : N ≠ 0 := by omega
    simp [hN0, hepsilon]
  · have hqpos : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hq)
    have hlogq : Real.log q < 0 := Real.log_neg hqpos hq1
    have horder :
        Nat.ceil (Real.log (epsilon / C) / Real.log q) + 1 ≤ N := by
      simpa [geometricDecayExplicitTruncationOrder, hq] using hN
    have hceil :
        Real.log (epsilon / C) / Real.log q ≤
          (Nat.ceil (Real.log (epsilon / C) / Real.log q) : ℝ) :=
      Nat.le_ceil _
    have hceilSucc :
        (Nat.ceil (Real.log (epsilon / C) / Real.log q) : ℝ) <
          ((Nat.ceil (Real.log (epsilon / C) / Real.log q) + 1 : ℕ) : ℝ) := by
      exact_mod_cast
        Nat.lt_succ_self (Nat.ceil (Real.log (epsilon / C) / Real.log q))
    have horderCast :
        ((Nat.ceil (Real.log (epsilon / C) / Real.log q) + 1 : ℕ) : ℝ) ≤
          (N : ℝ) := by
      exact_mod_cast horder
    have hquotient_lt :
        Real.log (epsilon / C) / Real.log q < (N : ℝ) :=
      lt_of_le_of_lt hceil (lt_of_lt_of_le hceilSucc horderCast)
    have hmul := mul_lt_mul_of_neg_right hquotient_lt hlogq
    have hlogqne : Real.log q ≠ 0 := ne_of_lt hlogq
    have hlogbound :
        (N : ℝ) * Real.log q < Real.log (epsilon / C) := by
      rw [div_mul_cancel₀ _ hlogqne] at hmul
      exact hmul
    have hdivpos : 0 < epsilon / C := div_pos hepsilon hC
    have hpow : q ^ N < epsilon / C :=
      (Real.pow_lt_iff_lt_log hqpos hdivpos).2 hlogbound
    calc
      q ^ N * C < (epsilon / C) * C :=
        mul_lt_mul_of_pos_right hpow hC
      _ = epsilon := div_mul_cancel₀ epsilon (ne_of_gt hC)

/-- Explicit Taylor truncation order for the standard closed-subgap resolvent
envelope. -/
noncomputable def resolventTaylorClosedBall_explicitTruncationOrder
    (delta lambda r epsilon : ℝ) : ℕ :=
  geometricDecayExplicitTruncationOrder
    (r * (delta - lambda)⁻¹)
    ((delta - lambda - r)⁻¹)
    epsilon

/-- The explicit closed-ball resolvent truncation order is positive. -/
theorem resolventTaylorClosedBall_explicitTruncationOrder_pos
    (delta lambda r epsilon : ℝ) :
    0 < resolventTaylorClosedBall_explicitTruncationOrder
      delta lambda r epsilon := by
  exact geometricDecayExplicitTruncationOrder_pos _ _ _

/-- The logarithmic-ceiling order gives a strict epsilon bound for the exact
closed-ball geometric resolvent envelope. -/
theorem resolventTaylorClosedBall_errorEnvelope_lt_epsilon_of_explicitTruncationOrder
    {delta lambda r epsilon : ℝ}
    (hlambda : lambda < delta)
    (hr0 : 0 ≤ r) (hrlt : r < delta - lambda)
    (hepsilon : 0 < epsilon)
    {N : ℕ}
    (hN : resolventTaylorClosedBall_explicitTruncationOrder
      delta lambda r epsilon ≤ N) :
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
  exact
    geometricDecay_pow_mul_lt_of_explicitTruncationOrder
      hq0 hq1 hC hepsilon hN

/-- The explicit logarithmic-ceiling degree controls the operator-norm Taylor
remainder for every member of a common-gap orthonormal-diagonal family and every
parameter in the closed subgap ball. -/
theorem orthonormalDiagonalHamiltonianResolvent_taylor_operatorNorm_error_lt_closedBall_family_of_explicitTruncationOrder
    {J ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : J → OrthonormalBasis ι ℝ E) (a : J → ι → ℝ) (delta : ℝ)
    (hdelta : ∀ j : J, ∀ i : ι, delta ≤ a j i)
    {lambda r epsilon : ℝ} (hlambda : lambda < delta)
    (hr0 : 0 ≤ r) (hrlt : r < delta - lambda)
    (hepsilon : 0 < epsilon)
    {N : ℕ}
    (hN : resolventTaylorClosedBall_explicitTruncationOrder
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
    (resolventTaylorClosedBall_errorEnvelope_lt_epsilon_of_explicitTruncationOrder
      hlambda hr0 hrlt hepsilon hN)

/-- The same explicit degree controls every two-unit-ball real matrix element of
the Taylor remainder throughout a common-gap family. -/
theorem orthonormalDiagonalHamiltonianResolvent_taylor_matrixElement_error_abs_lt_closedBall_unitBalls_family_of_explicitTruncationOrder
    {J ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : J → OrthonormalBasis ι ℝ E) (a : J → ι → ℝ) (delta : ℝ)
    (hdelta : ∀ j : J, ∀ i : ι, delta ≤ a j i)
    {lambda r epsilon : ℝ} (hlambda : lambda < delta)
    (hr0 : 0 ≤ r) (hrlt : r < delta - lambda)
    (hepsilon : 0 < epsilon)
    {N : ℕ}
    (hN : resolventTaylorClosedBall_explicitTruncationOrder
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
    (resolventTaylorClosedBall_errorEnvelope_lt_epsilon_of_explicitTruncationOrder
      hlambda hr0 hrlt hepsilon hN)

/-- The explicit order itself, without a later-degree quantifier, gives the
family-uniform operator-norm epsilon estimate. -/
theorem orthonormalDiagonalHamiltonianResolvent_taylor_operatorNorm_error_lt_closedBall_family_at_explicitTruncationOrder
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
          (resolventTaylorClosedBall_explicitTruncationOrder
            delta lambda r epsilon),
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
            iteratedDeriv k
              (orthonormalDiagonalHamiltonianResolvent (b j) (a j)) lambda)‖ <
      epsilon := by
  exact
    orthonormalDiagonalHamiltonianResolvent_taylor_operatorNorm_error_lt_closedBall_family_of_explicitTruncationOrder
      b a delta hdelta hlambda hr0 hrlt hepsilon le_rfl j mu hmu

/-- The explicit order itself gives the simultaneous two-unit-ball
matrix-element epsilon estimate. -/
theorem orthonormalDiagonalHamiltonianResolvent_taylor_matrixElement_error_abs_lt_closedBall_unitBalls_family_at_explicitTruncationOrder
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
          (resolventTaylorClosedBall_explicitTruncationOrder
            delta lambda r epsilon),
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
            iteratedDeriv k
              (orthonormalDiagonalHamiltonianResolvent (b j) (a j)) lambda) y)| <
      epsilon := by
  exact
    orthonormalDiagonalHamiltonianResolvent_taylor_matrixElement_error_abs_lt_closedBall_unitBalls_family_of_explicitTruncationOrder
      b a delta hdelta hlambda hr0 hrlt hepsilon le_rfl j mu hmu x y hx hy

end MathlibAnalytic
end MGAP4D

end