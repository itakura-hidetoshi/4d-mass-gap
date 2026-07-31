import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorStrongLimit
import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianResolventTaylorOperatorNormLimitTransferBundle
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 3200000

/-- Open resolvent calculus together with the reciprocal distance-to-gap
operator-norm estimate. -/
structure ContinuousLinearMapOpenResolventNormBoundData
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    extends ContinuousLinearMapOpenResolventData E where
  resolvent_norm_le : ∀ {lambda : ℝ}, lambda < gap →
    ‖resolvent lambda‖ ≤ (gap - lambda)⁻¹

namespace ContinuousLinearMapOpenResolventNormBoundData

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [CompleteSpace E]

/-- A proof-indexed below-gap family with the reciprocal gap bound canonically
determines norm-bounded open-resolvent data. -/
noncomputable def ofBelowGapFamily
    (gap : ℝ) (R : ∀ lambda : ℝ, lambda < gap → E →L[ℝ] E)
    (hsub : ∀ {lambda mu : ℝ}
      (hlambda : lambda < gap) (hmu : mu < gap),
      ‖R lambda hlambda - R mu hmu‖ ≤
        |lambda - mu| * ((gap - lambda)⁻¹ * (gap - mu)⁻¹))
    (hidentity : ∀ {lambda mu : ℝ}
      (hlambda : lambda < gap) (hmu : mu < gap),
      R lambda hlambda - R mu hmu =
        (lambda - mu) • ((R lambda hlambda).comp (R mu hmu)))
    (hnorm : ∀ {lambda : ℝ} (hlambda : lambda < gap),
      ‖R lambda hlambda‖ ≤ (gap - lambda)⁻¹) :
    ContinuousLinearMapOpenResolventNormBoundData E where
  gap := gap
  resolvent := belowGapContinuousLinearMapFamily gap R
  continuousOn :=
    belowGapContinuousLinearMapFamily_continuousOn gap R hsub
  resolvent_identity := by
    intro lambda mu hlambda hmu
    rw [belowGapContinuousLinearMapFamily_of_lt gap R hlambda,
      belowGapContinuousLinearMapFamily_of_lt gap R hmu]
    exact hidentity hlambda hmu
  resolvent_norm_le := by
    intro lambda hlambda
    rw [belowGapContinuousLinearMapFamily_of_lt gap R hlambda]
    exact hnorm hlambda

/-- The normalized local perturbation is strictly contractive throughout the
full distance-to-gap ball. -/
theorem perturb_norm_lt_one_of_norm_sub_lt
    (D : ContinuousLinearMapOpenResolventNormBoundData E)
    {lambda mu : ℝ} (hlambda : lambda < D.gap)
    (hdist : ‖mu - lambda‖ < D.gap - lambda) :
    ‖(mu - lambda) • D.resolvent lambda‖ < 1 := by
  have hgap : 0 < D.gap - lambda := sub_pos.mpr hlambda
  calc
    ‖(mu - lambda) • D.resolvent lambda‖ ≤
        ‖mu - lambda‖ * ‖D.resolvent lambda‖ :=
      ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ ‖mu - lambda‖ * (D.gap - lambda)⁻¹ :=
      mul_le_mul_of_nonneg_left (D.resolvent_norm_le hlambda)
        (norm_nonneg _)
    _ < (D.gap - lambda) * (D.gap - lambda)⁻¹ :=
      mul_lt_mul_of_pos_right hdist (inv_pos.mpr hgap)
    _ = 1 := mul_inv_cancel₀ (ne_of_gt hgap)

/-- Exact local inverse representation obtained only from the resolvent
identity; no commutativity assumption is used. -/
theorem eq_inverse_one_sub_mul
    (D : ContinuousLinearMapOpenResolventNormBoundData E)
    {lambda mu : ℝ} (hlambda : lambda < D.gap)
    (hmu : mu < D.gap)
    (hsmall : ‖(mu - lambda) • D.resolvent lambda‖ < 1) :
    D.resolvent mu =
      Ring.inverse (1 - (mu - lambda) • D.resolvent lambda) *
        D.resolvent lambda := by
  let Rlambda := D.resolvent lambda
  let Rmu := D.resolvent mu
  let perturb : E →L[ℝ] E := (mu - lambda) • Rlambda
  change Rmu = Ring.inverse (1 - perturb) * Rlambda
  have hid : Rlambda - Rmu =
      (lambda - mu) • (Rlambda * Rmu) := by
    simpa [Rlambda, Rmu, ContinuousLinearMap.mul_def] using
      D.resolvent_identity hlambda hmu
  have hid' : Rmu - (mu - lambda) • (Rlambda * Rmu) = Rlambda := by
    rw [sub_eq_add_neg]
    have hneg :
        -((mu - lambda) • (Rlambda * Rmu)) =
          (lambda - mu) • (Rlambda * Rmu) := by module
    rw [hneg, ← hid]
    abel
  have hmul : (1 - perturb) * Rmu = Rlambda := by
    apply ContinuousLinearMap.ext
    intro y
    have h := congrArg (fun A : E →L[ℝ] E => A y) hid'
    simpa [perturb, ContinuousLinearMap.mul_def] using h
  rw [NormedRing.inverse_one_sub perturb hsmall]
  let u := Units.oneSub perturb hsmall
  change Rmu = (↑u⁻¹ : E →L[ℝ] E) * Rlambda
  symm
  calc
    (↑u⁻¹ : E →L[ℝ] E) * Rlambda =
        (↑u⁻¹ : E →L[ℝ] E) * ((1 - perturb) * Rmu) := by rw [hmul]
    _ = (↑u⁻¹ : E →L[ℝ] E) * ((↑u : E →L[ℝ] E) * Rmu) := by
      simp [u]
    _ = Rmu := by
      rw [← mul_assoc]
      simp

/-- Exact finite ordered Neumann expansion with its noncommutative remainder. -/
theorem neumann_nth_order_of_norm_sub_lt
    (D : ContinuousLinearMapOpenResolventNormBoundData E)
    (N : ℕ) {lambda mu : ℝ} (hlambda : lambda < D.gap)
    (hdist : ‖mu - lambda‖ < D.gap - lambda) :
    D.resolvent mu =
      (∑ i ∈ Finset.range N,
          ((mu - lambda) • D.resolvent lambda) ^ i) *
        D.resolvent lambda +
      ((mu - lambda) • D.resolvent lambda) ^ N *
        D.resolvent mu := by
  have hmu : mu < D.gap := by
    have hle : mu - lambda ≤ ‖mu - lambda‖ := by
      simpa [Real.norm_eq_abs] using le_abs_self (mu - lambda)
    linarith
  let Rlambda := D.resolvent lambda
  let Rmu := D.resolvent mu
  let perturb : E →L[ℝ] E := (mu - lambda) • Rlambda
  change Rmu =
    (∑ i ∈ Finset.range N, perturb ^ i) * Rlambda + perturb ^ N * Rmu
  have hsmall : ‖perturb‖ < 1 := by
    simpa [perturb, Rlambda] using
      D.perturb_norm_lt_one_of_norm_sub_lt hlambda hdist
  have hlocal : Rmu = Ring.inverse (1 - perturb) * Rlambda := by
    simpa [perturb, Rlambda, Rmu] using
      D.eq_inverse_one_sub_mul hlambda hmu hsmall
  calc
    Rmu = Ring.inverse (1 - perturb) * Rlambda := hlocal
    _ = ((∑ i ∈ Finset.range N, perturb ^ i) +
          perturb ^ N * Ring.inverse (1 - perturb)) * Rlambda := by
      exact congrArg (fun A : E →L[ℝ] E => A * Rlambda)
        (NormedRing.inverse_one_sub_nth_order' N hsmall)
    _ = (∑ i ∈ Finset.range N, perturb ^ i) * Rlambda +
        perturb ^ N * (Ring.inverse (1 - perturb) * Rlambda) := by
      noncomm_ring
    _ = (∑ i ∈ Finset.range N, perturb ^ i) * Rlambda +
        perturb ^ N * Rmu := by rw [← hlocal]

/-- Factorial Taylor coefficients coincide exactly with the ordered finite
Neumann partial sum. -/
theorem taylorPartialSum_eq_neumann
    (D : ContinuousLinearMapOpenResolventNormBoundData E)
    (N : ℕ) {lambda mu : ℝ} (hlambda : lambda < D.gap) :
    continuousLinearMapTaylorPartialSum D.resolvent lambda mu N =
      (∑ i ∈ Finset.range N,
          ((mu - lambda) • D.resolvent lambda) ^ i) *
        D.resolvent lambda := by
  unfold continuousLinearMapTaylorPartialSum
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  rw [D.iteratedDeriv k hlambda]
  have hfactorial : (k.factorial : ℝ) ≠ 0 := by positivity
  have hscalar :
      (mu - lambda) ^ k * (k.factorial : ℝ)⁻¹ *
          (k.factorial : ℝ) =
        (mu - lambda) ^ k := by
    rw [mul_assoc, inv_mul_cancel₀ hfactorial, mul_one]
  rw [smul_smul, hscalar, smul_pow, Algebra.smul_mul_assoc]
  simp only [ContinuousLinearMap.mul_def, pow_succ]

/-- Closed-ball geometric operator-norm remainder estimate for every
norm-bounded open resolvent. -/
theorem sub_taylorPartialSum_norm_le_closedBall
    (D : ContinuousLinearMapOpenResolventNormBoundData E)
    (N : ℕ) {lambda r mu : ℝ} (hlambda : lambda < D.gap)
    (hr0 : 0 ≤ r) (hrlt : r < D.gap - lambda)
    (hmu : ‖mu - lambda‖ ≤ r) :
    ‖D.resolvent mu -
        continuousLinearMapTaylorPartialSum D.resolvent lambda mu N‖ ≤
      (r * (D.gap - lambda)⁻¹) ^ N *
        (D.gap - lambda - r)⁻¹ := by
  have hdist : ‖mu - lambda‖ < D.gap - lambda :=
    lt_of_le_of_lt hmu hrlt
  have hmuGap : mu < D.gap := by
    have hle : mu - lambda ≤ ‖mu - lambda‖ := by
      simpa [Real.norm_eq_abs] using le_abs_self (mu - lambda)
    linarith
  rw [D.taylorPartialSum_eq_neumann N hlambda]
  have hExpansion := D.neumann_nth_order_of_norm_sub_lt N hlambda hdist
  have hRemainder :
      D.resolvent mu -
          (∑ i ∈ Finset.range N,
              ((mu - lambda) • D.resolvent lambda) ^ i) *
            D.resolvent lambda =
        ((mu - lambda) • D.resolvent lambda) ^ N *
          D.resolvent mu := by
    calc
      D.resolvent mu -
          (∑ i ∈ Finset.range N,
              ((mu - lambda) • D.resolvent lambda) ^ i) *
            D.resolvent lambda =
        ((∑ i ∈ Finset.range N,
              ((mu - lambda) • D.resolvent lambda) ^ i) *
            D.resolvent lambda +
          ((mu - lambda) • D.resolvent lambda) ^ N *
            D.resolvent mu) -
          (∑ i ∈ Finset.range N,
              ((mu - lambda) • D.resolvent lambda) ^ i) *
            D.resolvent lambda :=
        congrArg (fun A : E →L[ℝ] E =>
          A - (∑ i ∈ Finset.range N,
              ((mu - lambda) • D.resolvent lambda) ^ i) *
            D.resolvent lambda) hExpansion
      _ = ((mu - lambda) • D.resolvent lambda) ^ N *
          D.resolvent mu := by abel
  rw [hRemainder]
  have hRlambda := D.resolvent_norm_le hlambda
  have hRmu := D.resolvent_norm_le hmuGap
  have hPerturb :
      ‖(mu - lambda) • D.resolvent lambda‖ ≤
        r * (D.gap - lambda)⁻¹ := by
    calc
      ‖(mu - lambda) • D.resolvent lambda‖ ≤
          ‖mu - lambda‖ * ‖D.resolvent lambda‖ :=
        ContinuousLinearMap.opNorm_smul_le _ _
      _ ≤ r * ‖D.resolvent lambda‖ :=
        mul_le_mul_of_nonneg_right hmu (norm_nonneg _)
      _ ≤ r * (D.gap - lambda)⁻¹ :=
        mul_le_mul_of_nonneg_left hRlambda hr0
  have hMargin : D.gap - lambda - r ≤ D.gap - mu := by
    have hle : mu - lambda ≤ r := by
      exact le_trans (by
        simpa [Real.norm_eq_abs] using le_abs_self (mu - lambda)) hmu
    linarith
  have hInv : (D.gap - mu)⁻¹ ≤ (D.gap - lambda - r)⁻¹ := by
    have hMarginPos : 0 < D.gap - lambda - r := sub_pos.mpr hrlt
    simpa only [one_div] using
      one_div_le_one_div_of_le hMarginPos hMargin
  cases N with
  | zero =>
      simpa only [pow_zero, one_mul] using le_trans hRmu hInv
  | succ N =>
      let perturb : E →L[ℝ] E :=
        (mu - lambda) • D.resolvent lambda
      let q : ℝ := r * (D.gap - lambda)⁻¹
      have hPerturb' : ‖perturb‖ ≤ q := by
        simpa [perturb, q] using hPerturb
      have hq0 : 0 ≤ q := by
        exact mul_nonneg hr0
          (inv_nonneg.mpr (sub_pos.mpr hlambda).le)
      have hPow : ‖perturb‖ ^ (N + 1) ≤ q ^ (N + 1) :=
        pow_le_pow_left₀ (norm_nonneg perturb) hPerturb' (N + 1)
      change ‖perturb ^ (N + 1) * D.resolvent mu‖ ≤
        q ^ (N + 1) * (D.gap - lambda - r)⁻¹
      calc
        ‖perturb ^ (N + 1) * D.resolvent mu‖ ≤
            ‖perturb ^ (N + 1)‖ * ‖D.resolvent mu‖ := by
          simpa only [ContinuousLinearMap.mul_def] using
            (perturb ^ (N + 1)).opNorm_comp_le (D.resolvent mu)
        _ ≤ ‖perturb‖ ^ (N + 1) * ‖D.resolvent mu‖ :=
          mul_le_mul_of_nonneg_right
            (norm_pow_le' perturb (by omega)) (norm_nonneg _)
        _ ≤ q ^ (N + 1) * ‖D.resolvent mu‖ :=
          mul_le_mul_of_nonneg_right hPow (norm_nonneg _)
        _ ≤ q ^ (N + 1) * (D.gap - mu)⁻¹ :=
          mul_le_mul_of_nonneg_left hRmu (pow_nonneg hq0 (N + 1))
        _ ≤ q ^ (N + 1) * (D.gap - lambda - r)⁻¹ :=
          mul_le_mul_of_nonneg_left hInv (pow_nonneg hq0 (N + 1))

/-- A single worst-corner degree controls the operator-norm Taylor remainder
throughout a valid parameter box. -/
theorem taylor_operatorNorm_error_lt_parameterBox_of_worstCorner
    (D : ContinuousLinearMapOpenResolventNormBoundData E)
    {deltaMin lambdaMax rMax epsilonMin : ℝ}
    (hdelta : deltaMin ≤ D.gap)
    (hlambdaMax : lambdaMax < deltaMin)
    (hrMax0 : 0 ≤ rMax)
    (hrMaxlt : rMax < deltaMin - lambdaMax)
    (hepsilonMin : 0 < epsilonMin)
    {lambda r epsilon : ℝ}
    (hlambda : lambda ≤ lambdaMax)
    (hr0 : 0 ≤ r) (hr : r ≤ rMax)
    (hepsilon : epsilonMin ≤ epsilon)
    {N : ℕ}
    (hN : resolventTaylorClosedBall_parameterBoxWorstCornerSharpTruncationOrder
      deltaMin lambdaMax rMax epsilonMin ≤ N)
    (mu : ℝ) (hmu : ‖mu - lambda‖ ≤ r) :
    ‖D.resolvent mu -
        continuousLinearMapTaylorPartialSum D.resolvent lambda mu N‖ <
      epsilon := by
  have hlambdaGap : lambda < D.gap := by linarith
  have hrlt : r < D.gap - lambda := by linarith
  have hepsilonPos : 0 < epsilon := lt_of_lt_of_le hepsilonMin hepsilon
  have hsharp :
      resolventTaylorClosedBall_sharpTruncationOrder
          D.gap lambda r epsilon ≤ N :=
    le_trans
      (resolventTaylorClosedBall_sharpTruncationOrder_le_parameterBoxWorstCorner
        hdelta hlambda hlambdaMax hr0 hr hrMaxlt hepsilonMin hepsilon)
      hN
  have hbound := D.sub_taylorPartialSum_norm_le_closedBall
    N hlambdaGap hr0 hrlt hmu
  have henvelope :
      (r * (D.gap - lambda)⁻¹) ^ N *
        (D.gap - lambda - r)⁻¹ < epsilon :=
    (resolventTaylorClosedBall_sharpTruncationOrder_le_iff
      hlambdaGap hr0 hrlt hepsilonPos N).1 hsharp
  exact lt_of_le_of_lt hbound henvelope

/-- The same certificate at the exact worst-corner sharp degree. -/
theorem taylor_operatorNorm_error_lt_parameterBox_at_worstCorner
    (D : ContinuousLinearMapOpenResolventNormBoundData E)
    {deltaMin lambdaMax rMax epsilonMin : ℝ}
    (hdelta : deltaMin ≤ D.gap)
    (hlambdaMax : lambdaMax < deltaMin)
    (hrMax0 : 0 ≤ rMax)
    (hrMaxlt : rMax < deltaMin - lambdaMax)
    (hepsilonMin : 0 < epsilonMin)
    {lambda r epsilon : ℝ}
    (hlambda : lambda ≤ lambdaMax)
    (hr0 : 0 ≤ r) (hr : r ≤ rMax)
    (hepsilon : epsilonMin ≤ epsilon)
    (mu : ℝ) (hmu : ‖mu - lambda‖ ≤ r) :
    ‖D.resolvent mu -
        continuousLinearMapTaylorPartialSum D.resolvent lambda mu
          (resolventTaylorClosedBall_parameterBoxWorstCornerSharpTruncationOrder
            deltaMin lambdaMax rMax epsilonMin)‖ < epsilon := by
  exact D.taylor_operatorNorm_error_lt_parameterBox_of_worstCorner
    hdelta hlambdaMax hrMax0 hrMaxlt hepsilonMin hlambda hr0 hr
    hepsilon le_rfl mu hmu

end ContinuousLinearMapOpenResolventNormBoundData

namespace ContinuousLinearMapOpenTaylorStrongLimitData

variable {α E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Every fixed finite Taylor partial sum converges strongly along the indexing
filter. -/
theorem taylorPartialSum_tendsto_apply
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (N : ℕ) {lambda : ℝ} (hlambda : lambda < gap)
    (mu : ℝ) (x : E) :
    Tendsto
      (fun a =>
        (continuousLinearMapTaylorPartialSum (F a) lambda mu N) x)
      l
      (𝓝 ((continuousLinearMapTaylorPartialSum
        S.limitResolvent lambda mu N) x)) := by
  unfold continuousLinearMapTaylorPartialSum
  have hsum := tendsto_finset_sum (Finset.range N)
    (fun k hk => S.taylorTerm_tendsto_apply k hlambda mu x)
  simpa only [Finset.sum_apply] using hsum

/-- Consequently the Taylor remainder applied to every fixed vector converges
to the corresponding remainder of the limit resolvent. -/
theorem taylorRemainder_tendsto_apply
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (N : ℕ) {lambda mu : ℝ} (hlambda : lambda < gap)
    (hmu : mu < gap) (x : E) :
    Tendsto
      (fun a =>
        (F a mu -
          continuousLinearMapTaylorPartialSum (F a) lambda mu N) x)
      l
      (𝓝 ((S.limitResolvent mu -
        continuousLinearMapTaylorPartialSum
          S.limitResolvent lambda mu N) x)) := by
  exact (S.value_tendsto_apply hmu x).sub
    (S.taylorPartialSum_tendsto_apply N hlambda mu x)

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
