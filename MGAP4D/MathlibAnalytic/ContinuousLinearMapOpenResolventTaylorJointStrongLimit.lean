import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorParameterBoxCertificate
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 3200000

/-- Operator-norm convergence of continuous linear maps implies pointwise
convergence on every fixed vector. -/
theorem continuousLinearMap_opNorm_tendsto_apply
    {β E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : Filter β} {A : β → E →L[ℝ] E} {L : E →L[ℝ] E}
    (hA : Tendsto A m (𝓝 L)) (x : E) :
    Tendsto (fun b => A b x) m (𝓝 (L x)) := by
  rw [Metric.tendsto_nhds] at hA ⊢
  intro epsilon hepsilon
  by_cases hx : x = 0
  · exact Filter.Eventually.of_forall (fun b => by simpa [hx] using hepsilon)
  · have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hEventually := hA (epsilon / ‖x‖) (div_pos hepsilon hxnorm)
    filter_upwards [hEventually] with b hb
    have hb' : ‖A b - L‖ < epsilon / ‖x‖ := by
      simpa [dist_eq_norm] using hb
    rw [dist_eq_norm]
    calc
      ‖A b x - L x‖ = ‖(A b - L) x‖ := by simp
      _ ≤ ‖A b - L‖ * ‖x‖ := (A b - L).le_opNorm x
      _ < (epsilon / ‖x‖) * ‖x‖ :=
        mul_lt_mul_of_pos_right hb' hxnorm
      _ = epsilon := div_mul_cancel₀ epsilon (ne_of_gt hxnorm)

/-- A family of norm-bounded open resolvents sharing one exact gap and one
operator-valued presentation. -/
structure ContinuousLinearMapOpenResolventNormBoundFamilyData
    {α E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (gap : ℝ) (F : α → ℝ → E →L[ℝ] E) where
  normBoundData : ∀ a : α,
    ContinuousLinearMapOpenResolventNormBoundData E
  gap_eq : ∀ a : α, (normBoundData a).gap = gap
  resolvent_eq : ∀ a : α, (normBoundData a).resolvent = F a

namespace ContinuousLinearMapOpenResolventNormBoundData

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [CompleteSpace E]

/-- Taylor partial sums of one norm-bounded open resolvent converge in operator
norm to the resolvent throughout every strict distance-to-gap ball. -/
theorem taylorPartialSum_tendsto_resolvent_atTop
    (D : ContinuousLinearMapOpenResolventNormBoundData E)
    {lambda r mu : ℝ}
    (hlambda : lambda < D.gap)
    (hr0 : 0 ≤ r) (hrlt : r < D.gap - lambda)
    (hmu : ‖mu - lambda‖ ≤ r) :
    Tendsto
      (fun N : ℕ =>
        continuousLinearMapTaylorPartialSum D.resolvent lambda mu N)
      atTop (𝓝 (D.resolvent mu)) := by
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  let N0 :=
    resolventTaylorClosedBall_parameterBoxWorstCornerSharpTruncationOrder
      D.gap lambda r epsilon
  filter_upwards [Filter.eventually_ge_atTop N0] with N hN
  have herror :=
    D.taylor_operatorNorm_error_lt_parameterBox_of_worstCorner
      (deltaMin := D.gap) (lambdaMax := lambda)
      (rMax := r) (epsilonMin := epsilon) (N := N)
      le_rfl hlambda hr0 hrlt hepsilon
      le_rfl hr0 le_rfl le_rfl hN mu hmu
  rw [dist_eq_norm]
  calc
    ‖continuousLinearMapTaylorPartialSum D.resolvent lambda mu N -
        D.resolvent mu‖ =
      ‖-(D.resolvent mu -
        continuousLinearMapTaylorPartialSum D.resolvent lambda mu N)‖ := by
      congr 1
      abel
    _ = ‖D.resolvent mu -
        continuousLinearMapTaylorPartialSum D.resolvent lambda mu N‖ :=
      norm_neg _
    _ < epsilon := herror

end ContinuousLinearMapOpenResolventNormBoundData

namespace ContinuousLinearMapOpenResolventNormBoundFamilyData

variable {α β E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Uniformly over an arbitrary member-selection net, every cofinal Taylor
degree net drives the operator-norm remainder to zero on a valid parameter
box. -/
theorem taylorRemainder_tendsto_zero_of_tendsto_degree
    {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    {m : Filter β} (a : β → α) (degree : β → ℕ)
    (hdegree : Tendsto degree m atTop)
    {deltaMin lambdaMax rMax : ℝ}
    (hdelta : deltaMin ≤ gap)
    (hlambdaMax : lambdaMax < deltaMin)
    (hrMax0 : 0 ≤ rMax)
    (hrMaxlt : rMax < deltaMin - lambdaMax)
    {lambda r : ℝ}
    (hlambda : lambda ≤ lambdaMax)
    (hr0 : 0 ≤ r) (hr : r ≤ rMax)
    (mu : ℝ) (hmu : ‖mu - lambda‖ ≤ r) :
    Tendsto
      (fun b =>
        F (a b) mu -
          continuousLinearMapTaylorPartialSum
            (F (a b)) lambda mu (degree b))
      m (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  let N0 :=
    resolventTaylorClosedBall_parameterBoxWorstCornerSharpTruncationOrder
      deltaMin lambdaMax rMax epsilon
  have hEventually : ∀ᶠ b in m, N0 ≤ degree b :=
    hdegree.eventually (Filter.eventually_ge_atTop N0)
  filter_upwards [hEventually] with b hN
  have hdelta' : deltaMin ≤ (B.normBoundData (a b)).gap := by
    rw [B.gap_eq (a b)]
    exact hdelta
  have herror :=
    (B.normBoundData (a b)).taylor_operatorNorm_error_lt_parameterBox_of_worstCorner
      (deltaMin := deltaMin) (lambdaMax := lambdaMax)
      (rMax := rMax) (epsilonMin := epsilon) (N := degree b)
      hdelta' hlambdaMax hrMax0 hrMaxlt hepsilon
      hlambda hr0 hr le_rfl hN mu hmu
  rw [B.resolvent_eq (a b)] at herror
  simpa [dist_eq_norm] using herror

/-- The equivalent partial-sum-minus-resolvent form of the uniform remainder
limit. -/
theorem taylorPartialSum_sub_resolvent_tendsto_zero_of_tendsto_degree
    {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    {m : Filter β} (a : β → α) (degree : β → ℕ)
    (hdegree : Tendsto degree m atTop)
    {deltaMin lambdaMax rMax : ℝ}
    (hdelta : deltaMin ≤ gap)
    (hlambdaMax : lambdaMax < deltaMin)
    (hrMax0 : 0 ≤ rMax)
    (hrMaxlt : rMax < deltaMin - lambdaMax)
    {lambda r : ℝ}
    (hlambda : lambda ≤ lambdaMax)
    (hr0 : 0 ≤ r) (hr : r ≤ rMax)
    (mu : ℝ) (hmu : ‖mu - lambda‖ ≤ r) :
    Tendsto
      (fun b =>
        continuousLinearMapTaylorPartialSum
            (F (a b)) lambda mu (degree b) -
          F (a b) mu)
      m (𝓝 0) := by
  have h := B.taylorRemainder_tendsto_zero_of_tendsto_degree
    a degree hdegree hdelta hlambdaMax hrMax0 hrMaxlt
    hlambda hr0 hr mu hmu
  simpa [neg_sub] using h.neg

end ContinuousLinearMapOpenResolventNormBoundFamilyData

namespace ContinuousLinearMapOpenTaylorStrongLimitData

variable {α β E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Joint strong convergence along any net whose member index tends to the
strong-limit filter and whose Taylor degree tends to infinity.  No relation
between the two rates is required because the Taylor remainder is uniformly
controlled over the whole resolvent family. -/
theorem taylorPartialSum_tendsto_limitResolvent_apply_of_joint
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    {m : Filter β} (a : β → α) (degree : β → ℕ)
    (ha : Tendsto a m l) (hdegree : Tendsto degree m atTop)
    {deltaMin lambdaMax rMax : ℝ}
    (hdelta : deltaMin ≤ gap)
    (hlambdaMax : lambdaMax < deltaMin)
    (hrMax0 : 0 ≤ rMax)
    (hrMaxlt : rMax < deltaMin - lambdaMax)
    {lambda r mu : ℝ}
    (hlambda : lambda ≤ lambdaMax)
    (hr0 : 0 ≤ r) (hr : r ≤ rMax)
    (hmuBall : ‖mu - lambda‖ ≤ r)
    (hmuGap : mu < gap)
    (x : E) :
    Tendsto
      (fun b =>
        (continuousLinearMapTaylorPartialSum
          (F (a b)) lambda mu (degree b)) x)
      m (𝓝 (S.limitResolvent mu x)) := by
  have hRemainderOp :=
    B.taylorRemainder_tendsto_zero_of_tendsto_degree
      a degree hdegree hdelta hlambdaMax hrMax0 hrMaxlt
      hlambda hr0 hr mu hmuBall
  have hRemainderApply :=
    continuousLinearMap_opNorm_tendsto_apply hRemainderOp x
  have hValue := (S.value_tendsto_apply hmuGap x).comp ha
  have hCombined := hValue.sub hRemainderApply
  simpa using hCombined

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
