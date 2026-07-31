import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorJointStrongLimit
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 4000000

namespace ContinuousLinearMapOpenResolventNormBoundData

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [CompleteSpace E]

/-- On every closed subgap half-line, a norm-bounded open resolvent has one
uniform operator-norm Lipschitz constant. -/
theorem resolvent_sub_norm_le_on_Iic
    (D : ContinuousLinearMapOpenResolventNormBoundData E)
    {u lambda mu : ℝ} (hu : u < D.gap)
    (hlambda : lambda ≤ u) (hmu : mu ≤ u) :
    ‖D.resolvent lambda - D.resolvent mu‖ ≤
      |lambda - mu| *
        ((D.gap - u)⁻¹ * (D.gap - u)⁻¹) := by
  have hlambdaGap : lambda < D.gap := lt_of_le_of_lt hlambda hu
  have hmuGap : mu < D.gap := lt_of_le_of_lt hmu hu
  have hmargin : 0 < D.gap - u := sub_pos.mpr hu
  have hlambdaInv :
      (D.gap - lambda)⁻¹ ≤ (D.gap - u)⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le hmargin (by linarith : D.gap - u ≤ D.gap - lambda)
  have hmuInv :
      (D.gap - mu)⁻¹ ≤ (D.gap - u)⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le hmargin (by linarith : D.gap - u ≤ D.gap - mu)
  have hRlambda : ‖D.resolvent lambda‖ ≤ (D.gap - u)⁻¹ :=
    le_trans (D.resolvent_norm_le hlambdaGap) hlambdaInv
  have hRmu : ‖D.resolvent mu‖ ≤ (D.gap - u)⁻¹ :=
    le_trans (D.resolvent_norm_le hmuGap) hmuInv
  rw [D.resolvent_identity hlambdaGap hmuGap]
  calc
    ‖(lambda - mu) •
        ((D.resolvent lambda).comp (D.resolvent mu))‖ ≤
        ‖lambda - mu‖ *
          ‖(D.resolvent lambda).comp (D.resolvent mu)‖ :=
      ContinuousLinearMap.opNorm_smul_le _ _
    _ ≤ ‖lambda - mu‖ *
        (‖D.resolvent lambda‖ * ‖D.resolvent mu‖) :=
      mul_le_mul_of_nonneg_left
        ((D.resolvent lambda).opNorm_comp_le (D.resolvent mu))
        (norm_nonneg _)
    _ ≤ ‖lambda - mu‖ *
        ((D.gap - u)⁻¹ * (D.gap - u)⁻¹) := by
      gcongr
    _ = |lambda - mu| *
        ((D.gap - u)⁻¹ * (D.gap - u)⁻¹) := by
      rw [Real.norm_eq_abs]

/-- Vector-valued equicontinuity inherited from the common operator-norm
Lipschitz estimate. -/
theorem resolvent_sub_apply_norm_le_on_Iic
    (D : ContinuousLinearMapOpenResolventNormBoundData E)
    {u lambda mu : ℝ} (hu : u < D.gap)
    (hlambda : lambda ≤ u) (hmu : mu ≤ u) (x : E) :
    ‖D.resolvent lambda x - D.resolvent mu x‖ ≤
      |lambda - mu| *
        (((D.gap - u)⁻¹ * (D.gap - u)⁻¹) * ‖x‖) := by
  calc
    ‖D.resolvent lambda x - D.resolvent mu x‖ =
        ‖(D.resolvent lambda - D.resolvent mu) x‖ := by simp
    _ ≤ ‖D.resolvent lambda - D.resolvent mu‖ * ‖x‖ :=
      (D.resolvent lambda - D.resolvent mu).le_opNorm x
    _ ≤
        (|lambda - mu| *
          ((D.gap - u)⁻¹ * (D.gap - u)⁻¹)) * ‖x‖ :=
      mul_le_mul_of_nonneg_right
        (D.resolvent_sub_norm_le_on_Iic hu hlambda hmu)
        (norm_nonneg x)
    _ = |lambda - mu| *
        (((D.gap - u)⁻¹ * (D.gap - u)⁻¹) * ‖x‖) := by ring

end ContinuousLinearMapOpenResolventNormBoundData

namespace ContinuousLinearMapOpenResolventNormBoundFamilyData

variable {α β E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- One cofinal degree net makes the Taylor remainder operator-norm small
simultaneously at every point of a valid parameter box and uniformly over an
arbitrary member-selection net. -/
theorem taylorRemainder_uniform_parameterBox_eventually_of_tendsto_degree
    {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    {m : Filter β} (a : β → α) (degree : β → ℕ)
    (hdegree : Tendsto degree m atTop)
    {deltaMin lambdaMax rMax : ℝ}
    (hdelta : deltaMin ≤ gap)
    (hlambdaMax : lambdaMax < deltaMin)
    (hrMax0 : 0 ≤ rMax)
    (hrMaxlt : rMax < deltaMin - lambdaMax) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ b in m, ∀ lambda r mu : ℝ,
        lambda ≤ lambdaMax →
        0 ≤ r → r ≤ rMax → ‖mu - lambda‖ ≤ r →
        ‖F (a b) mu -
          continuousLinearMapTaylorPartialSum
            (F (a b)) lambda mu (degree b)‖ < epsilon := by
  intro epsilon hepsilon
  let N0 :=
    resolventTaylorClosedBall_parameterBoxWorstCornerSharpTruncationOrder
      deltaMin lambdaMax rMax epsilon
  have hEventually : ∀ᶠ b in m, N0 ≤ degree b :=
    hdegree.eventually (Filter.eventually_ge_atTop N0)
  filter_upwards [hEventually] with b hN
  intro lambda r mu hlambda hr0 hr hmu
  have hdelta' : deltaMin ≤ (B.normBoundData (a b)).gap := by
    rw [B.gap_eq (a b)]
    exact hdelta
  have herror :=
    (B.normBoundData (a b)).taylor_operatorNorm_error_lt_parameterBox_of_worstCorner
      (deltaMin := deltaMin) (lambdaMax := lambdaMax)
      (rMax := rMax) (epsilonMin := epsilon) (N := degree b)
      hdelta' hlambdaMax hrMax0 hrMaxlt hepsilon
      hlambda hr0 hr le_rfl hN mu hmu
  rwa [B.resolvent_eq (a b)] at herror

end ContinuousLinearMapOpenResolventNormBoundFamilyData

namespace ContinuousLinearMapOpenTaylorStrongLimitData

variable {α β E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Pointwise strong resolvent convergence plus the common reciprocal-gap
Lipschitz bound upgrades to uniform strong convergence on every compact subgap
parameter set. -/
theorem value_tendsto_uniformOn_compact_apply
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap)
    (hLresolvent : L.resolvent = S.limitResolvent)
    (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < gap)
    (x : E) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ mu ∈ K,
        ‖F a mu x - S.limitResolvent mu x‖ < epsilon := by
  intro epsilon hepsilon
  let q : ℝ := (gap - u)⁻¹ * (gap - u)⁻¹
  let c : ℝ := q * ‖x‖
  have hmargin : 0 < gap - u := sub_pos.mpr hu
  have hq0 : 0 ≤ q := by
    exact mul_nonneg (inv_nonneg.mpr hmargin.le) (inv_nonneg.mpr hmargin.le)
  have hc0 : 0 ≤ c := mul_nonneg hq0 (norm_nonneg x)
  let eta : ℝ := epsilon / (3 * (c + 1))
  have hc1 : 0 < c + 1 := by linarith
  have heta : 0 < eta := div_pos hepsilon (mul_pos (by norm_num) hc1)
  have hetaC : eta * c < epsilon / 3 := by
    have hcLt : c < c + 1 := lt_add_one c
    have hmul := mul_lt_mul_of_pos_left hcLt heta
    calc
      eta * c < eta * (c + 1) := by simpa [mul_comm] using hmul
      _ = epsilon / 3 := by
        dsimp [eta]
        field_simp [ne_of_gt hc1]
        <;> ring
  let U : K → Set ℝ := fun y => Metric.ball y.1 eta
  have hUopen : ∀ y : K, IsOpen (U y) := fun y => Metric.isOpen_ball
  have hcover : K ⊆ ⋃ y : K, U y := by
    intro mu hmu
    apply mem_iUnion.2
    exact ⟨⟨mu, hmu⟩, Metric.mem_ball_self heta⟩
  obtain ⟨t, ht⟩ := hKcompact.elim_finite_subcover U hUopen hcover
  have hcenter : ∀ y : K,
      ∀ᶠ a in l,
        ‖F a y.1 x - S.limitResolvent y.1 x‖ < epsilon / 3 := by
    intro y
    have hyGap : y.1 < gap := lt_of_le_of_lt (hKu y.2) hu
    have hy := S.value_tendsto_apply hyGap x
    rw [Metric.tendsto_nhds] at hy
    have hyEventually := hy (epsilon / 3) (div_pos hepsilon (by norm_num))
    simpa [dist_eq_norm] using hyEventually
  have hfinite : ∀ᶠ a in l, ∀ y ∈ t,
      ‖F a y.1 x - S.limitResolvent y.1 x‖ < epsilon / 3 := by
    classical
    induction t using Finset.induction_on with
    | empty => simp
    | @insert y t hy ih =>
        filter_upwards [hcenter y, ih] with a hay hat
        intro z hz
        simp only [Finset.mem_insert] at hz
        rcases hz with hzy | hzt
        · simpa [hzy] using hay
        · exact hat z hzt
  filter_upwards [hfinite] with a ha
  intro mu hmuK
  have hmuCover := ht hmuK
  rcases mem_iUnion.1 hmuCover with ⟨y, hyCover⟩
  rcases mem_iUnion.1 hyCover with ⟨hyt, hmuBall⟩
  have hmuU : mu ≤ u := hKu hmuK
  have hyU : y.1 ≤ u := hKu y.2
  have hdist : |mu - y.1| < eta := by
    simpa [U, Real.dist_eq] using hmuBall
  have hFamilyGap : u < (B.normBoundData a).gap := by
    rw [B.gap_eq a]
    exact hu
  have hFamilyBound :=
    (B.normBoundData a).resolvent_sub_apply_norm_le_on_Iic
      hFamilyGap hmuU hyU x
  rw [B.gap_eq a, B.resolvent_eq a] at hFamilyBound
  have hFamilySmall : ‖F a mu x - F a y.1 x‖ < epsilon / 3 := by
    refine lt_of_le_of_lt hFamilyBound ?_
    calc
      |mu - y.1| * c ≤ eta * c :=
        mul_le_mul_of_nonneg_right (le_of_lt hdist) hc0
      _ < epsilon / 3 := hetaC
  have hLimitGap : u < L.gap := by rw [hLgap]; exact hu
  have hLimitBound :=
    L.resolvent_sub_apply_norm_le_on_Iic hLimitGap hyU hmuU x
  rw [hLgap, hLresolvent] at hLimitBound
  have hLimitSmall :
      ‖S.limitResolvent y.1 x - S.limitResolvent mu x‖ < epsilon / 3 := by
    refine lt_of_le_of_lt hLimitBound ?_
    calc
      |y.1 - mu| * c = |mu - y.1| * c := by rw [abs_sub_comm]
      _ ≤ eta * c := mul_le_mul_of_nonneg_right (le_of_lt hdist) hc0
      _ < epsilon / 3 := hetaC
  have hdecomp :
      F a mu x - S.limitResolvent mu x =
        (F a mu x - F a y.1 x) +
          (F a y.1 x - S.limitResolvent y.1 x) +
            (S.limitResolvent y.1 x - S.limitResolvent mu x) := by
    abel
  rw [hdecomp]
  calc
    ‖(F a mu x - F a y.1 x) +
        (F a y.1 x - S.limitResolvent y.1 x) +
          (S.limitResolvent y.1 x - S.limitResolvent mu x)‖ ≤
      ‖F a mu x - F a y.1 x‖ +
        ‖F a y.1 x - S.limitResolvent y.1 x‖ +
          ‖S.limitResolvent y.1 x - S.limitResolvent mu x‖ := by
      exact le_trans (norm_add_le _ _)
        (add_le_add_right (norm_add_le _ _) _)
    _ < epsilon := by
      have hcenterSmall := ha y hyt
      linarith

/-- Joint Taylor/time convergence is uniform on the full closed parameter box.
The two rates remain independent; compactness is used only to uniformize the
actual strong resolvent limit in the target spectral parameter. -/
theorem taylorPartialSum_tendsto_limitResolvent_apply_uniform_parameterBox_of_joint
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap)
    (hLresolvent : L.resolvent = S.limitResolvent)
    {m : Filter β} (a : β → α) (degree : β → ℕ)
    (ha : Tendsto a m l) (hdegree : Tendsto degree m atTop)
    {deltaMin lambdaMin lambdaMax rMax : ℝ}
    (hdelta : deltaMin ≤ gap)
    (hlambdaBounds : lambdaMin ≤ lambdaMax)
    (hlambdaMax : lambdaMax < deltaMin)
    (hrMax0 : 0 ≤ rMax)
    (hrMaxlt : rMax < deltaMin - lambdaMax)
    (x : E) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ b in m, ∀ lambda r mu : ℝ,
        lambdaMin ≤ lambda → lambda ≤ lambdaMax →
        0 ≤ r → r ≤ rMax → ‖mu - lambda‖ ≤ r →
        ‖(continuousLinearMapTaylorPartialSum
            (F (a b)) lambda mu (degree b)) x -
          S.limitResolvent mu x‖ < epsilon := by
  intro epsilon hepsilon
  let K : Set ℝ := Set.Icc (lambdaMin - rMax) (lambdaMax + rMax)
  have hUpperGap : lambdaMax + rMax < gap := by linarith
  have hUniformValueL :=
    S.value_tendsto_uniformOn_compact_apply B L hLgap hLresolvent
      K isCompact_Icc (u := lambdaMax + rMax)
      (fun mu hmu => hmu.2) hUpperGap x
      (epsilon / 2) (half_pos hepsilon)
  have hUniformValue :
      ∀ᶠ b in m, ∀ mu ∈ K,
        ‖F (a b) mu x - S.limitResolvent mu x‖ < epsilon / 2 :=
    ha.eventually hUniformValueL
  let opEpsilon : ℝ := epsilon / (2 * (‖x‖ + 1))
  have hx1 : 0 < ‖x‖ + 1 := by positivity
  have hopEpsilon : 0 < opEpsilon :=
    div_pos hepsilon (mul_pos (by norm_num) hx1)
  have hUniformRemainder :=
    B.taylorRemainder_uniform_parameterBox_eventually_of_tendsto_degree
      a degree hdegree hdelta hlambdaMax hrMax0 hrMaxlt
      opEpsilon hopEpsilon
  filter_upwards [hUniformValue, hUniformRemainder] with b hValue hRemainder
  intro lambda r mu hlambdaMin hlambdaMax' hr0 hr hmu
  have habs : |mu - lambda| ≤ r := by
    simpa [Real.norm_eq_abs] using hmu
  have hdiff := abs_le.mp habs
  have hmuK : mu ∈ K := by
    constructor <;> dsimp [K] <;> linarith
  have hValueSmall := hValue mu hmuK
  have hOpSmall :=
    hRemainder lambda r mu hlambdaMax' hr0 hr hmu
  have hApplySmall :
      ‖(continuousLinearMapTaylorPartialSum
          (F (a b)) lambda mu (degree b) - F (a b) mu) x‖ < epsilon / 2 := by
    have hApplyLe :
        ‖(continuousLinearMapTaylorPartialSum
            (F (a b)) lambda mu (degree b) - F (a b) mu) x‖ ≤
          ‖F (a b) mu -
            continuousLinearMapTaylorPartialSum
              (F (a b)) lambda mu (degree b)‖ * ‖x‖ := by
      calc
        ‖(continuousLinearMapTaylorPartialSum
            (F (a b)) lambda mu (degree b) - F (a b) mu) x‖ =
          ‖(F (a b) mu -
            continuousLinearMapTaylorPartialSum
              (F (a b)) lambda mu (degree b)) x‖ := by
            rw [show continuousLinearMapTaylorPartialSum
                (F (a b)) lambda mu (degree b) - F (a b) mu =
              -(F (a b) mu -
                continuousLinearMapTaylorPartialSum
                  (F (a b)) lambda mu (degree b)) by abel]
            simp
        _ ≤ ‖F (a b) mu -
              continuousLinearMapTaylorPartialSum
                (F (a b)) lambda mu (degree b)‖ * ‖x‖ :=
          (F (a b) mu -
            continuousLinearMapTaylorPartialSum
              (F (a b)) lambda mu (degree b)).le_opNorm x
    refine lt_of_le_of_lt hApplyLe ?_
    calc
      ‖F (a b) mu -
          continuousLinearMapTaylorPartialSum
            (F (a b)) lambda mu (degree b)‖ * ‖x‖ <
        opEpsilon * ‖x‖ :=
          mul_lt_mul_of_pos_right hOpSmall (by positivity)
      _ < epsilon / 2 := by
        dsimp [opEpsilon]
        have hxlt : ‖x‖ < ‖x‖ + 1 := lt_add_one _
        have hratio : ‖x‖ / (‖x‖ + 1) < 1 :=
          (div_lt_one hx1).2 hxlt
        calc
          epsilon / (2 * (‖x‖ + 1)) * ‖x‖ =
              (epsilon / 2) * (‖x‖ / (‖x‖ + 1)) := by field_simp; ring
          _ < (epsilon / 2) * 1 :=
            mul_lt_mul_of_pos_left hratio (half_pos hepsilon)
          _ = epsilon / 2 := mul_one _
  have hdecomp :
      (continuousLinearMapTaylorPartialSum
          (F (a b)) lambda mu (degree b)) x -
        S.limitResolvent mu x =
      (continuousLinearMapTaylorPartialSum
          (F (a b)) lambda mu (degree b) - F (a b) mu) x +
        (F (a b) mu x - S.limitResolvent mu x) := by
    simp
  rw [hdecomp]
  exact lt_of_le_of_lt (norm_add_le _ _) (by linarith)

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
