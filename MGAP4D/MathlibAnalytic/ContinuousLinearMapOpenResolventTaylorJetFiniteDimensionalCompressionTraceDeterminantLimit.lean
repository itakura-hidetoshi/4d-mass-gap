import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorJetLocallyUniformFiniteDimensionalCompressionLimit
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- The trace of a continuous endomorphism on a finite-dimensional real normed
space, packaged as a continuous linear functional on the operator-norm space. -/
def continuousLinearMapTrace
    {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] :
    (V →L[ℝ] V) →L[ℝ] ℝ :=
  (((LinearMap.trace ℝ V).comp (ContinuousLinearMap.coeLM ℝ))).toContinuousLinearMap

@[simp]
theorem continuousLinearMapTrace_apply
    {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (A : V →L[ℝ] V) :
    continuousLinearMapTrace A = LinearMap.trace ℝ V A.toLinearMap := rfl

/-- The finite-dimensional trace is globally Lipschitz with the operator norm
of its continuous-linear-functional packaging. -/
theorem continuousLinearMapTrace_sub_abs_le
    {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (A B : V →L[ℝ] V) :
    |continuousLinearMapTrace A - continuousLinearMapTrace B| ≤
      ‖(continuousLinearMapTrace : (V →L[ℝ] V) →L[ℝ] ℝ)‖ * ‖A - B‖ := by
  have h :=
    (continuousLinearMapTrace : (V →L[ℝ] V) →L[ℝ] ℝ).le_opNorm (A - B)
  simpa [map_sub, Real.norm_eq_abs] using h

namespace ContinuousLinearMapOpenTaylorStrongLimitData

variable {α β E V : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [FiniteDimensional ℝ V]

/-- At every fixed strict-subgap spectral point, the compressed Taylor jet
converges in operator norm as an ordinary filter limit. -/
theorem iteratedDeriv_finiteDimensionalCompression_tendsto
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap)
    (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (k : ℕ) {lambda : ℝ} (hlambda : lambda < gap) :
    Tendsto
      (fun a =>
        continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k (F a) lambda))
      l
      (𝓝 (continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k S.limitResolvent lambda))) := by
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  have h :=
    S.iteratedDeriv_tendsto_uniformOn_compact_finiteDimensionalCompression
      B L hLgap hLresolvent J Q k ({lambda} : Set ℝ)
      isCompact_singleton
      (u := lambda)
      (by
        intro mu hmu
        have hEq : mu = lambda := Set.mem_singleton_iff.mp hmu
        simpa [hEq])
      hlambda epsilon hepsilon
  filter_upwards [h] with a ha
  have hAt := ha lambda (by simp)
  simpa [dist_eq_norm] using hAt

/-- The traces of all fixed compressed Taylor-jet levels converge uniformly on
every compact strict-subgap spectral set. -/
theorem iteratedDeriv_trace_finiteDimensionalCompression_tendsto_uniformOn_compact
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap)
    (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (k : ℕ) (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < gap) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ lambda ∈ K,
        |continuousLinearMapTrace
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) -
          continuousLinearMapTrace
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda))| < epsilon := by
  intro epsilon hepsilon
  let c : ℝ :=
    ‖(continuousLinearMapTrace : (V →L[ℝ] V) →L[ℝ] ℝ)‖
  let eta : ℝ := epsilon / (c + 1)
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hc1 : 0 < c + 1 := by linarith
  have heta : 0 < eta := div_pos hepsilon hc1
  have hOperator :=
    S.iteratedDeriv_tendsto_uniformOn_compact_finiteDimensionalCompression
      B L hLgap hLresolvent J Q k K hKcompact hKu hu eta heta
  filter_upwards [hOperator] with a ha
  intro lambda hlambda
  let A := continuousLinearMapCompression J Q
    (_root_.iteratedDeriv k (F a) lambda)
  let A0 := continuousLinearMapCompression J Q
    (_root_.iteratedDeriv k S.limitResolvent lambda)
  have hTrace := continuousLinearMapTrace_sub_abs_le A A0
  have hOp : ‖A - A0‖ < eta := by
    simpa [A, A0] using ha lambda hlambda
  calc
    |continuousLinearMapTrace A - continuousLinearMapTrace A0| ≤
        c * ‖A - A0‖ := by simpa [c] using hTrace
    _ ≤ (c + 1) * ‖A - A0‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ < (c + 1) * eta := mul_lt_mul_of_pos_left hOp hc1
    _ = epsilon := by
      dsimp [eta]
      field_simp [ne_of_gt hc1]

/-- A complete finite Taylor jet has uniformly convergent compressed traces on
each compact strict-subgap set. -/
theorem iteratedDeriv_trace_finiteDimensionalCompression_tendsto_uniformOn_compact_jet
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap)
    (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (order : ℕ) (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < gap) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ k ≤ order, ∀ lambda ∈ K,
        |continuousLinearMapTrace
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) -
          continuousLinearMapTrace
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda))| < epsilon := by
  intro epsilon hepsilon
  let c : ℝ :=
    ‖(continuousLinearMapTrace : (V →L[ℝ] V) →L[ℝ] ℝ)‖
  let eta : ℝ := epsilon / (c + 1)
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hc1 : 0 < c + 1 := by linarith
  have heta : 0 < eta := div_pos hepsilon hc1
  have hOperator :=
    S.iteratedDeriv_tendsto_uniformOn_compact_finiteDimensionalCompression_jet
      B L hLgap hLresolvent J Q order K hKcompact hKu hu eta heta
  filter_upwards [hOperator] with a ha
  intro k hk lambda hlambda
  let A := continuousLinearMapCompression J Q
    (_root_.iteratedDeriv k (F a) lambda)
  let A0 := continuousLinearMapCompression J Q
    (_root_.iteratedDeriv k S.limitResolvent lambda)
  have hTrace := continuousLinearMapTrace_sub_abs_le A A0
  have hOp : ‖A - A0‖ < eta := by
    simpa [A, A0] using ha k hk lambda hlambda
  calc
    |continuousLinearMapTrace A - continuousLinearMapTrace A0| ≤
        c * ‖A - A0‖ := by simpa [c] using hTrace
    _ ≤ (c + 1) * ‖A - A0‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ < (c + 1) * eta := mul_lt_mul_of_pos_left hOp hc1
    _ = epsilon := by
      dsimp [eta]
      field_simp [ne_of_gt hc1]

/-- At a fixed strict-subgap point, determinants of compressed Taylor jets
converge by continuity of determinant on finite-dimensional operator space. -/
theorem iteratedDeriv_det_finiteDimensionalCompression_tendsto
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap)
    (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (k : ℕ) {lambda : ℝ} (hlambda : lambda < gap) :
    Tendsto
      (fun a =>
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k (F a) lambda)).det)
      l
      (𝓝 ((continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k S.limitResolvent lambda)).det)) := by
  have hCompression :=
    S.iteratedDeriv_finiteDimensionalCompression_tendsto
      B L hLgap hLresolvent J Q k hlambda
  exact (ContinuousLinearMap.continuous_det.tendsto _).comp hCompression

/-- Traces of compressed finite-time Taylor partial sums converge uniformly on
the complete closed Taylor parameter box, with independent time and degree
rates. -/
theorem taylorPartialSum_trace_finiteDimensionalCompression_tendsto_limitResolvent_uniform_parameterBox_of_joint
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap)
    (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    {m : Filter β} (a : β → α) (degree : β → ℕ)
    (ha : Tendsto a m l) (hdegree : Tendsto degree m atTop)
    {deltaMin lambdaMin lambdaMax rMax : ℝ}
    (hdelta : deltaMin ≤ gap)
    (hlambdaBounds : lambdaMin ≤ lambdaMax)
    (hlambdaMax : lambdaMax < deltaMin)
    (hrMax0 : 0 ≤ rMax)
    (hrMaxlt : rMax < deltaMin - lambdaMax) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ b in m, ∀ lambda r mu : ℝ,
        lambdaMin ≤ lambda → lambda ≤ lambdaMax →
        0 ≤ r → r ≤ rMax → ‖mu - lambda‖ ≤ r →
        |continuousLinearMapTrace
            (continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (F (a b)) lambda mu (degree b))) -
          continuousLinearMapTrace
            (continuousLinearMapCompression J Q
              (S.limitResolvent mu))| < epsilon := by
  intro epsilon hepsilon
  let c : ℝ :=
    ‖(continuousLinearMapTrace : (V →L[ℝ] V) →L[ℝ] ℝ)‖
  let eta : ℝ := epsilon / (c + 1)
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hc1 : 0 < c + 1 := by linarith
  have heta : 0 < eta := div_pos hepsilon hc1
  have hOperator :=
    S.taylorPartialSum_tendsto_limitResolvent_finiteDimensionalCompression_uniform_parameterBox_of_joint
      B L hLgap hLresolvent J Q a degree ha hdegree
      hdelta hlambdaBounds hlambdaMax hrMax0 hrMaxlt eta heta
  filter_upwards [hOperator] with b hb
  intro lambda r mu hlambdaMin hlambdaMax' hr0 hr hmu
  let A := continuousLinearMapCompression J Q
    (continuousLinearMapTaylorPartialSum
      (F (a b)) lambda mu (degree b))
  let A0 := continuousLinearMapCompression J Q (S.limitResolvent mu)
  have hTrace := continuousLinearMapTrace_sub_abs_le A A0
  have hOp : ‖A - A0‖ < eta := by
    simpa [A, A0] using
      hb lambda r mu hlambdaMin hlambdaMax' hr0 hr hmu
  calc
    |continuousLinearMapTrace A - continuousLinearMapTrace A0| ≤
        c * ‖A - A0‖ := by simpa [c] using hTrace
    _ ≤ (c + 1) * ‖A - A0‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ < (c + 1) * eta := mul_lt_mul_of_pos_left hOp hc1
    _ = epsilon := by
      dsimp [eta]
      field_simp [ne_of_gt hc1]

/-- At every fixed valid Taylor-box point, compressed Taylor partial sums
converge in operator norm as an ordinary joint-net limit. -/
theorem taylorPartialSum_finiteDimensionalCompression_tendsto_limitResolvent_of_joint
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap)
    (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    {m : Filter β} (a : β → α) (degree : β → ℕ)
    (ha : Tendsto a m l) (hdegree : Tendsto degree m atTop)
    {deltaMin lambdaMin lambdaMax rMax lambda r mu : ℝ}
    (hdelta : deltaMin ≤ gap)
    (hlambdaBounds : lambdaMin ≤ lambdaMax)
    (hlambdaMax : lambdaMax < deltaMin)
    (hrMax0 : 0 ≤ rMax)
    (hrMaxlt : rMax < deltaMin - lambdaMax)
    (hlambdaMin : lambdaMin ≤ lambda)
    (hlambdaMax' : lambda ≤ lambdaMax)
    (hr0 : 0 ≤ r) (hr : r ≤ rMax)
    (hmu : ‖mu - lambda‖ ≤ r) :
    Tendsto
      (fun b =>
        continuousLinearMapCompression J Q
          (continuousLinearMapTaylorPartialSum
            (F (a b)) lambda mu (degree b)))
      m
      (𝓝 (continuousLinearMapCompression J Q
        (S.limitResolvent mu))) := by
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  have h :=
    S.taylorPartialSum_tendsto_limitResolvent_finiteDimensionalCompression_uniform_parameterBox_of_joint
      B L hLgap hLresolvent J Q a degree ha hdegree
      hdelta hlambdaBounds hlambdaMax hrMax0 hrMaxlt epsilon hepsilon
  filter_upwards [h] with b hb
  have hAt :=
    hb lambda r mu hlambdaMin hlambdaMax' hr0 hr hmu
  simpa [dist_eq_norm] using hAt

/-- Determinants of compressed Taylor partial sums converge at every fixed
valid point of the closed Taylor parameter box. -/
theorem taylorPartialSum_det_finiteDimensionalCompression_tendsto_limitResolvent_of_joint
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap)
    (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    {m : Filter β} (a : β → α) (degree : β → ℕ)
    (ha : Tendsto a m l) (hdegree : Tendsto degree m atTop)
    {deltaMin lambdaMin lambdaMax rMax lambda r mu : ℝ}
    (hdelta : deltaMin ≤ gap)
    (hlambdaBounds : lambdaMin ≤ lambdaMax)
    (hlambdaMax : lambdaMax < deltaMin)
    (hrMax0 : 0 ≤ rMax)
    (hrMaxlt : rMax < deltaMin - lambdaMax)
    (hlambdaMin : lambdaMin ≤ lambda)
    (hlambdaMax' : lambda ≤ lambdaMax)
    (hr0 : 0 ≤ r) (hr : r ≤ rMax)
    (hmu : ‖mu - lambda‖ ≤ r) :
    Tendsto
      (fun b =>
        (continuousLinearMapCompression J Q
          (continuousLinearMapTaylorPartialSum
            (F (a b)) lambda mu (degree b))).det)
      m
      (𝓝 ((continuousLinearMapCompression J Q
        (S.limitResolvent mu)).det)) := by
  have hCompression :=
    S.taylorPartialSum_finiteDimensionalCompression_tendsto_limitResolvent_of_joint
      B L hLgap hLresolvent J Q a degree ha hdegree
      hdelta hlambdaBounds hlambdaMax hrMax0 hrMaxlt
      hlambdaMin hlambdaMax' hr0 hr hmu
  exact (ContinuousLinearMap.continuous_det.tendsto _).comp hCompression

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
