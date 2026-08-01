import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventFiniteParameterObservableCompact
import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventFiniteParameterClosedBox
import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventFiniteParameterTaylorDysonClosedBox
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

namespace ContinuousLinearMapOpenTaylorStrongLimitData

variable {α β E V W : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Closed-box convergence of an arbitrary continuous-linear observation of a
fixed finite-parameter mixed Fréchet derivative for arbitrary joint nets. -/
theorem taylorPartialSum_realResolventFiniteParameterMixedResponse_tendsto_uniform_closedBox_of_joint
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (φ : (V →L[ℝ] V) →L[ℝ] W)
    (parameterDimension mixedOrder : ℕ) (H : Fin parameterDimension → (V →L[ℝ] V))
    (u : Fin mixedOrder → (Fin parameterDimension → ℝ))
    {m : Filter β} (a : β → α) (degree : β → ℕ) (ha : Tendsto a m l)
    (hdegree : Tendsto degree m atTop) (box : ContinuousLinearMapClosedTaylorParameterBox gap)
    (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant
      (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z, continuousLinearMapRealResolventNorm
      (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in m, ∀ p, box.Contains p → ∀ z ∈ Z,
      ‖continuousLinearMapFiniteParameterRealResolventSymmetricDerivativeLinearResponse φ parameterDimension mixedOrder
          (continuousLinearMapCompression J Q (continuousLinearMapTaylorPartialSum
            (F (a b)) p.center p.target (degree b))) H z u -
        continuousLinearMapFiniteParameterRealResolventSymmetricDerivativeLinearResponse φ parameterDimension mixedOrder
          (continuousLinearMapCompression J Q (S.limitResolvent p.target)) H z u‖ < epsilon := by
  intro epsilon hepsilon
  have hdelta : 0 < epsilon / (‖φ‖ + 1) := div_pos hepsilon (by positivity)
  filter_upwards [
    S.taylorPartialSum_realResolventFiniteParameterSymmetricDerivative_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
      B L hLgap hLresolvent J Q parameterDimension mixedOrder H u
      a degree ha hdegree box Z margin hmargin hlimitMargin M hM hlimitNorm
      (epsilon / (‖φ‖ + 1)) hdelta] with b hb
  intro p hp z hz
  simpa only [continuousLinearMapFiniteParameterRealResolventSymmetricDerivativeLinearResponse_apply] using
    continuousLinearMap_map_sub_norm_lt_of_norm_sub_lt φ hepsilon (hb p hp z hz)

/-- Simultaneous closed-box convergence of a complete finite observed mixed
Fréchet jet for arbitrary joint time and ambient Taylor-degree nets. -/
theorem taylorPartialSum_realResolventFiniteParameterMixedResponse_tendsto_uniform_closedBox_of_joint_rectangular
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (φ : (V →L[ℝ] V) →L[ℝ] W)
    (parameterDimension mixedOrder : ℕ) (H : Fin parameterDimension → (V →L[ℝ] V))
    (u : ∀ n : Fin (mixedOrder + 1), Fin n.1 → (Fin parameterDimension → ℝ))
    {m : Filter β} (a : β → α) (degree : β → ℕ) (ha : Tendsto a m l)
    (hdegree : Tendsto degree m atTop) (box : ContinuousLinearMapClosedTaylorParameterBox gap)
    (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant
      (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z, continuousLinearMapRealResolventNorm
      (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in m, ∀ n : Fin (mixedOrder + 1),
      ∀ p, box.Contains p → ∀ z ∈ Z,
        ‖continuousLinearMapFiniteParameterRealResolventSymmetricDerivativeLinearResponse φ parameterDimension n.1
            (continuousLinearMapCompression J Q (continuousLinearMapTaylorPartialSum
              (F (a b)) p.center p.target (degree b))) H z (u n) -
          continuousLinearMapFiniteParameterRealResolventSymmetricDerivativeLinearResponse φ parameterDimension n.1
            (continuousLinearMapCompression J Q (S.limitResolvent p.target)) H z (u n)‖ < epsilon := by
  intro epsilon hepsilon
  have hdelta : 0 < epsilon / (‖φ‖ + 1) := div_pos hepsilon (by positivity)
  filter_upwards [
    S.taylorPartialSum_realResolventFiniteParameterSymmetricDerivative_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint_rectangular
      B L hLgap hLresolvent J Q parameterDimension mixedOrder H u
      a degree ha hdegree box Z margin hmargin hlimitMargin M hM hlimitNorm
      (epsilon / (‖φ‖ + 1)) hdelta] with b hb
  intro n p hp z hz
  simpa only [continuousLinearMapFiniteParameterRealResolventSymmetricDerivativeLinearResponse_apply] using
    continuousLinearMap_map_sub_norm_lt_of_norm_sub_lt φ hepsilon (hb n p hp z hz)

/-- Closed-box convergence of an arbitrary continuous-linear observation of a
fixed finite-parameter Taylor-Dyson coefficient for arbitrary joint nets. -/
theorem taylorPartialSum_realResolventFiniteParameterTaylorResponse_tendsto_uniform_closedBox_of_joint
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (φ : (V →L[ℝ] V) →L[ℝ] W)
    (parameterOrder parameterDimension : ℕ) (H : Fin parameterDimension → (V →L[ℝ] V))
    (h : Fin parameterDimension → ℝ) {m : Filter β} (a : β → α) (degree : β → ℕ)
    (ha : Tendsto a m l) (hdegree : Tendsto degree m atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant
      (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z, continuousLinearMapRealResolventNorm
      (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in m, ∀ p, box.Contains p → ∀ z ∈ Z,
      ‖continuousLinearMapFiniteParameterRealResolventTaylorDysonResponse φ parameterOrder parameterDimension
          (continuousLinearMapCompression J Q (continuousLinearMapTaylorPartialSum
            (F (a b)) p.center p.target (degree b))) H z 0 h -
        continuousLinearMapFiniteParameterRealResolventTaylorDysonResponse φ parameterOrder parameterDimension
          (continuousLinearMapCompression J Q (S.limitResolvent p.target)) H z 0 h‖ < epsilon := by
  intro epsilon hepsilon
  have hdelta : 0 < epsilon / (‖φ‖ + 1) := div_pos hepsilon (by positivity)
  filter_upwards [
    S.taylorPartialSum_realResolventFiniteParameterTaylorDysonCoefficient_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
      B L hLgap hLresolvent J Q parameterOrder parameterDimension H h
      a degree ha hdegree box Z margin hmargin hlimitMargin M hM hlimitNorm
      (epsilon / (‖φ‖ + 1)) hdelta] with b hb
  intro p hp z hz
  simpa only [continuousLinearMapFiniteParameterRealResolventTaylorDysonResponse_apply] using
    continuousLinearMap_map_sub_norm_lt_of_norm_sub_lt φ hepsilon (hb p hp z hz)

/-- Simultaneous closed-box convergence of the complete finite observed
Taylor-Dyson jet for arbitrary joint time and ambient Taylor-degree nets. -/
theorem taylorPartialSum_realResolventFiniteParameterTaylorResponse_tendsto_uniform_closedBox_of_joint_rectangular
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (φ : (V →L[ℝ] V) →L[ℝ] W)
    (parameterOrder parameterDimension : ℕ) (H : Fin parameterDimension → (V →L[ℝ] V))
    (h : Fin parameterDimension → ℝ) {m : Filter β} (a : β → α) (degree : β → ℕ)
    (ha : Tendsto a m l) (hdegree : Tendsto degree m atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant
      (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z, continuousLinearMapRealResolventNorm
      (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in m, ∀ n : Fin (parameterOrder + 1),
      ∀ p, box.Contains p → ∀ z ∈ Z,
        ‖continuousLinearMapFiniteParameterRealResolventTaylorDysonResponse φ n.1 parameterDimension
            (continuousLinearMapCompression J Q (continuousLinearMapTaylorPartialSum
              (F (a b)) p.center p.target (degree b))) H z 0 h -
          continuousLinearMapFiniteParameterRealResolventTaylorDysonResponse φ n.1 parameterDimension
            (continuousLinearMapCompression J Q (S.limitResolvent p.target)) H z 0 h‖ < epsilon := by
  intro epsilon hepsilon
  have hdelta : 0 < epsilon / (‖φ‖ + 1) := div_pos hepsilon (by positivity)
  filter_upwards [
    S.taylorPartialSum_realResolventFiniteParameterTaylorDysonCoefficient_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint_rectangular
      B L hLgap hLresolvent J Q parameterOrder parameterDimension H h
      a degree ha hdegree box Z margin hmargin hlimitMargin M hM hlimitNorm
      (epsilon / (‖φ‖ + 1)) hdelta] with b hb
  intro n p hp z hz
  simpa only [continuousLinearMapFiniteParameterRealResolventTaylorDysonResponse_apply] using
    continuousLinearMap_map_sub_norm_lt_of_norm_sub_lt φ hepsilon (hb n p hp z hz)

/-- Closed-box convergence of the basis-independent trace of a fixed
Taylor-Dyson coefficient. -/
theorem taylorPartialSum_realResolventFiniteParameterTaylorTrace_tendsto_uniform_closedBox_of_joint
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (parameterOrder parameterDimension : ℕ)
    (H : Fin parameterDimension → (V →L[ℝ] V)) (h : Fin parameterDimension → ℝ)
    {m : Filter β} (a : β → α) (degree : β → ℕ) (ha : Tendsto a m l)
    (hdegree : Tendsto degree m atTop) (box : ContinuousLinearMapClosedTaylorParameterBox gap)
    (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant
      (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z, continuousLinearMapRealResolventNorm
      (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in m, ∀ p, box.Contains p → ∀ z ∈ Z,
      |continuousLinearMapFiniteParameterRealResolventTaylorDysonTraceCoefficient V parameterOrder parameterDimension
          (continuousLinearMapCompression J Q (continuousLinearMapTaylorPartialSum
            (F (a b)) p.center p.target (degree b))) H z 0 h -
        continuousLinearMapFiniteParameterRealResolventTaylorDysonTraceCoefficient V parameterOrder parameterDimension
          (continuousLinearMapCompression J Q (S.limitResolvent p.target)) H z 0 h| < epsilon := by
  simpa [Real.norm_eq_abs, continuousLinearMapFiniteParameterRealResolventTaylorDysonTraceCoefficient] using
    S.taylorPartialSum_realResolventFiniteParameterTaylorResponse_tendsto_uniform_closedBox_of_joint
      B L hLgap hLresolvent J Q (continuousLinearMapTrace (V := V))
      parameterOrder parameterDimension H h a degree ha hdegree
      box Z margin hmargin hlimitMargin M hM hlimitNorm

/-- Closed-box convergence of the complete finite basis-independent trace
Taylor-Dyson jet. -/
theorem taylorPartialSum_realResolventFiniteParameterTaylorTrace_tendsto_uniform_closedBox_of_joint_rectangular
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (parameterOrder parameterDimension : ℕ)
    (H : Fin parameterDimension → (V →L[ℝ] V)) (h : Fin parameterDimension → ℝ)
    {m : Filter β} (a : β → α) (degree : β → ℕ) (ha : Tendsto a m l)
    (hdegree : Tendsto degree m atTop) (box : ContinuousLinearMapClosedTaylorParameterBox gap)
    (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant
      (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z, continuousLinearMapRealResolventNorm
      (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in m, ∀ n : Fin (parameterOrder + 1),
      ∀ p, box.Contains p → ∀ z ∈ Z,
        |continuousLinearMapFiniteParameterRealResolventTaylorDysonTraceCoefficient V n.1 parameterDimension
            (continuousLinearMapCompression J Q (continuousLinearMapTaylorPartialSum
              (F (a b)) p.center p.target (degree b))) H z 0 h -
          continuousLinearMapFiniteParameterRealResolventTaylorDysonTraceCoefficient V n.1 parameterDimension
            (continuousLinearMapCompression J Q (S.limitResolvent p.target)) H z 0 h| < epsilon := by
  simpa [Real.norm_eq_abs, continuousLinearMapFiniteParameterRealResolventTaylorDysonTraceCoefficient] using
    S.taylorPartialSum_realResolventFiniteParameterTaylorResponse_tendsto_uniform_closedBox_of_joint_rectangular
      B L hLgap hLresolvent J Q (continuousLinearMapTrace (V := V))
      parameterOrder parameterDimension H h a degree ha hdegree
      box Z margin hmargin hlimitMargin M hM hlimitNorm

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
