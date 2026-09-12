import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventFiniteParameterObservableClosedBox
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

namespace ContinuousLinearMapOpenTaylorStrongLimitData

variable {α E V W : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Diagonal no-rate closed-box convergence of an arbitrary observation of a
fixed finite-parameter mixed Fréchet derivative. -/
theorem taylorPartialSum_realResolventFiniteParameterMixedResponse_tendsto_uniform_closedBox_of_tendsto_degree
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (φ : (V →L[ℝ] V) →L[ℝ] W)
    (parameterDimension mixedOrder : ℕ) (H : Fin parameterDimension → (V →L[ℝ] V))
    (u : Fin mixedOrder → (Fin parameterDimension → ℝ))
    (degree : α → ℕ) (hdegree : Tendsto degree l atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant
      (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z, continuousLinearMapRealResolventNorm
      (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l, ∀ p, box.Contains p → ∀ z ∈ Z,
      ‖continuousLinearMapFiniteParameterRealResolventSymmetricDerivativeLinearResponse φ parameterDimension mixedOrder
          (continuousLinearMapCompression J Q (continuousLinearMapTaylorPartialSum
            (F a) p.center p.target (degree a))) H z u -
        continuousLinearMapFiniteParameterRealResolventSymmetricDerivativeLinearResponse φ parameterDimension mixedOrder
          (continuousLinearMapCompression J Q (S.limitResolvent p.target)) H z u‖ < epsilon := by
  exact
    S.taylorPartialSum_realResolventFiniteParameterMixedResponse_tendsto_uniform_closedBox_of_joint
      B L hLgap hLresolvent J Q φ parameterDimension mixedOrder H u
      (fun a => a) degree tendsto_id hdegree box Z margin hmargin
      hlimitMargin M hM hlimitNorm

/-- Diagonal no-rate convergence of the complete finite observed mixed
Fréchet jet. -/
theorem taylorPartialSum_realResolventFiniteParameterMixedResponse_tendsto_uniform_closedBox_of_tendsto_degree_rectangular
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (φ : (V →L[ℝ] V) →L[ℝ] W)
    (parameterDimension mixedOrder : ℕ) (H : Fin parameterDimension → (V →L[ℝ] V))
    (u : ∀ n : Fin (mixedOrder + 1), Fin n.1 → (Fin parameterDimension → ℝ))
    (degree : α → ℕ) (hdegree : Tendsto degree l atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant
      (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z, continuousLinearMapRealResolventNorm
      (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l, ∀ n : Fin (mixedOrder + 1),
      ∀ p, box.Contains p → ∀ z ∈ Z,
        ‖continuousLinearMapFiniteParameterRealResolventSymmetricDerivativeLinearResponse φ parameterDimension n.1
            (continuousLinearMapCompression J Q (continuousLinearMapTaylorPartialSum
              (F a) p.center p.target (degree a))) H z (u n) -
          continuousLinearMapFiniteParameterRealResolventSymmetricDerivativeLinearResponse φ parameterDimension n.1
            (continuousLinearMapCompression J Q (S.limitResolvent p.target)) H z (u n)‖ < epsilon := by
  exact
    S.taylorPartialSum_realResolventFiniteParameterMixedResponse_tendsto_uniform_closedBox_of_joint_rectangular
      B L hLgap hLresolvent J Q φ parameterDimension mixedOrder H u
      (fun a => a) degree tendsto_id hdegree box Z margin hmargin
      hlimitMargin M hM hlimitNorm

/-- Diagonal no-rate closed-box convergence of an arbitrary observation of a
fixed Taylor-Dyson coefficient. -/
theorem taylorPartialSum_realResolventFiniteParameterTaylorResponse_tendsto_uniform_closedBox_of_tendsto_degree
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (φ : (V →L[ℝ] V) →L[ℝ] W)
    (parameterOrder parameterDimension : ℕ) (H : Fin parameterDimension → (V →L[ℝ] V))
    (h : Fin parameterDimension → ℝ) (degree : α → ℕ) (hdegree : Tendsto degree l atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant
      (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z, continuousLinearMapRealResolventNorm
      (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l, ∀ p, box.Contains p → ∀ z ∈ Z,
      ‖continuousLinearMapFiniteParameterRealResolventTaylorDysonResponse φ parameterOrder parameterDimension
          (continuousLinearMapCompression J Q (continuousLinearMapTaylorPartialSum
            (F a) p.center p.target (degree a))) H z 0 h -
        continuousLinearMapFiniteParameterRealResolventTaylorDysonResponse φ parameterOrder parameterDimension
          (continuousLinearMapCompression J Q (S.limitResolvent p.target)) H z 0 h‖ < epsilon := by
  exact
    S.taylorPartialSum_realResolventFiniteParameterTaylorResponse_tendsto_uniform_closedBox_of_joint
      B L hLgap hLresolvent J Q φ parameterOrder parameterDimension H h
      (fun a => a) degree tendsto_id hdegree box Z margin hmargin
      hlimitMargin M hM hlimitNorm

/-- Diagonal no-rate convergence of the complete finite observed
Taylor-Dyson jet. -/
theorem taylorPartialSum_realResolventFiniteParameterTaylorResponse_tendsto_uniform_closedBox_of_tendsto_degree_rectangular
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (φ : (V →L[ℝ] V) →L[ℝ] W)
    (parameterOrder parameterDimension : ℕ) (H : Fin parameterDimension → (V →L[ℝ] V))
    (h : Fin parameterDimension → ℝ) (degree : α → ℕ) (hdegree : Tendsto degree l atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant
      (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z, continuousLinearMapRealResolventNorm
      (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l, ∀ n : Fin (parameterOrder + 1),
      ∀ p, box.Contains p → ∀ z ∈ Z,
        ‖continuousLinearMapFiniteParameterRealResolventTaylorDysonResponse φ n.1 parameterDimension
            (continuousLinearMapCompression J Q (continuousLinearMapTaylorPartialSum
              (F a) p.center p.target (degree a))) H z 0 h -
          continuousLinearMapFiniteParameterRealResolventTaylorDysonResponse φ n.1 parameterDimension
            (continuousLinearMapCompression J Q (S.limitResolvent p.target)) H z 0 h‖ < epsilon := by
  exact
    S.taylorPartialSum_realResolventFiniteParameterTaylorResponse_tendsto_uniform_closedBox_of_joint_rectangular
      B L hLgap hLresolvent J Q φ parameterOrder parameterDimension H h
      (fun a => a) degree tendsto_id hdegree box Z margin hmargin
      hlimitMargin M hM hlimitNorm

/-- Diagonal no-rate convergence of the basis-independent trace of a fixed
Taylor-Dyson coefficient. -/
theorem taylorPartialSum_realResolventFiniteParameterTaylorTrace_tendsto_uniform_closedBox_of_tendsto_degree
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (parameterOrder parameterDimension : ℕ)
    (H : Fin parameterDimension → (V →L[ℝ] V)) (h : Fin parameterDimension → ℝ)
    (degree : α → ℕ) (hdegree : Tendsto degree l atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant
      (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z, continuousLinearMapRealResolventNorm
      (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l, ∀ p, box.Contains p → ∀ z ∈ Z,
      |continuousLinearMapFiniteParameterRealResolventTaylorDysonTraceCoefficient V parameterOrder parameterDimension
          (continuousLinearMapCompression J Q (continuousLinearMapTaylorPartialSum
            (F a) p.center p.target (degree a))) H z 0 h -
        continuousLinearMapFiniteParameterRealResolventTaylorDysonTraceCoefficient V parameterOrder parameterDimension
          (continuousLinearMapCompression J Q (S.limitResolvent p.target)) H z 0 h| < epsilon := by
  exact
    S.taylorPartialSum_realResolventFiniteParameterTaylorTrace_tendsto_uniform_closedBox_of_joint
      B L hLgap hLresolvent J Q parameterOrder parameterDimension H h
      (fun a => a) degree tendsto_id hdegree box Z margin hmargin
      hlimitMargin M hM hlimitNorm

/-- Diagonal no-rate convergence of the complete finite basis-independent
trace Taylor-Dyson jet. -/
theorem taylorPartialSum_realResolventFiniteParameterTaylorTrace_tendsto_uniform_closedBox_of_tendsto_degree_rectangular
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (parameterOrder parameterDimension : ℕ)
    (H : Fin parameterDimension → (V →L[ℝ] V)) (h : Fin parameterDimension → ℝ)
    (degree : α → ℕ) (hdegree : Tendsto degree l atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant
      (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z, continuousLinearMapRealResolventNorm
      (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l, ∀ n : Fin (parameterOrder + 1),
      ∀ p, box.Contains p → ∀ z ∈ Z,
        |continuousLinearMapFiniteParameterRealResolventTaylorDysonTraceCoefficient V n.1 parameterDimension
            (continuousLinearMapCompression J Q (continuousLinearMapTaylorPartialSum
              (F a) p.center p.target (degree a))) H z 0 h -
          continuousLinearMapFiniteParameterRealResolventTaylorDysonTraceCoefficient V n.1 parameterDimension
            (continuousLinearMapCompression J Q (S.limitResolvent p.target)) H z 0 h| < epsilon := by
  exact
    S.taylorPartialSum_realResolventFiniteParameterTaylorTrace_tendsto_uniform_closedBox_of_joint_rectangular
      B L hLgap hLresolvent J Q parameterOrder parameterDimension H h
      (fun a => a) degree tendsto_id hdegree box Z margin hmargin
      hlimitMargin M hM hlimitNorm

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
