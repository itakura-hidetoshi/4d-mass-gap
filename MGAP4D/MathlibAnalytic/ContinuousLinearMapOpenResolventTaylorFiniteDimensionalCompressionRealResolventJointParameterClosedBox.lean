import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterCompact
import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventFiniteParameterObservableClosedBox
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

/-- Complete closed-box convergence of an observed joint coordinate mixed
Fréchet derivative for arbitrary joint approximation nets. -/
theorem taylorPartialSum_realResolventJointCoordinateMixedResponse_tendsto_uniform_closedBox_of_joint
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (φ : (V →L[ℝ] V) →L[ℝ] W)
    (m n : ℕ) (H : Fin m → (V →L[ℝ] V)) (κ : Fin n → Option (Fin m))
    {f : Filter β} (a : β → α) (degree : β → ℕ)
    (ha : Tendsto a f l) (hdegree : Tendsto degree f atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤
      |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in f,
      ∀ p, box.Contains p → ∀ z ∈ Z,
        ‖continuousLinearMapJointSpectralOperatorRealResolventCoordinateMixedResponse
            φ m n (continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (F (a b)) p.center p.target (degree b))) H z κ -
          continuousLinearMapJointSpectralOperatorRealResolventCoordinateMixedResponse
            φ m n (continuousLinearMapCompression J Q
              (S.limitResolvent p.target)) H z κ‖ < epsilon := by
  simpa [continuousLinearMapJointSpectralOperatorRealResolventCoordinateMixedResponse] using
    S.taylorPartialSum_realResolventFiniteParameterMixedResponse_tendsto_uniform_closedBox_of_joint
      B L hLgap hLresolvent J Q φ (m + 1) n
      (continuousLinearMapJointSpectralOperatorDirectionFamily m H)
      (continuousLinearMapJointSpectralOperatorCoordinateDirectionTuple m n κ)
      a degree ha hdegree box Z margin hmargin hlimitMargin M hM hlimitNorm

/-- Complete closed-box convergence of a fixed observed joint Taylor-Dyson
coefficient for arbitrary joint approximation nets. -/
theorem taylorPartialSum_realResolventJointTaylorResponse_tendsto_uniform_closedBox_of_joint
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (φ : (V →L[ℝ] V) →L[ℝ] W)
    (parameterOrder m : ℕ) (H : Fin m → (V →L[ℝ] V))
    (ds : ℝ) (h : Fin m → ℝ) {f : Filter β}
    (a : β → α) (degree : β → ℕ) (ha : Tendsto a f l)
    (hdegree : Tendsto degree f atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤
      |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in f,
      ∀ p, box.Contains p → ∀ z ∈ Z,
        ‖continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonResponse
            φ parameterOrder m (continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (F (a b)) p.center p.target (degree b))) H z 0 ds 0 h -
          continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonResponse
            φ parameterOrder m (continuousLinearMapCompression J Q
              (S.limitResolvent p.target)) H z 0 ds 0 h‖ < epsilon := by
  simpa [continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonResponse,
    continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonCoefficient] using
    S.taylorPartialSum_realResolventFiniteParameterTaylorResponse_tendsto_uniform_closedBox_of_joint
      B L hLgap hLresolvent J Q φ parameterOrder (m + 1)
      (continuousLinearMapJointSpectralOperatorDirectionFamily m H)
      (continuousLinearMapJointSpectralOperatorParameter m ds h)
      a degree ha hdegree box Z margin hmargin hlimitMargin M hM hlimitNorm

/-- Simultaneous complete closed-box convergence of the finite observed joint
Taylor-Dyson jet for arbitrary joint approximation nets. -/
theorem taylorPartialSum_realResolventJointTaylorResponse_tendsto_uniform_closedBox_of_joint_rectangular
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (φ : (V →L[ℝ] V) →L[ℝ] W)
    (parameterOrder m : ℕ) (H : Fin m → (V →L[ℝ] V))
    (ds : ℝ) (h : Fin m → ℝ) {f : Filter β}
    (a : β → α) (degree : β → ℕ) (ha : Tendsto a f l)
    (hdegree : Tendsto degree f atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤
      |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in f,
      ∀ n : Fin (parameterOrder + 1), ∀ p, box.Contains p → ∀ z ∈ Z,
        ‖continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonResponse
            φ n.1 m (continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (F (a b)) p.center p.target (degree b))) H z 0 ds 0 h -
          continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonResponse
            φ n.1 m (continuousLinearMapCompression J Q
              (S.limitResolvent p.target)) H z 0 ds 0 h‖ < epsilon := by
  simpa [continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonResponse,
    continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonCoefficient] using
    S.taylorPartialSum_realResolventFiniteParameterTaylorResponse_tendsto_uniform_closedBox_of_joint_rectangular
      B L hLgap hLresolvent J Q φ parameterOrder (m + 1)
      (continuousLinearMapJointSpectralOperatorDirectionFamily m H)
      (continuousLinearMapJointSpectralOperatorParameter m ds h)
      a degree ha hdegree box Z margin hmargin hlimitMargin M hM hlimitNorm

/-- Closed-box convergence of a fixed basis-independent joint trace
Taylor-Dyson coefficient. -/
theorem taylorPartialSum_realResolventJointTaylorTrace_tendsto_uniform_closedBox_of_joint
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (parameterOrder m : ℕ) (H : Fin m → (V →L[ℝ] V))
    (ds : ℝ) (h : Fin m → ℝ) {f : Filter β}
    (a : β → α) (degree : β → ℕ) (ha : Tendsto a f l)
    (hdegree : Tendsto degree f atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤
      |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in f,
      ∀ p, box.Contains p → ∀ z ∈ Z,
        |continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonTraceCoefficient
            V parameterOrder m (continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (F (a b)) p.center p.target (degree b))) H z 0 ds 0 h -
          continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonTraceCoefficient
            V parameterOrder m (continuousLinearMapCompression J Q
              (S.limitResolvent p.target)) H z 0 ds 0 h| < epsilon := by
  simpa [continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonTraceCoefficient,
    Real.norm_eq_abs] using
    S.taylorPartialSum_realResolventJointTaylorResponse_tendsto_uniform_closedBox_of_joint
      B L hLgap hLresolvent J Q (continuousLinearMapTrace (V := V))
      parameterOrder m H ds h a degree ha hdegree box Z margin hmargin
      hlimitMargin M hM hlimitNorm

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
