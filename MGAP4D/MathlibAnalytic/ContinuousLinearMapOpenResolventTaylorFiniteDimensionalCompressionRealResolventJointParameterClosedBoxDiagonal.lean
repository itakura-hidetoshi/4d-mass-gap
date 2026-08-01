import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterClosedBox
import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventFiniteParameterObservableClosedBoxDiagonal
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

/-- Diagonal no-rate complete closed-box convergence of an observed joint
coordinate mixed Fréchet derivative. -/
theorem taylorPartialSum_realResolventJointCoordinateMixedResponse_tendsto_uniform_closedBox_of_tendsto_degree
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (φ : (V →L[ℝ] V) →L[ℝ] W)
    (m n : ℕ) (H : Fin m → (V →L[ℝ] V)) (κ : Fin n → Option (Fin m))
    (degree : α → ℕ) (hdegree : Tendsto degree l atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤
      |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l,
      ∀ p, box.Contains p → ∀ z ∈ Z,
        ‖continuousLinearMapJointSpectralOperatorRealResolventCoordinateMixedResponse
            φ m n (continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (F a) p.center p.target (degree a))) H z κ -
          continuousLinearMapJointSpectralOperatorRealResolventCoordinateMixedResponse
            φ m n (continuousLinearMapCompression J Q
              (S.limitResolvent p.target)) H z κ‖ < epsilon := by
  exact
    S.taylorPartialSum_realResolventJointCoordinateMixedResponse_tendsto_uniform_closedBox_of_joint
      B L hLgap hLresolvent J Q φ m n H κ (fun a => a) degree tendsto_id hdegree
      box Z margin hmargin hlimitMargin M hM hlimitNorm

/-- Diagonal no-rate complete closed-box convergence of a fixed observed joint
Taylor-Dyson coefficient. -/
theorem taylorPartialSum_realResolventJointTaylorResponse_tendsto_uniform_closedBox_of_tendsto_degree
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (φ : (V →L[ℝ] V) →L[ℝ] W)
    (parameterOrder m : ℕ) (H : Fin m → (V →L[ℝ] V))
    (ds : ℝ) (h : Fin m → ℝ) (degree : α → ℕ)
    (hdegree : Tendsto degree l atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤
      |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l,
      ∀ p, box.Contains p → ∀ z ∈ Z,
        ‖continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonResponse
            φ parameterOrder m (continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (F a) p.center p.target (degree a))) H z 0 ds 0 h -
          continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonResponse
            φ parameterOrder m (continuousLinearMapCompression J Q
              (S.limitResolvent p.target)) H z 0 ds 0 h‖ < epsilon := by
  exact
    S.taylorPartialSum_realResolventJointTaylorResponse_tendsto_uniform_closedBox_of_joint
      B L hLgap hLresolvent J Q φ parameterOrder m H ds h
      (fun a => a) degree tendsto_id hdegree box Z margin hmargin
      hlimitMargin M hM hlimitNorm

/-- Diagonal no-rate convergence of the complete finite observed joint
Taylor-Dyson jet. -/
theorem taylorPartialSum_realResolventJointTaylorResponse_tendsto_uniform_closedBox_of_tendsto_degree_rectangular
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (φ : (V →L[ℝ] V) →L[ℝ] W)
    (parameterOrder m : ℕ) (H : Fin m → (V →L[ℝ] V))
    (ds : ℝ) (h : Fin m → ℝ) (degree : α → ℕ)
    (hdegree : Tendsto degree l atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤
      |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l,
      ∀ n : Fin (parameterOrder + 1), ∀ p, box.Contains p → ∀ z ∈ Z,
        ‖continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonResponse
            φ n.1 m (continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (F a) p.center p.target (degree a))) H z 0 ds 0 h -
          continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonResponse
            φ n.1 m (continuousLinearMapCompression J Q
              (S.limitResolvent p.target)) H z 0 ds 0 h‖ < epsilon := by
  exact
    S.taylorPartialSum_realResolventJointTaylorResponse_tendsto_uniform_closedBox_of_joint_rectangular
      B L hLgap hLresolvent J Q φ parameterOrder m H ds h
      (fun a => a) degree tendsto_id hdegree box Z margin hmargin
      hlimitMargin M hM hlimitNorm

/-- Diagonal no-rate convergence of a basis-independent joint trace
Taylor-Dyson coefficient. -/
theorem taylorPartialSum_realResolventJointTaylorTrace_tendsto_uniform_closedBox_of_tendsto_degree
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (parameterOrder m : ℕ) (H : Fin m → (V →L[ℝ] V))
    (ds : ℝ) (h : Fin m → ℝ) (degree : α → ℕ)
    (hdegree : Tendsto degree l atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤
      |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l,
      ∀ p, box.Contains p → ∀ z ∈ Z,
        |continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonTraceCoefficient
            V parameterOrder m (continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (F a) p.center p.target (degree a))) H z 0 ds 0 h -
          continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonTraceCoefficient
            V parameterOrder m (continuousLinearMapCompression J Q
              (S.limitResolvent p.target)) H z 0 ds 0 h| < epsilon := by
  exact
    S.taylorPartialSum_realResolventJointTaylorTrace_tendsto_uniform_closedBox_of_joint
      B L hLgap hLresolvent J Q parameterOrder m H ds h
      (fun a => a) degree tendsto_id hdegree box Z margin hmargin
      hlimitMargin M hM hlimitNorm

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
