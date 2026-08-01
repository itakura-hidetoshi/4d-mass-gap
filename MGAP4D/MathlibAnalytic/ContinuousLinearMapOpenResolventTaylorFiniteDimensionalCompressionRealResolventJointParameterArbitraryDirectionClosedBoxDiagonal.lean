import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterArbitraryDirectionClosedBox
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

/-- Diagonal no-rate closed-box convergence of an arbitrary Banach-valued
observation of a fixed genuine joint Fréchet derivative. -/
theorem taylorPartialSum_realResolventJointArbitraryDirectionResponse_tendsto_uniform_closedBox_of_tendsto_degree
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (φ : (V →L[ℝ] V) →L[ℝ] W)
    (m n : ℕ) (H : Fin m → (V →L[ℝ] V))
    (u : Fin n → (Fin (m + 1) → ℝ)) (degree : α → ℕ)
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
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l, ∀ p, box.Contains p → ∀ z ∈ Z,
      ‖continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivativeLinearResponse
          φ m n (continuousLinearMapCompression J Q
            (continuousLinearMapTaylorPartialSum (F a) p.center p.target (degree a)))
          H z 0 0 u -
        continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivativeLinearResponse
          φ m n (continuousLinearMapCompression J Q (S.limitResolvent p.target))
          H z 0 0 u‖ < epsilon := by
  exact
    S.taylorPartialSum_realResolventJointArbitraryDirectionResponse_tendsto_uniform_closedBox_of_joint
      B L hLgap hLresolvent J Q φ m n H u (fun a => a) degree
      tendsto_id hdegree box Z margin hmargin hlimitMargin M hM hlimitNorm

/-- Diagonal no-rate convergence of the complete finite arbitrary-direction
joint Fréchet response jet. -/
theorem taylorPartialSum_realResolventJointArbitraryDirectionResponse_tendsto_uniform_closedBox_of_tendsto_degree_rectangular
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (φ : (V →L[ℝ] V) →L[ℝ] W)
    (mixedOrder m : ℕ) (H : Fin m → (V →L[ℝ] V))
    (u : ∀ n : Fin (mixedOrder + 1), Fin n.1 → (Fin (m + 1) → ℝ))
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
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l, ∀ n : Fin (mixedOrder + 1),
      ∀ p, box.Contains p → ∀ z ∈ Z,
        ‖continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivativeLinearResponse
            φ m n.1 (continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum (F a) p.center p.target (degree a)))
            H z 0 0 (u n) -
          continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivativeLinearResponse
            φ m n.1 (continuousLinearMapCompression J Q (S.limitResolvent p.target))
            H z 0 0 (u n)‖ < epsilon := by
  exact
    S.taylorPartialSum_realResolventJointArbitraryDirectionResponse_tendsto_uniform_closedBox_of_joint_rectangular
      B L hLgap hLresolvent J Q φ mixedOrder m H u (fun a => a) degree
      tendsto_id hdegree box Z margin hmargin hlimitMargin M hM hlimitNorm

/-- Diagonal no-rate convergence of the basis-independent trace of a fixed
genuine joint Fréchet derivative in arbitrary directions. -/
theorem taylorPartialSum_realResolventJointArbitraryDirectionTrace_tendsto_uniform_closedBox_of_tendsto_degree
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (m n : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (u : Fin n → (Fin (m + 1) → ℝ))
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
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l, ∀ p, box.Contains p → ∀ z ∈ Z,
      |continuousLinearMapJointSpectralOperatorRealResolventSymmetricTraceDerivative
          V m n (continuousLinearMapCompression J Q
            (continuousLinearMapTaylorPartialSum (F a) p.center p.target (degree a)))
          H z 0 0 u -
        continuousLinearMapJointSpectralOperatorRealResolventSymmetricTraceDerivative
          V m n (continuousLinearMapCompression J Q (S.limitResolvent p.target))
          H z 0 0 u| < epsilon := by
  exact
    S.taylorPartialSum_realResolventJointArbitraryDirectionTrace_tendsto_uniform_closedBox_of_joint
      B L hLgap hLresolvent J Q m n H u (fun a => a) degree
      tendsto_id hdegree box Z margin hmargin hlimitMargin M hM hlimitNorm

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
