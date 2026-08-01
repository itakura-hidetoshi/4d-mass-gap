import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventFiniteParameterCompact
import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventOperatorSymmetricMultilinearClosedBox
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

namespace ContinuousLinearMapOpenTaylorStrongLimitData

variable {α β E V : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [FiniteDimensional ℝ V]

/-- Uniform convergence of a fixed finite-parameter mixed resolvent derivative
on a complete closed Taylor box for arbitrary joint time and Taylor-degree
nets. -/
theorem taylorPartialSum_realResolventFiniteParameterSymmetricDerivative_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (parameterDimension mixedOrder : ℕ)
    (H : Fin parameterDimension → (V →L[ℝ] V))
    (u : Fin mixedOrder → (Fin parameterDimension → ℝ))
    {m : Filter β} (a : β → α) (taylorDegree : β → ℕ)
    (ha : Tendsto a m l) (hdegree : Tendsto taylorDegree m atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in m,
      ∀ p, box.Contains p → ∀ z ∈ Z,
        ‖continuousLinearMapFiniteParameterRealResolventSymmetricDerivative
            parameterDimension mixedOrder
            (continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (F (a b)) p.center p.target (taylorDegree b))) H z u -
          continuousLinearMapFiniteParameterRealResolventSymmetricDerivative
            parameterDimension mixedOrder
            (continuousLinearMapCompression J Q (S.limitResolvent p.target)) H z u‖ < epsilon := by
  simpa only [continuousLinearMapFiniteParameterRealResolventSymmetricDerivative_apply] using
    S.taylorPartialSum_realResolventOperatorSymmetricDerivative_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
      B L hLgap hLresolvent J Q mixedOrder
      (continuousLinearMapFiniteParameterDirectionTuple
        parameterDimension mixedOrder H u)
      a taylorDegree ha hdegree box Z margin hmargin hlimitMargin
      M hM hlimitNorm

/-- Simultaneous closed-box convergence of the full finite mixed-partial jet
for arbitrary joint time and Taylor-degree nets. -/
theorem taylorPartialSum_realResolventFiniteParameterSymmetricDerivative_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint_rectangular
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (parameterDimension mixedOrder : ℕ)
    (H : Fin parameterDimension → (V →L[ℝ] V))
    (u : ∀ n : Fin (mixedOrder + 1),
      Fin n.1 → (Fin parameterDimension → ℝ))
    {m : Filter β} (a : β → α) (taylorDegree : β → ℕ)
    (ha : Tendsto a m l) (hdegree : Tendsto taylorDegree m atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in m,
      ∀ n : Fin (mixedOrder + 1), ∀ p, box.Contains p → ∀ z ∈ Z,
        ‖continuousLinearMapFiniteParameterRealResolventSymmetricDerivative
            parameterDimension n.1
            (continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (F (a b)) p.center p.target (taylorDegree b))) H z (u n) -
          continuousLinearMapFiniteParameterRealResolventSymmetricDerivative
            parameterDimension n.1
            (continuousLinearMapCompression J Q (S.limitResolvent p.target)) H z (u n)‖ < epsilon := by
  simpa only [continuousLinearMapFiniteParameterRealResolventSymmetricDerivative_apply] using
    S.taylorPartialSum_realResolventOperatorSymmetricDerivative_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint_rectangular
      B L hLgap hLresolvent J Q mixedOrder
      (fun n => continuousLinearMapFiniteParameterDirectionTuple
        parameterDimension n.1 H (u n))
      a taylorDegree ha hdegree box Z margin hmargin hlimitMargin
      M hM hlimitNorm

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
