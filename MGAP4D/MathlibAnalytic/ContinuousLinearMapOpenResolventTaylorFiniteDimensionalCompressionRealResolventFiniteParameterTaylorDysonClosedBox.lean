import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventFiniteParameterTaylorDysonCompact
import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventOperatorDysonClosedBox
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

/-- Closed-box convergence of a fixed finite-parameter Taylor-Dyson
coefficient for arbitrary joint time and ambient Taylor-degree nets. -/
theorem taylorPartialSum_realResolventFiniteParameterTaylorDysonCoefficient_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (parameterOrder parameterDimension : ℕ)
    (H : Fin parameterDimension → (V →L[ℝ] V))
    (h : Fin parameterDimension → ℝ)
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
        ‖continuousLinearMapFiniteParameterRealResolventTaylorDysonCoefficient
            parameterOrder parameterDimension
            (continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (F (a b)) p.center p.target (taylorDegree b))) H z 0 h -
          continuousLinearMapFiniteParameterRealResolventTaylorDysonCoefficient
            parameterOrder parameterDimension
            (continuousLinearMapCompression J Q (S.limitResolvent p.target)) H z 0 h‖ < epsilon := by
  simpa [continuousLinearMapFiniteParameterRealResolventTaylorDysonCoefficient,
    continuousLinearMapFiniteParameterOperatorIncrement] using
    S.taylorPartialSum_realResolventOperatorDysonCoefficient_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
      B L hLgap hLresolvent J Q parameterOrder
      (continuousLinearMapFiniteParameterDirectionSynthesis parameterDimension H h)
      a taylorDegree ha hdegree box Z margin hmargin hlimitMargin M hM hlimitNorm

/-- Simultaneous closed-box convergence of the complete finite parameter
Taylor-Dyson jet for arbitrary joint time and ambient Taylor-degree nets. -/
theorem taylorPartialSum_realResolventFiniteParameterTaylorDysonCoefficient_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint_rectangular
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (parameterOrder parameterDimension : ℕ)
    (H : Fin parameterDimension → (V →L[ℝ] V))
    (h : Fin parameterDimension → ℝ)
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
      ∀ n : Fin (parameterOrder + 1), ∀ p, box.Contains p → ∀ z ∈ Z,
        ‖continuousLinearMapFiniteParameterRealResolventTaylorDysonCoefficient
            n.1 parameterDimension
            (continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (F (a b)) p.center p.target (taylorDegree b))) H z 0 h -
          continuousLinearMapFiniteParameterRealResolventTaylorDysonCoefficient
            n.1 parameterDimension
            (continuousLinearMapCompression J Q (S.limitResolvent p.target)) H z 0 h‖ < epsilon := by
  simpa [continuousLinearMapFiniteParameterRealResolventTaylorDysonCoefficient,
    continuousLinearMapFiniteParameterOperatorIncrement] using
    S.taylorPartialSum_realResolventOperatorDysonCoefficient_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint_rectangular
      B L hLgap hLresolvent J Q parameterOrder
      (continuousLinearMapFiniteParameterDirectionSynthesis parameterDimension H h)
      a taylorDegree ha hdegree box Z margin hmargin hlimitMargin M hM hlimitNorm

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
