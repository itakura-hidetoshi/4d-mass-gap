import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventFiniteParameterTaylorDysonClosedBox
import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventOperatorDysonClosedBoxDiagonal
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

namespace ContinuousLinearMapOpenTaylorStrongLimitData

variable {α E V : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [FiniteDimensional ℝ V]

/-- Diagonal closed-box convergence of a fixed finite-parameter Taylor-Dyson
coefficient, with no rate relation beyond convergence of the ambient Taylor
degree to `atTop`. -/
theorem taylorPartialSum_realResolventFiniteParameterTaylorDysonCoefficient_finiteDimensionalCompression_tendsto_uniform_closedBox_of_tendsto_degree
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (parameterOrder parameterDimension : ℕ)
    (H : Fin parameterDimension → (V →L[ℝ] V))
    (h : Fin parameterDimension → ℝ)
    (degree : α → ℕ) (hdegree : Tendsto degree l atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l,
      ∀ p, box.Contains p → ∀ z ∈ Z,
        ‖continuousLinearMapFiniteParameterRealResolventTaylorDysonCoefficient
            parameterOrder parameterDimension
            (continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (F a) p.center p.target (degree a))) H z 0 h -
          continuousLinearMapFiniteParameterRealResolventTaylorDysonCoefficient
            parameterOrder parameterDimension
            (continuousLinearMapCompression J Q (S.limitResolvent p.target)) H z 0 h‖ < epsilon := by
  simpa [continuousLinearMapFiniteParameterRealResolventTaylorDysonCoefficient,
    continuousLinearMapFiniteParameterOperatorIncrement] using
    S.taylorPartialSum_realResolventOperatorDysonCoefficient_finiteDimensionalCompression_tendsto_uniform_closedBox_of_tendsto_degree
      B L hLgap hLresolvent J Q parameterOrder
      (continuousLinearMapFiniteParameterDirectionSynthesis parameterDimension H h)
      degree hdegree box Z margin hmargin hlimitMargin M hM hlimitNorm

/-- Diagonal no-rate convergence of the complete finite-parameter
Taylor-Dyson jet. -/
theorem taylorPartialSum_realResolventFiniteParameterTaylorDysonCoefficient_finiteDimensionalCompression_tendsto_uniform_closedBox_of_tendsto_degree_rectangular
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (parameterOrder parameterDimension : ℕ)
    (H : Fin parameterDimension → (V →L[ℝ] V))
    (h : Fin parameterDimension → ℝ)
    (degree : α → ℕ) (hdegree : Tendsto degree l atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l,
      ∀ n : Fin (parameterOrder + 1), ∀ p, box.Contains p → ∀ z ∈ Z,
        ‖continuousLinearMapFiniteParameterRealResolventTaylorDysonCoefficient
            n.1 parameterDimension
            (continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (F a) p.center p.target (degree a))) H z 0 h -
          continuousLinearMapFiniteParameterRealResolventTaylorDysonCoefficient
            n.1 parameterDimension
            (continuousLinearMapCompression J Q (S.limitResolvent p.target)) H z 0 h‖ < epsilon := by
  simpa [continuousLinearMapFiniteParameterRealResolventTaylorDysonCoefficient,
    continuousLinearMapFiniteParameterOperatorIncrement] using
    S.taylorPartialSum_realResolventOperatorDysonCoefficient_finiteDimensionalCompression_tendsto_uniform_closedBox_of_tendsto_degree_rectangular
      B L hLgap hLresolvent J Q parameterOrder
      (continuousLinearMapFiniteParameterDirectionSynthesis parameterDimension H h)
      degree hdegree box Z margin hmargin hlimitMargin M hM hlimitNorm

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
