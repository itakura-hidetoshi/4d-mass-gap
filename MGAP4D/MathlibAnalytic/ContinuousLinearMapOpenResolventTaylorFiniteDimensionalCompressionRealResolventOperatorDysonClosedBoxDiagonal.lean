import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventOperatorDysonClosedBox
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

namespace ContinuousLinearMapOpenTaylorStrongLimitData

variable {α E V : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [FiniteDimensional ℝ V]

/-- Diagonal closed-box convergence of a fixed operator Dyson coefficient,
with no time/Taylor-degree rate relation beyond convergence of the Taylor
degree net to `atTop`. -/
theorem taylorPartialSum_realResolventOperatorDysonCoefficient_finiteDimensionalCompression_tendsto_uniform_closedBox_of_tendsto_degree
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (dysonOrder : ℕ) (H : V →L[ℝ] V)
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
        ‖continuousLinearMapRealResolventOperatorDysonCoefficient dysonOrder
            (continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (F a) p.center p.target (degree a))) H z -
          continuousLinearMapRealResolventOperatorDysonCoefficient dysonOrder
            (continuousLinearMapCompression J Q (S.limitResolvent p.target)) H z‖ < epsilon := by
  exact
    S.taylorPartialSum_realResolventOperatorDysonCoefficient_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
      B L hLgap hLresolvent J Q dysonOrder H (fun a => a) degree
      tendsto_id hdegree box Z margin hmargin hlimitMargin M hM hlimitNorm

/-- Diagonal closed-box convergence of the full finite operator Dyson jet. -/
theorem taylorPartialSum_realResolventOperatorDysonCoefficient_finiteDimensionalCompression_tendsto_uniform_closedBox_of_tendsto_degree_rectangular
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (dysonOrder : ℕ) (H : V →L[ℝ] V)
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
      ∀ n : Fin (dysonOrder + 1), ∀ p, box.Contains p → ∀ z ∈ Z,
        ‖continuousLinearMapRealResolventOperatorDysonCoefficient n.1
            (continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (F a) p.center p.target (degree a))) H z -
          continuousLinearMapRealResolventOperatorDysonCoefficient n.1
            (continuousLinearMapCompression J Q (S.limitResolvent p.target)) H z‖ < epsilon := by
  exact
    S.taylorPartialSum_realResolventOperatorDysonCoefficient_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint_rectangular
      B L hLgap hLresolvent J Q dysonOrder H (fun a => a) degree
      tendsto_id hdegree box Z margin hmargin hlimitMargin M hM hlimitNorm

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
