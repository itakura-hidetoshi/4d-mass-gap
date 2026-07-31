import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventStabilityClosedBox
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

/-- Diagonal real-resolvent stability on a complete closed Taylor box, with no
rate relation between the original filter and the Taylor degree. -/
theorem taylorPartialSum_realResolvent_finiteDimensionalCompression_eventually_stable_uniform_closedBox_of_tendsto_degree
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (degree : α → ℕ) (hdegree : Tendsto degree l atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitResolventNorm : ∀ p, box.Contains p → ∀ z ∈ Z, continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l, ∀ p, box.Contains p → ∀ z ∈ Z,
      IsUnit (continuousLinearMapRealShift (continuousLinearMapCompression J Q (continuousLinearMapTaylorPartialSum (F a) p.center p.target (degree a))) z) ∧
      continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q (continuousLinearMapTaylorPartialSum (F a) p.center p.target (degree a))) z ≤ 2 * (M + 1) ∧
      ‖continuousLinearMapRealResolvent (continuousLinearMapCompression J Q (continuousLinearMapTaylorPartialSum (F a) p.center p.target (degree a))) z - continuousLinearMapRealResolvent (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z‖ < epsilon := by
  exact S.taylorPartialSum_realResolvent_finiteDimensionalCompression_eventually_stable_uniform_closedBox_of_joint
    B L hLgap hLresolvent J Q (fun a => a) degree tendsto_id hdegree
    box Z margin hmargin hlimitMargin M hM hlimitResolventNorm

/-- Diagonal operator-valued real-resolvent convergence on the complete closed
Taylor box. -/
theorem taylorPartialSum_realResolvent_finiteDimensionalCompression_tendsto_uniform_closedBox_of_tendsto_degree
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (degree : α → ℕ) (hdegree : Tendsto degree l atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitResolventNorm : ∀ p, box.Contains p → ∀ z ∈ Z, continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l, ∀ p, box.Contains p → ∀ z ∈ Z,
      ‖continuousLinearMapRealResolvent (continuousLinearMapCompression J Q (continuousLinearMapTaylorPartialSum (F a) p.center p.target (degree a))) z - continuousLinearMapRealResolvent (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z‖ < epsilon := by
  exact S.taylorPartialSum_realResolvent_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
    B L hLgap hLresolvent J Q (fun a => a) degree tendsto_id hdegree
    box Z margin hmargin hlimitMargin M hM hlimitResolventNorm

/-- Diagonal eventual real resolvent-set inclusion on the complete closed box. -/
theorem taylorPartialSum_finiteDimensionalCompression_eventually_mem_realResolventSet_uniform_closedBox_of_tendsto_degree
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (degree : α → ℕ) (hdegree : Tendsto degree l atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitResolventNorm : ∀ p, box.Contains p → ∀ z ∈ Z, continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ᶠ a in l, ∀ p, box.Contains p → ∀ z ∈ Z,
      z ∈ resolventSet ℝ (continuousLinearMapCompression J Q (continuousLinearMapTaylorPartialSum (F a) p.center p.target (degree a))) := by
  exact S.taylorPartialSum_finiteDimensionalCompression_eventually_mem_realResolventSet_uniform_closedBox_of_joint
    B L hLgap hLresolvent J Q (fun a => a) degree tendsto_id hdegree
    box Z margin hmargin hlimitMargin M hM hlimitResolventNorm

/-- Diagonal eventual exclusion from the real operator-norm pseudospectrum. -/
theorem taylorPartialSum_finiteDimensionalCompression_eventually_not_mem_realPseudospectrum_uniform_closedBox_of_tendsto_degree
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (degree : α → ℕ) (hdegree : Tendsto degree l atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitResolventNorm : ∀ p, box.Contains p → ∀ z ∈ Z, continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ᶠ a in l, ∀ p, box.Contains p → ∀ z ∈ Z,
      z ∉ continuousLinearMapRealPseudospectrum (2 * (M + 1)) (continuousLinearMapCompression J Q (continuousLinearMapTaylorPartialSum (F a) p.center p.target (degree a))) := by
  exact S.taylorPartialSum_finiteDimensionalCompression_eventually_not_mem_realPseudospectrum_uniform_closedBox_of_joint
    B L hLgap hLresolvent J Q (fun a => a) degree tendsto_id hdegree
    box Z margin hmargin hlimitMargin M hM hlimitResolventNorm

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
