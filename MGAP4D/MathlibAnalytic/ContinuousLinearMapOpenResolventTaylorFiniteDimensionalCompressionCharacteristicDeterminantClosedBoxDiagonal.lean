import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionCharacteristicDeterminantClosedBox
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

/-- Diagonal form: the Taylor degree may depend arbitrarily on the original
filter variable, with no rate relation, for the complete characteristic
profile on a closed Taylor box × compact real spectral set. -/
theorem taylorPartialSum_characteristicDeterminant_finiteDimensionalCompression_tendsto_uniform_closedBox_compactReal_of_tendsto_degree
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (degree : α → ℕ) (hdegree : Tendsto degree l atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap)
    (Z : Set ℝ) (hZcompact : IsCompact Z) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ p, box.Contains p → ∀ z ∈ Z,
        |continuousLinearMapCharacteristicDeterminant
            (continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (F a) p.center p.target (degree a))) z -
          continuousLinearMapCharacteristicDeterminant
            (continuousLinearMapCompression J Q
              (S.limitResolvent p.target)) z| < epsilon := by
  exact
    S.taylorPartialSum_characteristicDeterminant_finiteDimensionalCompression_tendsto_uniform_closedBox_compactReal_of_joint
      B L hLgap hLresolvent J Q (fun a => a) degree tendsto_id hdegree
      box Z hZcompact

/-- Diagonal convergence of finite characteristic determinant sample jets on
the complete closed Taylor box. -/
theorem taylorPartialSum_characteristicDeterminantSampleJet_finiteDimensionalCompression_tendsto_uniform_closedBox_of_tendsto_degree
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (degree : α → ℕ) (hdegree : Tendsto degree l atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap)
    {sampleOrder : ℕ} (sample : Fin (sampleOrder + 1) → ℝ) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ p, box.Contains p →
        ‖continuousLinearMapCharacteristicDeterminantSampleJet sample
            (continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (F a) p.center p.target (degree a))) -
          continuousLinearMapCharacteristicDeterminantSampleJet sample
            (continuousLinearMapCompression J Q
              (S.limitResolvent p.target))‖ < epsilon := by
  exact
    S.taylorPartialSum_characteristicDeterminantSampleJet_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
      B L hLgap hLresolvent J Q (fun a => a) degree tendsto_id hdegree
      box sample

/-- Diagonal quantitative real zero-exclusion on the complete closed box, with
no speed relation between the original limit and Taylor degree. -/
theorem taylorPartialSum_characteristicDeterminant_finiteDimensionalCompression_eventually_abs_gt_half_margin_closedBox_compactReal_of_tendsto_degree
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (degree : α → ℕ) (hdegree : Tendsto degree l atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap)
    (Z : Set ℝ) (hZcompact : IsCompact Z)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q
          (S.limitResolvent p.target)) z|) :
    ∀ᶠ a in l, ∀ p, box.Contains p → ∀ z ∈ Z,
      margin / 2 < |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q
          (continuousLinearMapTaylorPartialSum
            (F a) p.center p.target (degree a))) z| := by
  exact
    S.taylorPartialSum_characteristicDeterminant_finiteDimensionalCompression_eventually_abs_gt_half_margin_closedBox_compactReal_of_joint
      B L hLgap hLresolvent J Q (fun a => a) degree tendsto_id hdegree
      box Z hZcompact margin hmargin hlimitMargin

/-- Diagonal real characteristic zero-exclusion on the complete closed box. -/
theorem taylorPartialSum_characteristicDeterminant_finiteDimensionalCompression_eventually_ne_zero_closedBox_compactReal_of_tendsto_degree
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (degree : α → ℕ) (hdegree : Tendsto degree l atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap)
    (Z : Set ℝ) (hZcompact : IsCompact Z)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q
          (S.limitResolvent p.target)) z|) :
    ∀ᶠ a in l, ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q
          (continuousLinearMapTaylorPartialSum
            (F a) p.center p.target (degree a))) z ≠ 0 := by
  exact
    S.taylorPartialSum_characteristicDeterminant_finiteDimensionalCompression_eventually_ne_zero_closedBox_compactReal_of_joint
      B L hLgap hLresolvent J Q (fun a => a) degree tendsto_id hdegree
      box Z hZcompact margin hmargin hlimitMargin

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
