import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionZeroFreeCharacteristicCalculusClosedBox
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

/-- Diagonal reciprocal characteristic calculus on a complete closed Taylor
box, with no rate relation between the original filter and Taylor degree. -/
theorem taylorPartialSum_characteristicDeterminantReciprocal_finiteDimensionalCompression_tendsto_uniform_closedBox_compactReal_of_tendsto_degree
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
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ p, box.Contains p → ∀ z ∈ Z,
        |continuousLinearMapCharacteristicDeterminantReciprocal
            (continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (F a) p.center p.target (degree a))) z -
          continuousLinearMapCharacteristicDeterminantReciprocal
            (continuousLinearMapCompression J Q
              (S.limitResolvent p.target)) z| < epsilon := by
  exact
    S.taylorPartialSum_characteristicDeterminantReciprocal_finiteDimensionalCompression_tendsto_uniform_closedBox_compactReal_of_joint
      B L hLgap hLresolvent J Q (fun a => a) degree tendsto_id hdegree
      box Z hZcompact margin hmargin hlimitMargin

/-- Diagonal logarithmic absolute characteristic calculus on a complete closed
Taylor box, with no rate relation. -/
theorem taylorPartialSum_characteristicDeterminantLogAbs_finiteDimensionalCompression_tendsto_uniform_closedBox_compactReal_of_tendsto_degree
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
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ p, box.Contains p → ∀ z ∈ Z,
        |continuousLinearMapCharacteristicDeterminantLogAbs
            (continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (F a) p.center p.target (degree a))) z -
          continuousLinearMapCharacteristicDeterminantLogAbs
            (continuousLinearMapCompression J Q
              (S.limitResolvent p.target)) z| < epsilon := by
  exact
    S.taylorPartialSum_characteristicDeterminantLogAbs_finiteDimensionalCompression_tendsto_uniform_closedBox_compactReal_of_joint
      B L hLgap hLresolvent J Q (fun a => a) degree tendsto_id hdegree
      box Z hZcompact margin hmargin hlimitMargin

/-- Diagonal two-point characteristic determinant-ratio calculus on complete
closed Taylor boxes and compact numerator/denominator spectral sets. -/
theorem taylorPartialSum_characteristicDeterminantRatio_finiteDimensionalCompression_tendsto_uniform_closedBox_compactReal_of_tendsto_degree
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (degree : α → ℕ) (hdegree : Tendsto degree l atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap)
    (Z W : Set ℝ) (hZcompact : IsCompact Z) (hWcompact : IsCompact W)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ w ∈ W,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q
          (S.limitResolvent p.target)) w|) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ p, box.Contains p → ∀ z ∈ Z, ∀ w ∈ W,
        |continuousLinearMapCharacteristicDeterminantRatio
            (continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (F a) p.center p.target (degree a))) z w -
          continuousLinearMapCharacteristicDeterminantRatio
            (continuousLinearMapCompression J Q
              (S.limitResolvent p.target)) z w| < epsilon := by
  exact
    S.taylorPartialSum_characteristicDeterminantRatio_finiteDimensionalCompression_tendsto_uniform_closedBox_compactReal_of_joint
      B L hLgap hLresolvent J Q (fun a => a) degree tendsto_id hdegree
      box Z W hZcompact hWcompact margin hmargin hlimitMargin

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
