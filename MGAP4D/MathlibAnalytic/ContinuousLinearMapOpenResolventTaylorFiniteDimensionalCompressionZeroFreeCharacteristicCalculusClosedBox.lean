import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionZeroFreeCharacteristicCalculusCompact
import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionCharacteristicDeterminantClosedBox
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

namespace ContinuousLinearMapOpenTaylorStrongLimitData

variable {α β E V : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [FiniteDimensional ℝ V]

/-- Reciprocal characteristic profiles of compressed Taylor partial sums
converge uniformly on a complete closed Taylor box × compact real spectral set
for arbitrary joint time/degree nets. -/
theorem taylorPartialSum_characteristicDeterminantReciprocal_finiteDimensionalCompression_tendsto_uniform_closedBox_compactReal_of_joint
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    {m : Filter β} (a : β → α) (degree : β → ℕ)
    (ha : Tendsto a m l) (hdegree : Tendsto degree m atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap)
    (Z : Set ℝ) (hZcompact : IsCompact Z)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q
          (S.limitResolvent p.target)) z|) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ b in m, ∀ p, box.Contains p → ∀ z ∈ Z,
        |continuousLinearMapCharacteristicDeterminantReciprocal
            (continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (F (a b)) p.center p.target (degree b))) z -
          continuousLinearMapCharacteristicDeterminantReciprocal
            (continuousLinearMapCompression J Q
              (S.limitResolvent p.target)) z| < epsilon := by
  let upper : ℝ := box.lambdaMax + box.rMax
  let R : ℝ := ‖Q‖ * (gap - upper)⁻¹ * ‖J‖
  have hupper : upper < gap := by
    simpa [upper] using box.upper_lt_gap
  have hgapMargin : 0 < gap - upper := sub_pos.mpr hupper
  have hinv : 0 ≤ (gap - upper)⁻¹ := inv_nonneg.mpr hgapMargin.le
  have hR : 0 ≤ R := by
    dsimp [R]
    exact mul_nonneg (mul_nonneg (norm_nonneg Q) hinv) (norm_nonneg J)
  have hlimit : ∀ p ∈ {p | box.Contains p},
      ‖continuousLinearMapCompression J Q
          (S.limitResolvent p.target)‖ ≤ R := by
    intro p hp
    have h := L.resolvent_finiteDimensionalCompression_norm_le_on_Iic
      J Q (by simpa [hLgap] using hupper) (box.target_le_upper hp)
    simpa [R, upper, hLgap, hLresolvent] using h
  have hoperator : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ b in m, ∀ p ∈ {p | box.Contains p},
        ‖continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (F (a b)) p.center p.target (degree b)) -
          continuousLinearMapCompression J Q
              (S.limitResolvent p.target)‖ < eta := by
    intro eta heta
    have h :=
      S.taylorPartialSum_tendsto_limitResolvent_finiteDimensionalCompression_uniform_parameterBox_of_joint
        B L hLgap hLresolvent J Q a degree ha hdegree
        box.delta_le_gap box.lambda_bounds box.lambdaMax_lt_delta
        box.rMax_nonneg box.rMax_lt_margin eta heta
    filter_upwards [h] with b hb
    intro p hp
    exact hb p.center p.radius p.target
      hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2
  exact
    finiteDimensional_characteristicDeterminantReciprocal_tendsto_uniformOn_compactRealParameter
      (l := m) (s := {p | box.Contains p})
      (fun b p => continuousLinearMapCompression J Q
        (continuousLinearMapTaylorPartialSum
          (F (a b)) p.center p.target (degree b)))
      (fun p => continuousLinearMapCompression J Q
        (S.limitResolvent p.target))
      R hR hlimit hoperator Z hZcompact margin hmargin
      (by intro p hp z hz; exact hlimitMargin p hp z hz)

/-- Logarithmic absolute characteristic profiles of compressed Taylor partial
sums converge uniformly on complete closed Taylor boxes for arbitrary joint
nets under a positive continuum determinant margin. -/
theorem taylorPartialSum_characteristicDeterminantLogAbs_finiteDimensionalCompression_tendsto_uniform_closedBox_compactReal_of_joint
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    {m : Filter β} (a : β → α) (degree : β → ℕ)
    (ha : Tendsto a m l) (hdegree : Tendsto degree m atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap)
    (Z : Set ℝ) (hZcompact : IsCompact Z)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q
          (S.limitResolvent p.target)) z|) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ b in m, ∀ p, box.Contains p → ∀ z ∈ Z,
        |continuousLinearMapCharacteristicDeterminantLogAbs
            (continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (F (a b)) p.center p.target (degree b))) z -
          continuousLinearMapCharacteristicDeterminantLogAbs
            (continuousLinearMapCompression J Q
              (S.limitResolvent p.target)) z| < epsilon := by
  let upper : ℝ := box.lambdaMax + box.rMax
  let R : ℝ := ‖Q‖ * (gap - upper)⁻¹ * ‖J‖
  have hupper : upper < gap := by
    simpa [upper] using box.upper_lt_gap
  have hgapMargin : 0 < gap - upper := sub_pos.mpr hupper
  have hinv : 0 ≤ (gap - upper)⁻¹ := inv_nonneg.mpr hgapMargin.le
  have hR : 0 ≤ R := by
    dsimp [R]
    exact mul_nonneg (mul_nonneg (norm_nonneg Q) hinv) (norm_nonneg J)
  have hlimit : ∀ p ∈ {p | box.Contains p},
      ‖continuousLinearMapCompression J Q
          (S.limitResolvent p.target)‖ ≤ R := by
    intro p hp
    have h := L.resolvent_finiteDimensionalCompression_norm_le_on_Iic
      J Q (by simpa [hLgap] using hupper) (box.target_le_upper hp)
    simpa [R, upper, hLgap, hLresolvent] using h
  have hoperator : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ b in m, ∀ p ∈ {p | box.Contains p},
        ‖continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (F (a b)) p.center p.target (degree b)) -
          continuousLinearMapCompression J Q
              (S.limitResolvent p.target)‖ < eta := by
    intro eta heta
    have h :=
      S.taylorPartialSum_tendsto_limitResolvent_finiteDimensionalCompression_uniform_parameterBox_of_joint
        B L hLgap hLresolvent J Q a degree ha hdegree
        box.delta_le_gap box.lambda_bounds box.lambdaMax_lt_delta
        box.rMax_nonneg box.rMax_lt_margin eta heta
    filter_upwards [h] with b hb
    intro p hp
    exact hb p.center p.radius p.target
      hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2
  exact
    finiteDimensional_characteristicDeterminantLogAbs_tendsto_uniformOn_compactRealParameter
      (l := m) (s := {p | box.Contains p})
      (fun b p => continuousLinearMapCompression J Q
        (continuousLinearMapTaylorPartialSum
          (F (a b)) p.center p.target (degree b)))
      (fun p => continuousLinearMapCompression J Q
        (S.limitResolvent p.target))
      R hR hlimit hoperator Z hZcompact margin hmargin
      (by intro p hp z hz; exact hlimitMargin p hp z hz)

/-- Two-point characteristic determinant ratios of compressed Taylor partial
sums converge uniformly on complete closed Taylor boxes and compact numerator /
denominator real spectral sets for arbitrary joint nets. -/
theorem taylorPartialSum_characteristicDeterminantRatio_finiteDimensionalCompression_tendsto_uniform_closedBox_compactReal_of_joint
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    {m : Filter β} (a : β → α) (degree : β → ℕ)
    (ha : Tendsto a m l) (hdegree : Tendsto degree m atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap)
    (Z W : Set ℝ) (hZcompact : IsCompact Z) (hWcompact : IsCompact W)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ w ∈ W,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q
          (S.limitResolvent p.target)) w|) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ b in m, ∀ p, box.Contains p → ∀ z ∈ Z, ∀ w ∈ W,
        |continuousLinearMapCharacteristicDeterminantRatio
            (continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (F (a b)) p.center p.target (degree b))) z w -
          continuousLinearMapCharacteristicDeterminantRatio
            (continuousLinearMapCompression J Q
              (S.limitResolvent p.target)) z w| < epsilon := by
  let upper : ℝ := box.lambdaMax + box.rMax
  let R : ℝ := ‖Q‖ * (gap - upper)⁻¹ * ‖J‖
  have hupper : upper < gap := by
    simpa [upper] using box.upper_lt_gap
  have hgapMargin : 0 < gap - upper := sub_pos.mpr hupper
  have hinv : 0 ≤ (gap - upper)⁻¹ := inv_nonneg.mpr hgapMargin.le
  have hR : 0 ≤ R := by
    dsimp [R]
    exact mul_nonneg (mul_nonneg (norm_nonneg Q) hinv) (norm_nonneg J)
  have hlimit : ∀ p ∈ {p | box.Contains p},
      ‖continuousLinearMapCompression J Q
          (S.limitResolvent p.target)‖ ≤ R := by
    intro p hp
    have h := L.resolvent_finiteDimensionalCompression_norm_le_on_Iic
      J Q (by simpa [hLgap] using hupper) (box.target_le_upper hp)
    simpa [R, upper, hLgap, hLresolvent] using h
  have hoperator : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ b in m, ∀ p ∈ {p | box.Contains p},
        ‖continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (F (a b)) p.center p.target (degree b)) -
          continuousLinearMapCompression J Q
              (S.limitResolvent p.target)‖ < eta := by
    intro eta heta
    have h :=
      S.taylorPartialSum_tendsto_limitResolvent_finiteDimensionalCompression_uniform_parameterBox_of_joint
        B L hLgap hLresolvent J Q a degree ha hdegree
        box.delta_le_gap box.lambda_bounds box.lambdaMax_lt_delta
        box.rMax_nonneg box.rMax_lt_margin eta heta
    filter_upwards [h] with b hb
    intro p hp
    exact hb p.center p.radius p.target
      hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2
  exact
    finiteDimensional_characteristicDeterminantRatio_tendsto_uniformOn_compactRealParameter_product
      (l := m) (s := {p | box.Contains p})
      (fun b p => continuousLinearMapCompression J Q
        (continuousLinearMapTaylorPartialSum
          (F (a b)) p.center p.target (degree b)))
      (fun p => continuousLinearMapCompression J Q
        (S.limitResolvent p.target))
      R hR hlimit hoperator Z W hZcompact hWcompact margin hmargin
      (by intro p hp w hw; exact hlimitMargin p hp w hw)

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
