import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionCharacteristicDeterminantCompact
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

/-- The complete real characteristic determinant profile of compressed Taylor
partial sums converges uniformly on a full closed Taylor box × compact real
spectral set for arbitrary joint time/degree nets. -/
theorem taylorPartialSum_characteristicDeterminant_finiteDimensionalCompression_tendsto_uniform_closedBox_compactReal_of_joint
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    {m : Filter β} (a : β → α) (degree : β → ℕ)
    (ha : Tendsto a m l) (hdegree : Tendsto degree m atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap)
    (Z : Set ℝ) (hZcompact : IsCompact Z) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ b in m, ∀ p, box.Contains p → ∀ z ∈ Z,
        |continuousLinearMapCharacteristicDeterminant
            (continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (F (a b)) p.center p.target (degree b))) z -
          continuousLinearMapCharacteristicDeterminant
            (continuousLinearMapCompression J Q
              (S.limitResolvent p.target)) z| < epsilon := by
  let upper : ℝ := box.lambdaMax + box.rMax
  let R : ℝ := ‖Q‖ * (gap - upper)⁻¹ * ‖J‖
  have hupper : upper < gap := by
    simpa [upper] using box.upper_lt_gap
  have hmargin : 0 < gap - upper := sub_pos.mpr hupper
  have hinv : 0 ≤ (gap - upper)⁻¹ := inv_nonneg.mpr hmargin.le
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
    finiteDimensional_characteristicDeterminant_tendsto_uniformOn_compactRealParameter
      (l := m) (s := {p | box.Contains p})
      (fun b p => continuousLinearMapCompression J Q
        (continuousLinearMapTaylorPartialSum
          (F (a b)) p.center p.target (degree b)))
      (fun p => continuousLinearMapCompression J Q
        (S.limitResolvent p.target))
      R hR hlimit hoperator Z hZcompact

/-- Finite characteristic determinant sample jets converge uniformly on every
full closed Taylor box for arbitrary joint time/degree nets. -/
theorem taylorPartialSum_characteristicDeterminantSampleJet_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    {m : Filter β} (a : β → α) (degree : β → ℕ)
    (ha : Tendsto a m l) (hdegree : Tendsto degree m atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap)
    {sampleOrder : ℕ} (sample : Fin (sampleOrder + 1) → ℝ) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ b in m, ∀ p, box.Contains p →
        ‖continuousLinearMapCharacteristicDeterminantSampleJet sample
            (continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (F (a b)) p.center p.target (degree b))) -
          continuousLinearMapCharacteristicDeterminantSampleJet sample
            (continuousLinearMapCompression J Q
              (S.limitResolvent p.target))‖ < epsilon := by
  exact
    S.taylorPartialSum_continuousObservable_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
      B L hLgap hLresolvent J Q
      (continuousLinearMapCharacteristicDeterminantSampleJet sample)
      (continuous_continuousLinearMapCharacteristicDeterminantSampleJet sample)
      a degree ha hdegree box

/-- A positive continuum margin on the full closed Taylor box × compact real
spectral set is inherited by all sufficiently late joint approximants. -/
theorem taylorPartialSum_characteristicDeterminant_finiteDimensionalCompression_eventually_abs_gt_half_margin_closedBox_compactReal_of_joint
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
    ∀ᶠ b in m, ∀ p, box.Contains p → ∀ z ∈ Z,
      margin / 2 < |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q
          (continuousLinearMapTaylorPartialSum
            (F (a b)) p.center p.target (degree b))) z| := by
  have hconv :=
    S.taylorPartialSum_characteristicDeterminant_finiteDimensionalCompression_tendsto_uniform_closedBox_compactReal_of_joint
      B L hLgap hLresolvent J Q a degree ha hdegree box Z hZcompact
      (margin / 2) (half_pos hmargin)
  filter_upwards [hconv] with b hb
  intro p hp z hz
  let x := continuousLinearMapCharacteristicDeterminant
    (continuousLinearMapCompression J Q
      (continuousLinearMapTaylorPartialSum
        (F (a b)) p.center p.target (degree b))) z
  let y := continuousLinearMapCharacteristicDeterminant
    (continuousLinearMapCompression J Q
      (S.limitResolvent p.target)) z
  have hxy : |x - y| < margin / 2 := hb p hp z hz
  have hy : margin ≤ |y| := hlimitMargin p hp z hz
  have hyx : |y| ≤ |x - y| + |x| := by
    calc
      |y| = |(y - x) + x| := by ring_nf
      _ ≤ |y - x| + |x| := abs_add_le _ _
      _ = |x - y| + |x| := by rw [abs_sub_comm]
  linarith

/-- The same positive margin yields eventual real characteristic zero-exclusion
on the whole closed Taylor box × compact real spectral set. -/
theorem taylorPartialSum_characteristicDeterminant_finiteDimensionalCompression_eventually_ne_zero_closedBox_compactReal_of_joint
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
    ∀ᶠ b in m, ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q
          (continuousLinearMapTaylorPartialSum
            (F (a b)) p.center p.target (degree b))) z ≠ 0 := by
  have h :=
    S.taylorPartialSum_characteristicDeterminant_finiteDimensionalCompression_eventually_abs_gt_half_margin_closedBox_compactReal_of_joint
      B L hLgap hLresolvent J Q a degree ha hdegree box Z hZcompact
      margin hmargin hlimitMargin
  filter_upwards [h] with b hb
  intro p hp z hz
  exact abs_pos.mp (lt_trans (half_pos hmargin) (hb p hp z hz))

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
