import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalZeroFreeCharacteristicCalculusCore
import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionCharacteristicDeterminantCompact
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

namespace ContinuousLinearMapOpenTaylorStrongLimitData

variable {α E V : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [FiniteDimensional ℝ V]

/-- Reciprocal characteristic profiles of compressed fixed Taylor derivatives
converge uniformly on compact Taylor × real spectral products under a positive
continuum determinant margin. -/
theorem iteratedDeriv_characteristicDeterminantReciprocal_finiteDimensionalCompression_tendsto_uniformOn_compact_product
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (k : ℕ)
    (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < gap)
    (Z : Set ℝ) (hZcompact : IsCompact Z)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ lambda ∈ K, ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k S.limitResolvent lambda)) z|) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ lambda ∈ K, ∀ z ∈ Z,
        |continuousLinearMapCharacteristicDeterminantReciprocal
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) z -
          continuousLinearMapCharacteristicDeterminantReciprocal
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda)) z| < epsilon := by
  let R : ℝ :=
    ‖Q‖ * ((k.factorial : ℝ) * (gap - u)⁻¹ ^ (k + 1)) * ‖J‖
  have hmarginGap : 0 < gap - u := sub_pos.mpr hu
  have hinv : 0 ≤ (gap - u)⁻¹ := inv_nonneg.mpr hmarginGap.le
  have hR : 0 ≤ R := by
    dsimp [R]
    exact mul_nonneg
      (mul_nonneg (norm_nonneg Q)
        (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hinv _)))
      (norm_nonneg J)
  have hlimit : ∀ lambda ∈ K,
      ‖continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k S.limitResolvent lambda)‖ ≤ R := by
    intro lambda hlambda
    have h :=
      L.iteratedDeriv_finiteDimensionalCompression_norm_le_on_Iic
        J Q k (by simpa [hLgap] using hu) (hKu hlambda)
    simpa [R, hLgap, hLresolvent] using h
  have hoperator :=
    S.iteratedDeriv_tendsto_uniformOn_compact_finiteDimensionalCompression
      B L hLgap hLresolvent J Q k K hKcompact hKu hu
  exact
    finiteDimensional_characteristicDeterminantReciprocal_tendsto_uniformOn_compactRealParameter
      (l := l) (s := K)
      (fun a lambda => continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k (F a) lambda))
      (fun lambda => continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k S.limitResolvent lambda))
      R hR hlimit hoperator Z hZcompact margin hmargin hlimitMargin

/-- Logarithmic absolute characteristic profiles of compressed fixed Taylor
derivatives converge uniformly on compact products under the same positive
continuum determinant margin. -/
theorem iteratedDeriv_characteristicDeterminantLogAbs_finiteDimensionalCompression_tendsto_uniformOn_compact_product
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (k : ℕ)
    (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < gap)
    (Z : Set ℝ) (hZcompact : IsCompact Z)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ lambda ∈ K, ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k S.limitResolvent lambda)) z|) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ lambda ∈ K, ∀ z ∈ Z,
        |continuousLinearMapCharacteristicDeterminantLogAbs
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) z -
          continuousLinearMapCharacteristicDeterminantLogAbs
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda)) z| < epsilon := by
  let R : ℝ :=
    ‖Q‖ * ((k.factorial : ℝ) * (gap - u)⁻¹ ^ (k + 1)) * ‖J‖
  have hmarginGap : 0 < gap - u := sub_pos.mpr hu
  have hinv : 0 ≤ (gap - u)⁻¹ := inv_nonneg.mpr hmarginGap.le
  have hR : 0 ≤ R := by
    dsimp [R]
    exact mul_nonneg
      (mul_nonneg (norm_nonneg Q)
        (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hinv _)))
      (norm_nonneg J)
  have hlimit : ∀ lambda ∈ K,
      ‖continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k S.limitResolvent lambda)‖ ≤ R := by
    intro lambda hlambda
    have h :=
      L.iteratedDeriv_finiteDimensionalCompression_norm_le_on_Iic
        J Q k (by simpa [hLgap] using hu) (hKu hlambda)
    simpa [R, hLgap, hLresolvent] using h
  have hoperator :=
    S.iteratedDeriv_tendsto_uniformOn_compact_finiteDimensionalCompression
      B L hLgap hLresolvent J Q k K hKcompact hKu hu
  exact
    finiteDimensional_characteristicDeterminantLogAbs_tendsto_uniformOn_compactRealParameter
      (l := l) (s := K)
      (fun a lambda => continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k (F a) lambda))
      (fun lambda => continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k S.limitResolvent lambda))
      R hR hlimit hoperator Z hZcompact margin hmargin hlimitMargin

/-- Two-point characteristic determinant ratios of compressed fixed Taylor
derivatives converge uniformly on compact numerator/denominator spectral sets
under a positive continuum denominator margin. -/
theorem iteratedDeriv_characteristicDeterminantRatio_finiteDimensionalCompression_tendsto_uniformOn_compact_product
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (k : ℕ)
    (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < gap)
    (Z W : Set ℝ) (hZcompact : IsCompact Z) (hWcompact : IsCompact W)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ lambda ∈ K, ∀ w ∈ W,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k S.limitResolvent lambda)) w|) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ lambda ∈ K, ∀ z ∈ Z, ∀ w ∈ W,
        |continuousLinearMapCharacteristicDeterminantRatio
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) z w -
          continuousLinearMapCharacteristicDeterminantRatio
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda)) z w| < epsilon := by
  let R : ℝ :=
    ‖Q‖ * ((k.factorial : ℝ) * (gap - u)⁻¹ ^ (k + 1)) * ‖J‖
  have hmarginGap : 0 < gap - u := sub_pos.mpr hu
  have hinv : 0 ≤ (gap - u)⁻¹ := inv_nonneg.mpr hmarginGap.le
  have hR : 0 ≤ R := by
    dsimp [R]
    exact mul_nonneg
      (mul_nonneg (norm_nonneg Q)
        (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hinv _)))
      (norm_nonneg J)
  have hlimit : ∀ lambda ∈ K,
      ‖continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k S.limitResolvent lambda)‖ ≤ R := by
    intro lambda hlambda
    have h :=
      L.iteratedDeriv_finiteDimensionalCompression_norm_le_on_Iic
        J Q k (by simpa [hLgap] using hu) (hKu hlambda)
    simpa [R, hLgap, hLresolvent] using h
  have hoperator :=
    S.iteratedDeriv_tendsto_uniformOn_compact_finiteDimensionalCompression
      B L hLgap hLresolvent J Q k K hKcompact hKu hu
  exact
    finiteDimensional_characteristicDeterminantRatio_tendsto_uniformOn_compactRealParameter_product
      (l := l) (s := K)
      (fun a lambda => continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k (F a) lambda))
      (fun lambda => continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k S.limitResolvent lambda))
      R hR hlimit hoperator Z W hZcompact hWcompact
      margin hmargin hlimitMargin

/-- A complete finite Taylor jet of reciprocal characteristic profiles
converges simultaneously on compact Taylor × spectral products. -/
theorem iteratedDeriv_characteristicDeterminantReciprocal_finiteDimensionalCompression_tendsto_uniformOn_compact_product_jet
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (order : ℕ)
    (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < gap)
    (Z : Set ℝ) (hZcompact : IsCompact Z)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ k ≤ order, ∀ lambda ∈ K, ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k S.limitResolvent lambda)) z|) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ k ≤ order, ∀ lambda ∈ K, ∀ z ∈ Z,
        |continuousLinearMapCharacteristicDeterminantReciprocal
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) z -
          continuousLinearMapCharacteristicDeterminantReciprocal
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda)) z| < epsilon := by
  intro epsilon hepsilon
  have hk : ∀ k ∈ Finset.range (order + 1),
      ∀ᶠ a in l, ∀ lambda ∈ K, ∀ z ∈ Z,
        |continuousLinearMapCharacteristicDeterminantReciprocal
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) z -
          continuousLinearMapCharacteristicDeterminantReciprocal
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda)) z| < epsilon := by
    intro k hkRange
    have hkOrder : k ≤ order := Nat.lt_succ_iff.mp (Finset.mem_range.mp hkRange)
    exact S.iteratedDeriv_characteristicDeterminantReciprocal_finiteDimensionalCompression_tendsto_uniformOn_compact_product
      B L hLgap hLresolvent J Q k K hKcompact hKu hu Z hZcompact
      margin hmargin (hlimitMargin k hkOrder) epsilon hepsilon
  have hfinite : ∀ᶠ a in l, ∀ k ∈ Finset.range (order + 1),
      ∀ lambda ∈ K, ∀ z ∈ Z,
        |continuousLinearMapCharacteristicDeterminantReciprocal
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) z -
          continuousLinearMapCharacteristicDeterminantReciprocal
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda)) z| < epsilon := by
    change {a | ∀ k ∈ Finset.range (order + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
      |continuousLinearMapCharacteristicDeterminantReciprocal
          (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (F a) lambda)) z -
        continuousLinearMapCharacteristicDeterminantReciprocal
          (continuousLinearMapCompression J Q (_root_.iteratedDeriv k S.limitResolvent lambda)) z| < epsilon} ∈ l
    rw [show {a | ∀ k ∈ Finset.range (order + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
      |continuousLinearMapCharacteristicDeterminantReciprocal
          (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (F a) lambda)) z -
        continuousLinearMapCharacteristicDeterminantReciprocal
          (continuousLinearMapCompression J Q (_root_.iteratedDeriv k S.limitResolvent lambda)) z| < epsilon} =
      ⋂ k ∈ Finset.range (order + 1), {a | ∀ lambda ∈ K, ∀ z ∈ Z,
        |continuousLinearMapCharacteristicDeterminantReciprocal
            (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (F a) lambda)) z -
          continuousLinearMapCharacteristicDeterminantReciprocal
            (continuousLinearMapCompression J Q (_root_.iteratedDeriv k S.limitResolvent lambda)) z| < epsilon} by
      ext a
      simp]
    exact (Filter.biInter_finset_mem (Finset.range (order + 1))).2 hk
  filter_upwards [hfinite] with a ha
  intro k hkOrder
  exact ha k (Finset.mem_range.2 (Nat.lt_succ_iff.2 hkOrder))

/-- A complete finite Taylor jet of logarithmic absolute characteristic
profiles converges simultaneously on compact product sets. -/
theorem iteratedDeriv_characteristicDeterminantLogAbs_finiteDimensionalCompression_tendsto_uniformOn_compact_product_jet
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (order : ℕ)
    (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < gap)
    (Z : Set ℝ) (hZcompact : IsCompact Z)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ k ≤ order, ∀ lambda ∈ K, ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k S.limitResolvent lambda)) z|) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ k ≤ order, ∀ lambda ∈ K, ∀ z ∈ Z,
        |continuousLinearMapCharacteristicDeterminantLogAbs
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) z -
          continuousLinearMapCharacteristicDeterminantLogAbs
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda)) z| < epsilon := by
  intro epsilon hepsilon
  have hk : ∀ k ∈ Finset.range (order + 1),
      ∀ᶠ a in l, ∀ lambda ∈ K, ∀ z ∈ Z,
        |continuousLinearMapCharacteristicDeterminantLogAbs
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) z -
          continuousLinearMapCharacteristicDeterminantLogAbs
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda)) z| < epsilon := by
    intro k hkRange
    have hkOrder : k ≤ order := Nat.lt_succ_iff.mp (Finset.mem_range.mp hkRange)
    exact S.iteratedDeriv_characteristicDeterminantLogAbs_finiteDimensionalCompression_tendsto_uniformOn_compact_product
      B L hLgap hLresolvent J Q k K hKcompact hKu hu Z hZcompact
      margin hmargin (hlimitMargin k hkOrder) epsilon hepsilon
  have hfinite : ∀ᶠ a in l, ∀ k ∈ Finset.range (order + 1),
      ∀ lambda ∈ K, ∀ z ∈ Z,
        |continuousLinearMapCharacteristicDeterminantLogAbs
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) z -
          continuousLinearMapCharacteristicDeterminantLogAbs
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda)) z| < epsilon := by
    change {a | ∀ k ∈ Finset.range (order + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
      |continuousLinearMapCharacteristicDeterminantLogAbs
          (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (F a) lambda)) z -
        continuousLinearMapCharacteristicDeterminantLogAbs
          (continuousLinearMapCompression J Q (_root_.iteratedDeriv k S.limitResolvent lambda)) z| < epsilon} ∈ l
    rw [show {a | ∀ k ∈ Finset.range (order + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
      |continuousLinearMapCharacteristicDeterminantLogAbs
          (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (F a) lambda)) z -
        continuousLinearMapCharacteristicDeterminantLogAbs
          (continuousLinearMapCompression J Q (_root_.iteratedDeriv k S.limitResolvent lambda)) z| < epsilon} =
      ⋂ k ∈ Finset.range (order + 1), {a | ∀ lambda ∈ K, ∀ z ∈ Z,
        |continuousLinearMapCharacteristicDeterminantLogAbs
            (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (F a) lambda)) z -
          continuousLinearMapCharacteristicDeterminantLogAbs
            (continuousLinearMapCompression J Q (_root_.iteratedDeriv k S.limitResolvent lambda)) z| < epsilon} by
      ext a
      simp]
    exact (Filter.biInter_finset_mem (Finset.range (order + 1))).2 hk
  filter_upwards [hfinite] with a ha
  intro k hkOrder
  exact ha k (Finset.mem_range.2 (Nat.lt_succ_iff.2 hkOrder))

/-- A complete finite Taylor jet of two-point characteristic determinant ratios
converges simultaneously under a uniform continuum denominator margin. -/
theorem iteratedDeriv_characteristicDeterminantRatio_finiteDimensionalCompression_tendsto_uniformOn_compact_product_jet
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (order : ℕ)
    (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < gap)
    (Z W : Set ℝ) (hZcompact : IsCompact Z) (hWcompact : IsCompact W)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ k ≤ order, ∀ lambda ∈ K, ∀ w ∈ W,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k S.limitResolvent lambda)) w|) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ k ≤ order, ∀ lambda ∈ K, ∀ z ∈ Z, ∀ w ∈ W,
        |continuousLinearMapCharacteristicDeterminantRatio
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) z w -
          continuousLinearMapCharacteristicDeterminantRatio
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda)) z w| < epsilon := by
  intro epsilon hepsilon
  have hk : ∀ k ∈ Finset.range (order + 1),
      ∀ᶠ a in l, ∀ lambda ∈ K, ∀ z ∈ Z, ∀ w ∈ W,
        |continuousLinearMapCharacteristicDeterminantRatio
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) z w -
          continuousLinearMapCharacteristicDeterminantRatio
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda)) z w| < epsilon := by
    intro k hkRange
    have hkOrder : k ≤ order := Nat.lt_succ_iff.mp (Finset.mem_range.mp hkRange)
    exact S.iteratedDeriv_characteristicDeterminantRatio_finiteDimensionalCompression_tendsto_uniformOn_compact_product
      B L hLgap hLresolvent J Q k K hKcompact hKu hu Z W hZcompact hWcompact
      margin hmargin (hlimitMargin k hkOrder) epsilon hepsilon
  have hfinite : ∀ᶠ a in l, ∀ k ∈ Finset.range (order + 1),
      ∀ lambda ∈ K, ∀ z ∈ Z, ∀ w ∈ W,
        |continuousLinearMapCharacteristicDeterminantRatio
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) z w -
          continuousLinearMapCharacteristicDeterminantRatio
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda)) z w| < epsilon := by
    change {a | ∀ k ∈ Finset.range (order + 1), ∀ lambda ∈ K, ∀ z ∈ Z, ∀ w ∈ W,
      |continuousLinearMapCharacteristicDeterminantRatio
          (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (F a) lambda)) z w -
        continuousLinearMapCharacteristicDeterminantRatio
          (continuousLinearMapCompression J Q (_root_.iteratedDeriv k S.limitResolvent lambda)) z w| < epsilon} ∈ l
    rw [show {a | ∀ k ∈ Finset.range (order + 1), ∀ lambda ∈ K, ∀ z ∈ Z, ∀ w ∈ W,
      |continuousLinearMapCharacteristicDeterminantRatio
          (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (F a) lambda)) z w -
        continuousLinearMapCharacteristicDeterminantRatio
          (continuousLinearMapCompression J Q (_root_.iteratedDeriv k S.limitResolvent lambda)) z w| < epsilon} =
      ⋂ k ∈ Finset.range (order + 1), {a | ∀ lambda ∈ K, ∀ z ∈ Z, ∀ w ∈ W,
        |continuousLinearMapCharacteristicDeterminantRatio
            (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (F a) lambda)) z w -
          continuousLinearMapCharacteristicDeterminantRatio
            (continuousLinearMapCompression J Q (_root_.iteratedDeriv k S.limitResolvent lambda)) z w| < epsilon} by
      ext a
      simp]
    exact (Filter.biInter_finset_mem (Finset.range (order + 1))).2 hk
  filter_upwards [hfinite] with a ha
  intro k hkOrder
  exact ha k (Finset.mem_range.2 (Nat.lt_succ_iff.2 hkOrder))

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
