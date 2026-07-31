import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalCharacteristicDeterminantCore
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

/-- The complete real characteristic determinant profile of a compressed fixed
Taylor derivative converges uniformly on the product of a compact strict-subgap
Taylor set and a compact real spectral-parameter set. -/
theorem iteratedDeriv_characteristicDeterminant_finiteDimensionalCompression_tendsto_uniformOn_compact_product
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (k : ℕ)
    (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < gap)
    (Z : Set ℝ) (hZcompact : IsCompact Z) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ lambda ∈ K, ∀ z ∈ Z,
        |continuousLinearMapCharacteristicDeterminant
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) z -
          continuousLinearMapCharacteristicDeterminant
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda)) z| < epsilon := by
  let R : ℝ :=
    ‖Q‖ * ((k.factorial : ℝ) * (gap - u)⁻¹ ^ (k + 1)) * ‖J‖
  have hmargin : 0 < gap - u := sub_pos.mpr hu
  have hinv : 0 ≤ (gap - u)⁻¹ := inv_nonneg.mpr hmargin.le
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
    finiteDimensional_characteristicDeterminant_tendsto_uniformOn_compactRealParameter
      (l := l) (s := K)
      (fun a lambda => continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k (F a) lambda))
      (fun lambda => continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k S.limitResolvent lambda))
      R hR hlimit hoperator Z hZcompact

/-- Every finite vector of real characteristic determinant samples of a
compressed Taylor derivative converges compact-uniformly. -/
theorem iteratedDeriv_characteristicDeterminantSampleJet_finiteDimensionalCompression_tendsto_uniformOn_compact
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    {sampleOrder : ℕ} (sample : Fin (sampleOrder + 1) → ℝ)
    (k : ℕ) (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < gap) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ lambda ∈ K,
        ‖continuousLinearMapCharacteristicDeterminantSampleJet sample
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) -
          continuousLinearMapCharacteristicDeterminantSampleJet sample
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda))‖ < epsilon := by
  exact
    S.iteratedDeriv_continuousObservable_finiteDimensionalCompression_tendsto_uniformOn_compact
      B L hLgap hLresolvent J Q
      (continuousLinearMapCharacteristicDeterminantSampleJet sample)
      (continuous_continuousLinearMapCharacteristicDeterminantSampleJet sample)
      k K hKcompact hKu hu

/-- A complete finite Taylor jet of characteristic determinant profiles
converges simultaneously on compact Taylor and real spectral sets. -/
theorem iteratedDeriv_characteristicDeterminant_finiteDimensionalCompression_tendsto_uniformOn_compact_product_jet
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (order : ℕ)
    (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < gap)
    (Z : Set ℝ) (hZcompact : IsCompact Z) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ k ≤ order, ∀ lambda ∈ K, ∀ z ∈ Z,
        |continuousLinearMapCharacteristicDeterminant
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) z -
          continuousLinearMapCharacteristicDeterminant
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda)) z| < epsilon := by
  intro epsilon hepsilon
  have hk : ∀ k ∈ Finset.range (order + 1),
      ∀ᶠ a in l, ∀ lambda ∈ K, ∀ z ∈ Z,
        |continuousLinearMapCharacteristicDeterminant
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) z -
          continuousLinearMapCharacteristicDeterminant
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda)) z| < epsilon := by
    intro k hk
    exact
      S.iteratedDeriv_characteristicDeterminant_finiteDimensionalCompression_tendsto_uniformOn_compact_product
        B L hLgap hLresolvent J Q k K hKcompact hKu hu Z hZcompact
        epsilon hepsilon
  have hfinite : ∀ᶠ a in l, ∀ k ∈ Finset.range (order + 1),
      ∀ lambda ∈ K, ∀ z ∈ Z,
        |continuousLinearMapCharacteristicDeterminant
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) z -
          continuousLinearMapCharacteristicDeterminant
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda)) z| < epsilon := by
    change {a | ∀ k ∈ Finset.range (order + 1),
      ∀ lambda ∈ K, ∀ z ∈ Z,
        |continuousLinearMapCharacteristicDeterminant
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) z -
          continuousLinearMapCharacteristicDeterminant
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda)) z| < epsilon} ∈ l
    rw [show {a | ∀ k ∈ Finset.range (order + 1),
      ∀ lambda ∈ K, ∀ z ∈ Z,
        |continuousLinearMapCharacteristicDeterminant
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) z -
          continuousLinearMapCharacteristicDeterminant
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda)) z| < epsilon} =
      ⋂ k ∈ Finset.range (order + 1), {a | ∀ lambda ∈ K, ∀ z ∈ Z,
        |continuousLinearMapCharacteristicDeterminant
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) z -
          continuousLinearMapCharacteristicDeterminant
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda)) z| < epsilon} by
      ext a
      simp]
    exact (Filter.biInter_finset_mem (Finset.range (order + 1))).2
      fun k hk' => hk k hk'
  filter_upwards [hfinite] with a ha
  intro k hkOrder
  exact ha k (Finset.mem_range.2 (Nat.lt_succ_iff.2 hkOrder))

/-- A uniform positive continuum margin is inherited by a compressed fixed
Taylor derivative, uniformly on the compact Taylor × real spectral product. -/
theorem iteratedDeriv_characteristicDeterminant_finiteDimensionalCompression_eventually_abs_gt_half_margin
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
    ∀ᶠ a in l, ∀ lambda ∈ K, ∀ z ∈ Z,
      margin / 2 < |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k (F a) lambda)) z| := by
  have hconv :=
    S.iteratedDeriv_characteristicDeterminant_finiteDimensionalCompression_tendsto_uniformOn_compact_product
      B L hLgap hLresolvent J Q k K hKcompact hKu hu Z hZcompact
      (margin / 2) (half_pos hmargin)
  filter_upwards [hconv] with a ha
  intro lambda hlambda z hz
  let x := continuousLinearMapCharacteristicDeterminant
    (continuousLinearMapCompression J Q
      (_root_.iteratedDeriv k (F a) lambda)) z
  let y := continuousLinearMapCharacteristicDeterminant
    (continuousLinearMapCompression J Q
      (_root_.iteratedDeriv k S.limitResolvent lambda)) z
  have hxy : |x - y| < margin / 2 := ha lambda hlambda z hz
  have hy : margin ≤ |y| := hlimitMargin lambda hlambda z hz
  have hyx : |y| ≤ |x - y| + |x| := by
    calc
      |y| = |(y - x) + x| := by ring_nf
      _ ≤ |y - x| + |x| := abs_add _ _
      _ = |x - y| + |x| := by rw [abs_sub_comm]
  linarith

/-- The same positive margin gives eventual real characteristic zero-exclusion
for every compressed approximating Taylor derivative. -/
theorem iteratedDeriv_characteristicDeterminant_finiteDimensionalCompression_eventually_ne_zero
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
    ∀ᶠ a in l, ∀ lambda ∈ K, ∀ z ∈ Z,
      continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k (F a) lambda)) z ≠ 0 := by
  have h :=
    S.iteratedDeriv_characteristicDeterminant_finiteDimensionalCompression_eventually_abs_gt_half_margin
      B L hLgap hLresolvent J Q k K hKcompact hKu hu Z hZcompact
      margin hmargin hlimitMargin
  filter_upwards [h] with a ha
  intro lambda hlambda z hz
  exact abs_pos.mp (lt_trans (half_pos hmargin) (ha lambda hlambda z hz))

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
