import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventStabilityCore
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

/-- On a compact strict-subgap Taylor set and an arbitrary real spectral set,
a positive continuum characteristic-determinant margin together with a uniform
continuum compressed-resolvent bound yields eventual unit stability, a uniform
approximating inverse bound, and operator-norm convergence of the true
finite-dimensional real resolvents. -/
theorem iteratedDeriv_realResolvent_finiteDimensionalCompression_eventually_stable_uniformOn_compact_product
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (k : ℕ)
    (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < gap)
    (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ lambda ∈ K, ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k S.limitResolvent lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitResolventNorm : ∀ lambda ∈ K, ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k S.limitResolvent lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ lambda ∈ K, ∀ z ∈ Z,
        IsUnit (continuousLinearMapRealShift
          (continuousLinearMapCompression J Q
            (_root_.iteratedDeriv k (F a) lambda)) z) ∧
        continuousLinearMapRealResolventNorm
          (continuousLinearMapCompression J Q
            (_root_.iteratedDeriv k (F a) lambda)) z ≤ 2 * (M + 1) ∧
        ‖continuousLinearMapRealResolvent
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) z -
          continuousLinearMapRealResolvent
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda)) z‖ < epsilon := by
  have hoperator :=
    S.iteratedDeriv_tendsto_uniformOn_compact_finiteDimensionalCompression
      B L hLgap hLresolvent J Q k K hKcompact hKu hu
  exact finiteDimensional_realResolvent_eventually_stable
    (l := l) (s := K)
    (fun a lambda => continuousLinearMapCompression J Q
      (_root_.iteratedDeriv k (F a) lambda))
    (fun lambda => continuousLinearMapCompression J Q
      (_root_.iteratedDeriv k S.limitResolvent lambda))
    hoperator Z margin hmargin hlimitMargin M hM hlimitResolventNorm

/-- Compact-uniform convergence of the operator-valued real resolvents of a
compressed fixed Taylor derivative. -/
theorem iteratedDeriv_realResolvent_finiteDimensionalCompression_tendsto_uniformOn_compact_product
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (k : ℕ)
    (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < gap)
    (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ lambda ∈ K, ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k S.limitResolvent lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitResolventNorm : ∀ lambda ∈ K, ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k S.limitResolvent lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ lambda ∈ K, ∀ z ∈ Z,
        ‖continuousLinearMapRealResolvent
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) z -
          continuousLinearMapRealResolvent
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda)) z‖ < epsilon := by
  intro epsilon hepsilon
  have h := S.iteratedDeriv_realResolvent_finiteDimensionalCompression_eventually_stable_uniformOn_compact_product
    B L hLgap hLresolvent J Q k K hKcompact hKu hu Z
    margin hmargin hlimitMargin M hM hlimitResolventNorm epsilon hepsilon
  filter_upwards [h] with a ha
  exact fun lambda hlambda z hz => (ha lambda hlambda z hz).2.2

/-- Eventual compact-uniform inclusion of the real spectral set in the
resolvent set of every compressed approximating Taylor derivative. -/
theorem iteratedDeriv_finiteDimensionalCompression_eventually_mem_realResolventSet_uniformOn_compact_product
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (k : ℕ)
    (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < gap)
    (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ lambda ∈ K, ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k S.limitResolvent lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitResolventNorm : ∀ lambda ∈ K, ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k S.limitResolvent lambda)) z ≤ M) :
    ∀ᶠ a in l, ∀ lambda ∈ K, ∀ z ∈ Z,
      z ∈ resolventSet ℝ
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k (F a) lambda)) := by
  have h := S.iteratedDeriv_realResolvent_finiteDimensionalCompression_eventually_stable_uniformOn_compact_product
    B L hLgap hLresolvent J Q k K hKcompact hKu hu Z
    margin hmargin hlimitMargin M hM hlimitResolventNorm 1 zero_lt_one
  filter_upwards [h] with a ha
  intro lambda hlambda z hz
  exact continuousLinearMap_mem_real_resolventSet_of_isUnit _ _
    (ha lambda hlambda z hz).1

/-- Eventual compact-uniform exclusion from the real operator-norm
pseudospectrum at the explicit level `2 (M + 1)`. -/
theorem iteratedDeriv_finiteDimensionalCompression_eventually_not_mem_realPseudospectrum_uniformOn_compact_product
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (k : ℕ)
    (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < gap)
    (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ lambda ∈ K, ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k S.limitResolvent lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitResolventNorm : ∀ lambda ∈ K, ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k S.limitResolvent lambda)) z ≤ M) :
    ∀ᶠ a in l, ∀ lambda ∈ K, ∀ z ∈ Z,
      z ∉ continuousLinearMapRealPseudospectrum (2 * (M + 1))
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k (F a) lambda)) := by
  have h := S.iteratedDeriv_realResolvent_finiteDimensionalCompression_eventually_stable_uniformOn_compact_product
    B L hLgap hLresolvent J Q k K hKcompact hKu hu Z
    margin hmargin hlimitMargin M hM hlimitResolventNorm 1 zero_lt_one
  filter_upwards [h] with a ha
  intro lambda hlambda z hz
  exact continuousLinearMap_not_mem_realPseudospectrum_of_isUnit_of_norm_le
    (ha lambda hlambda z hz).1 (ha lambda hlambda z hz).2.1

/-- Simultaneous real-resolvent stability for every Taylor derivative up to a
fixed finite order. -/
theorem iteratedDeriv_realResolvent_finiteDimensionalCompression_eventually_stable_uniformOn_compact_product_jet
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (order : ℕ)
    (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < gap)
    (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ k ≤ order, ∀ lambda ∈ K, ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k S.limitResolvent lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitResolventNorm : ∀ k ≤ order, ∀ lambda ∈ K, ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k S.limitResolvent lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ a in l, ∀ k ≤ order, ∀ lambda ∈ K, ∀ z ∈ Z,
        IsUnit (continuousLinearMapRealShift
          (continuousLinearMapCompression J Q
            (_root_.iteratedDeriv k (F a) lambda)) z) ∧
        continuousLinearMapRealResolventNorm
          (continuousLinearMapCompression J Q
            (_root_.iteratedDeriv k (F a) lambda)) z ≤ 2 * (M + 1) ∧
        ‖continuousLinearMapRealResolvent
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) z -
          continuousLinearMapRealResolvent
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda)) z‖ < epsilon := by
  intro epsilon hepsilon
  have hk : ∀ k ∈ Finset.range (order + 1),
      ∀ᶠ a in l, ∀ lambda ∈ K, ∀ z ∈ Z,
        IsUnit (continuousLinearMapRealShift
          (continuousLinearMapCompression J Q
            (_root_.iteratedDeriv k (F a) lambda)) z) ∧
        continuousLinearMapRealResolventNorm
          (continuousLinearMapCompression J Q
            (_root_.iteratedDeriv k (F a) lambda)) z ≤ 2 * (M + 1) ∧
        ‖continuousLinearMapRealResolvent
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) z -
          continuousLinearMapRealResolvent
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda)) z‖ < epsilon := by
    intro k hk
    have hkOrder : k ≤ order := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    exact S.iteratedDeriv_realResolvent_finiteDimensionalCompression_eventually_stable_uniformOn_compact_product
      B L hLgap hLresolvent J Q k K hKcompact hKu hu Z
      margin hmargin (hlimitMargin k hkOrder) M hM
      (hlimitResolventNorm k hkOrder) epsilon hepsilon
  have hfinite : ∀ᶠ a in l, ∀ k ∈ Finset.range (order + 1),
      ∀ lambda ∈ K, ∀ z ∈ Z,
        IsUnit (continuousLinearMapRealShift
          (continuousLinearMapCompression J Q
            (_root_.iteratedDeriv k (F a) lambda)) z) ∧
        continuousLinearMapRealResolventNorm
          (continuousLinearMapCompression J Q
            (_root_.iteratedDeriv k (F a) lambda)) z ≤ 2 * (M + 1) ∧
        ‖continuousLinearMapRealResolvent
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) z -
          continuousLinearMapRealResolvent
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda)) z‖ < epsilon := by
    change {a | ∀ k ∈ Finset.range (order + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
      IsUnit (continuousLinearMapRealShift
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k (F a) lambda)) z) ∧
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k (F a) lambda)) z ≤ 2 * (M + 1) ∧
      ‖continuousLinearMapRealResolvent
          (continuousLinearMapCompression J Q
            (_root_.iteratedDeriv k (F a) lambda)) z -
        continuousLinearMapRealResolvent
          (continuousLinearMapCompression J Q
            (_root_.iteratedDeriv k S.limitResolvent lambda)) z‖ < epsilon} ∈ l
    rw [show {a | ∀ k ∈ Finset.range (order + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
      IsUnit (continuousLinearMapRealShift
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k (F a) lambda)) z) ∧
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k (F a) lambda)) z ≤ 2 * (M + 1) ∧
      ‖continuousLinearMapRealResolvent
          (continuousLinearMapCompression J Q
            (_root_.iteratedDeriv k (F a) lambda)) z -
        continuousLinearMapRealResolvent
          (continuousLinearMapCompression J Q
            (_root_.iteratedDeriv k S.limitResolvent lambda)) z‖ < epsilon} =
      ⋂ k ∈ Finset.range (order + 1), {a | ∀ lambda ∈ K, ∀ z ∈ Z,
        IsUnit (continuousLinearMapRealShift
          (continuousLinearMapCompression J Q
            (_root_.iteratedDeriv k (F a) lambda)) z) ∧
        continuousLinearMapRealResolventNorm
          (continuousLinearMapCompression J Q
            (_root_.iteratedDeriv k (F a) lambda)) z ≤ 2 * (M + 1) ∧
        ‖continuousLinearMapRealResolvent
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) z -
          continuousLinearMapRealResolvent
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda)) z‖ < epsilon} by
      ext a
      simp]
    exact (Filter.biInter_finset_mem (Finset.range (order + 1))).2
      fun k hk' => hk k hk'
  filter_upwards [hfinite] with a ha
  intro k hkOrder
  exact ha k (Finset.mem_range.2 (Nat.lt_succ_iff.2 hkOrder))

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
