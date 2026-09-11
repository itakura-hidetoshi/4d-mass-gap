import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterMultilinearJetBanachCore
import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterMultilinearJetDirectionFamilyCompact
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic
namespace ContinuousLinearMapOpenTaylorStrongLimitData

set_option maxHeartbeats 5000000

variable {α E V : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Compact-uniform convergence of the complete moving-direction carrier
rectangle in its genuine finite dependent-product norm. -/
theorem iteratedDeriv_realResolventJointMultilinearCarrierRectangularJet_finiteDimensionalCompression_tendsto_uniformOn_compact_product_directionFamily_norm
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (taylorOrder mixedOrder m : ℕ)
    (H : α → Fin m → (V →L[ℝ] V)) (H0 : Fin m → (V →L[ℝ] V))
    (hH : Tendsto H l (𝓝 H0)) (K : Set ℝ) (hKcompact : IsCompact K)
    {upper : ℝ} (hKupper : K ⊆ Set.Iic upper) (hupper : upper < gap)
    (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k.1 S.limitResolvent lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k.1 S.limitResolvent lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l, ∀ lambda ∈ K, ∀ z ∈ Z,
      ‖continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierRectangularJetFromResolventFamily
          m taylorOrder mixedOrder (H a)
          (continuousLinearMapCompressedIteratedDerivRealResolventFamily
            J Q taylorOrder (F a) lambda z) -
        continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierRectangularJetFromResolventFamily
          m taylorOrder mixedOrder H0
          (continuousLinearMapCompressedIteratedDerivRealResolventFamily
            J Q taylorOrder S.limitResolvent lambda z)‖ < epsilon := by
  intro epsilon hepsilon
  have h :=
    S.iteratedDeriv_realResolventJointMultilinearCarrierRectangularJet_finiteDimensionalCompression_tendsto_uniformOn_compact_product_directionFamily_sup
      B L hLgap hLresolvent J Q taylorOrder mixedOrder m H H0 hH K hKcompact
      hKupper hupper Z margin hmargin hlimitMargin M hM hlimitNorm epsilon hepsilon
  filter_upwards [h] with a ha
  intro lambda hlambda z hz
  apply (continuousLinearMapJointMultilinearCarrierRectangularJet_norm_sub_lt_iff_supDistance_lt
    _ _ hepsilon).2
  exact ha lambda hlambda z hz

variable {W : Type*}
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Compact-uniform convergence of every Banach-valued complete response
rectangle in the genuine finite dependent-product norm. -/
theorem iteratedDeriv_realResolventJointMultilinearResponseCarrierRectangularJet_finiteDimensionalCompression_tendsto_uniformOn_compact_product_directionFamily_norm
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (φ : (V →L[ℝ] V) →L[ℝ] W)
    (taylorOrder mixedOrder m : ℕ) (H : α → Fin m → (V →L[ℝ] V))
    (H0 : Fin m → (V →L[ℝ] V)) (hH : Tendsto H l (𝓝 H0))
    (K : Set ℝ) (hKcompact : IsCompact K) {upper : ℝ}
    (hKupper : K ⊆ Set.Iic upper) (hupper : upper < gap)
    (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k.1 S.limitResolvent lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k.1 S.limitResolvent lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l, ∀ lambda ∈ K, ∀ z ∈ Z,
      ‖continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierRectangularJetFromResolventFamily
          φ m taylorOrder mixedOrder (H a)
          (continuousLinearMapCompressedIteratedDerivRealResolventFamily
            J Q taylorOrder (F a) lambda z) -
        continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierRectangularJetFromResolventFamily
          φ m taylorOrder mixedOrder H0
          (continuousLinearMapCompressedIteratedDerivRealResolventFamily
            J Q taylorOrder S.limitResolvent lambda z)‖ < epsilon := by
  intro epsilon hepsilon
  have h :=
    S.iteratedDeriv_realResolventJointMultilinearResponseCarrierRectangularJet_finiteDimensionalCompression_tendsto_uniformOn_compact_product_directionFamily_sup
      B L hLgap hLresolvent J Q φ taylorOrder mixedOrder m H H0 hH K hKcompact
      hKupper hupper Z margin hmargin hlimitMargin M hM hlimitNorm epsilon hepsilon
  filter_upwards [h] with a ha
  intro lambda hlambda z hz
  apply (continuousLinearMapJointMultilinearCarrierRectangularJet_norm_sub_lt_iff_supDistance_lt
    _ _ hepsilon).2
  exact ha lambda hlambda z hz

/-- Compact-uniform convergence of the complete basis-independent trace
rectangle in its genuine finite dependent-product norm. -/
theorem iteratedDeriv_realResolventJointMultilinearTraceCarrierRectangularJet_finiteDimensionalCompression_tendsto_uniformOn_compact_product_directionFamily_norm
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (taylorOrder mixedOrder m : ℕ)
    (H : α → Fin m → (V →L[ℝ] V)) (H0 : Fin m → (V →L[ℝ] V))
    (hH : Tendsto H l (𝓝 H0)) (K : Set ℝ) (hKcompact : IsCompact K)
    {upper : ℝ} (hKupper : K ⊆ Set.Iic upper) (hupper : upper < gap)
    (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k.1 S.limitResolvent lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k.1 S.limitResolvent lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l, ∀ lambda ∈ K, ∀ z ∈ Z,
      ‖continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierRectangularJetFromResolventFamily
          V m taylorOrder mixedOrder (H a)
          (continuousLinearMapCompressedIteratedDerivRealResolventFamily
            J Q taylorOrder (F a) lambda z) -
        continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierRectangularJetFromResolventFamily
          V m taylorOrder mixedOrder H0
          (continuousLinearMapCompressedIteratedDerivRealResolventFamily
            J Q taylorOrder S.limitResolvent lambda z)‖ < epsilon := by
  intro epsilon hepsilon
  have h :=
    S.iteratedDeriv_realResolventJointMultilinearTraceCarrierRectangularJet_finiteDimensionalCompression_tendsto_uniformOn_compact_product_directionFamily_sup
      B L hLgap hLresolvent J Q taylorOrder mixedOrder m H H0 hH K hKcompact
      hKupper hupper Z margin hmargin hlimitMargin M hM hlimitNorm epsilon hepsilon
  filter_upwards [h] with a ha
  intro lambda hlambda z hz
  apply (continuousLinearMapJointMultilinearCarrierRectangularJet_norm_sub_lt_iff_supDistance_lt
    _ _ hepsilon).2
  exact ha lambda hlambda z hz

end ContinuousLinearMapOpenTaylorStrongLimitData
end MathlibAnalytic
end MGAP4D
