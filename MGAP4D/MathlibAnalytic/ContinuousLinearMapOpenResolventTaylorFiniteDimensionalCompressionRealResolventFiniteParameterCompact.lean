import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventFiniteParameterResponse
import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventOperatorSymmetricMultilinearCompact
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

namespace ContinuousLinearMapOpenTaylorStrongLimitData

variable {α E V : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [FiniteDimensional ℝ V]

/-- Compact-uniform convergence of a fixed finite-parameter mixed resolvent
derivative after arbitrary finite-dimensional compression. -/
theorem iteratedDeriv_realResolventFiniteParameterSymmetricDerivative_finiteDimensionalCompression_tendsto_uniformOn_compact_product
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (k parameterDimension mixedOrder : ℕ)
    (H : Fin parameterDimension → (V →L[ℝ] V))
    (u : Fin mixedOrder → (Fin parameterDimension → ℝ))
    (K : Set ℝ) (hKcompact : IsCompact K) {upper : ℝ}
    (hKupper : K ⊆ Set.Iic upper) (hupper : upper < gap) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ lambda ∈ K, ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant
      (continuousLinearMapCompression J Q (_root_.iteratedDeriv k S.limitResolvent lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ lambda ∈ K, ∀ z ∈ Z, continuousLinearMapRealResolventNorm
      (continuousLinearMapCompression J Q (_root_.iteratedDeriv k S.limitResolvent lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l, ∀ lambda ∈ K, ∀ z ∈ Z,
      ‖continuousLinearMapFiniteParameterRealResolventSymmetricDerivative parameterDimension mixedOrder
          (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (F a) lambda)) H z u -
        continuousLinearMapFiniteParameterRealResolventSymmetricDerivative parameterDimension mixedOrder
          (continuousLinearMapCompression J Q (_root_.iteratedDeriv k S.limitResolvent lambda)) H z u‖ < epsilon := by
  simpa only [continuousLinearMapFiniteParameterRealResolventSymmetricDerivative_apply] using
    S.iteratedDeriv_realResolventOperatorSymmetricDerivative_finiteDimensionalCompression_tendsto_uniformOn_compact_product
      B L hLgap hLresolvent J Q k mixedOrder
      (continuousLinearMapFiniteParameterDirectionTuple parameterDimension mixedOrder H u)
      K hKcompact hKupper hupper Z margin hmargin hlimitMargin M hM hlimitNorm

/-- Simultaneous compact-uniform convergence on the finite rectangle of
Taylor derivative orders and finite-parameter mixed derivative orders. -/
theorem iteratedDeriv_realResolventFiniteParameterSymmetricDerivative_finiteDimensionalCompression_tendsto_uniformOn_compact_product_rectangular
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (parameterDimension taylorOrder mixedOrder : ℕ)
    (H : Fin parameterDimension → (V →L[ℝ] V))
    (u : ∀ n : Fin (mixedOrder + 1), Fin n.1 → (Fin parameterDimension → ℝ))
    (K : Set ℝ) (hKcompact : IsCompact K) {upper : ℝ}
    (hKupper : K ⊆ Set.Iic upper) (hupper : upper < gap) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q (_root_.iteratedDeriv k.1 S.limitResolvent lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q (_root_.iteratedDeriv k.1 S.limitResolvent lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l, ∀ k : Fin (taylorOrder + 1),
      ∀ n : Fin (mixedOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
        ‖continuousLinearMapFiniteParameterRealResolventSymmetricDerivative parameterDimension n.1
            (continuousLinearMapCompression J Q (_root_.iteratedDeriv k.1 (F a) lambda)) H z (u n) -
          continuousLinearMapFiniteParameterRealResolventSymmetricDerivative parameterDimension n.1
            (continuousLinearMapCompression J Q (_root_.iteratedDeriv k.1 S.limitResolvent lambda)) H z (u n)‖ < epsilon := by
  simpa only [continuousLinearMapFiniteParameterRealResolventSymmetricDerivative_apply] using
    S.iteratedDeriv_realResolventOperatorSymmetricDerivative_finiteDimensionalCompression_tendsto_uniformOn_compact_product_rectangular
      B L hLgap hLresolvent J Q taylorOrder mixedOrder
      (fun n => continuousLinearMapFiniteParameterDirectionTuple parameterDimension n.1 H (u n))
      K hKcompact hKupper hupper Z margin hmargin hlimitMargin M hM hlimitNorm

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
