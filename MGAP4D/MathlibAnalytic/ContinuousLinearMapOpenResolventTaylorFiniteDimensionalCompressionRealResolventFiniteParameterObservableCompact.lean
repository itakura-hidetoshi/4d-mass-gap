import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventFiniteParameterObservable
import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventFiniteParameterCompact
import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventFiniteParameterTaylorDysonCompact
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

namespace ContinuousLinearMapOpenTaylorStrongLimitData

variable {α E V W : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Compact-uniform convergence of an arbitrary continuous-linear observation
of a fixed finite-parameter mixed Fréchet derivative. -/
theorem iteratedDeriv_realResolventFiniteParameterMixedResponse_tendsto_uniformOn_compact
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (φ : (V →L[ℝ] V) →L[ℝ] W)
    (k parameterDimension mixedOrder : ℕ) (H : Fin parameterDimension → (V →L[ℝ] V))
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
      ‖continuousLinearMapFiniteParameterRealResolventSymmetricDerivativeLinearResponse φ parameterDimension mixedOrder
          (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (F a) lambda)) H z u -
        continuousLinearMapFiniteParameterRealResolventSymmetricDerivativeLinearResponse φ parameterDimension mixedOrder
          (continuousLinearMapCompression J Q (_root_.iteratedDeriv k S.limitResolvent lambda)) H z u‖ < epsilon := by
  intro epsilon hepsilon
  have hdelta : 0 < epsilon / (‖φ‖ + 1) := div_pos hepsilon (by positivity)
  filter_upwards [
    S.iteratedDeriv_realResolventFiniteParameterSymmetricDerivative_finiteDimensionalCompression_tendsto_uniformOn_compact_product
      B L hLgap hLresolvent J Q k parameterDimension mixedOrder H u
      K hKcompact hKupper hupper Z margin hmargin hlimitMargin M hM hlimitNorm
      (epsilon / (‖φ‖ + 1)) hdelta] with a ha
  intro lambda hlambda z hz
  simpa only [continuousLinearMapFiniteParameterRealResolventSymmetricDerivativeLinearResponse_apply] using
    continuousLinearMap_map_sub_norm_lt_of_norm_sub_lt φ hepsilon (ha lambda hlambda z hz)

/-- Simultaneous compact-uniform convergence of arbitrary observed mixed
Fréchet derivatives on a finite ambient-order by mixed-order rectangle. -/
theorem iteratedDeriv_realResolventFiniteParameterMixedResponse_tendsto_uniformOn_compact_rectangular
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (φ : (V →L[ℝ] V) →L[ℝ] W)
    (parameterDimension taylorOrder mixedOrder : ℕ) (H : Fin parameterDimension → (V →L[ℝ] V))
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
        ‖continuousLinearMapFiniteParameterRealResolventSymmetricDerivativeLinearResponse φ parameterDimension n.1
            (continuousLinearMapCompression J Q (_root_.iteratedDeriv k.1 (F a) lambda)) H z (u n) -
          continuousLinearMapFiniteParameterRealResolventSymmetricDerivativeLinearResponse φ parameterDimension n.1
            (continuousLinearMapCompression J Q (_root_.iteratedDeriv k.1 S.limitResolvent lambda)) H z (u n)‖ < epsilon := by
  intro epsilon hepsilon
  have hdelta : 0 < epsilon / (‖φ‖ + 1) := div_pos hepsilon (by positivity)
  filter_upwards [
    S.iteratedDeriv_realResolventFiniteParameterSymmetricDerivative_finiteDimensionalCompression_tendsto_uniformOn_compact_product_rectangular
      B L hLgap hLresolvent J Q parameterDimension taylorOrder mixedOrder H u
      K hKcompact hKupper hupper Z margin hmargin hlimitMargin M hM hlimitNorm
      (epsilon / (‖φ‖ + 1)) hdelta] with a ha
  intro k n lambda hlambda z hz
  simpa only [continuousLinearMapFiniteParameterRealResolventSymmetricDerivativeLinearResponse_apply] using
    continuousLinearMap_map_sub_norm_lt_of_norm_sub_lt φ hepsilon (ha k n lambda hlambda z hz)

/-- Compact-uniform convergence of an arbitrary continuous-linear observation
of a fixed normalized finite-parameter Taylor-Dyson coefficient. -/
theorem iteratedDeriv_realResolventFiniteParameterTaylorResponse_tendsto_uniformOn_compact
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (φ : (V →L[ℝ] V) →L[ℝ] W)
    (k parameterOrder parameterDimension : ℕ) (H : Fin parameterDimension → (V →L[ℝ] V))
    (h : Fin parameterDimension → ℝ) (K : Set ℝ) (hKcompact : IsCompact K) {upper : ℝ}
    (hKupper : K ⊆ Set.Iic upper) (hupper : upper < gap) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ lambda ∈ K, ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant
      (continuousLinearMapCompression J Q (_root_.iteratedDeriv k S.limitResolvent lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ lambda ∈ K, ∀ z ∈ Z, continuousLinearMapRealResolventNorm
      (continuousLinearMapCompression J Q (_root_.iteratedDeriv k S.limitResolvent lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l, ∀ lambda ∈ K, ∀ z ∈ Z,
      ‖continuousLinearMapFiniteParameterRealResolventTaylorDysonResponse φ parameterOrder parameterDimension
          (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (F a) lambda)) H z 0 h -
        continuousLinearMapFiniteParameterRealResolventTaylorDysonResponse φ parameterOrder parameterDimension
          (continuousLinearMapCompression J Q (_root_.iteratedDeriv k S.limitResolvent lambda)) H z 0 h‖ < epsilon := by
  intro epsilon hepsilon
  have hdelta : 0 < epsilon / (‖φ‖ + 1) := div_pos hepsilon (by positivity)
  filter_upwards [
    S.iteratedDeriv_realResolventFiniteParameterTaylorDysonCoefficient_finiteDimensionalCompression_tendsto_uniformOn_compact_product
      B L hLgap hLresolvent J Q k parameterOrder parameterDimension H h
      K hKcompact hKupper hupper Z margin hmargin hlimitMargin M hM hlimitNorm
      (epsilon / (‖φ‖ + 1)) hdelta] with a ha
  intro lambda hlambda z hz
  simpa only [continuousLinearMapFiniteParameterRealResolventTaylorDysonResponse_apply] using
    continuousLinearMap_map_sub_norm_lt_of_norm_sub_lt φ hepsilon (ha lambda hlambda z hz)

/-- Simultaneous compact-uniform convergence of a complete finite observed
Taylor-Dyson jet on the ambient-order by parameter-order rectangle. -/
theorem iteratedDeriv_realResolventFiniteParameterTaylorResponse_tendsto_uniformOn_compact_rectangular
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (φ : (V →L[ℝ] V) →L[ℝ] W)
    (taylorOrder parameterOrder parameterDimension : ℕ)
    (H : Fin parameterDimension → (V →L[ℝ] V)) (h : Fin parameterDimension → ℝ)
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
      ∀ n : Fin (parameterOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
        ‖continuousLinearMapFiniteParameterRealResolventTaylorDysonResponse φ n.1 parameterDimension
            (continuousLinearMapCompression J Q (_root_.iteratedDeriv k.1 (F a) lambda)) H z 0 h -
          continuousLinearMapFiniteParameterRealResolventTaylorDysonResponse φ n.1 parameterDimension
            (continuousLinearMapCompression J Q (_root_.iteratedDeriv k.1 S.limitResolvent lambda)) H z 0 h‖ < epsilon := by
  intro epsilon hepsilon
  have hdelta : 0 < epsilon / (‖φ‖ + 1) := div_pos hepsilon (by positivity)
  filter_upwards [
    S.iteratedDeriv_realResolventFiniteParameterTaylorDysonCoefficient_finiteDimensionalCompression_tendsto_uniformOn_compact_product_rectangular
      B L hLgap hLresolvent J Q taylorOrder parameterOrder parameterDimension H h
      K hKcompact hKupper hupper Z margin hmargin hlimitMargin M hM hlimitNorm
      (epsilon / (‖φ‖ + 1)) hdelta] with a ha
  intro k n lambda hlambda z hz
  simpa only [continuousLinearMapFiniteParameterRealResolventTaylorDysonResponse_apply] using
    continuousLinearMap_map_sub_norm_lt_of_norm_sub_lt φ hepsilon (ha k n lambda hlambda z hz)

/-- Compact-uniform convergence of the basis-independent trace of a fixed
finite-parameter Taylor-Dyson coefficient. -/
theorem iteratedDeriv_realResolventFiniteParameterTaylorTrace_tendsto_uniformOn_compact
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (k parameterOrder parameterDimension : ℕ)
    (H : Fin parameterDimension → (V →L[ℝ] V)) (h : Fin parameterDimension → ℝ)
    (K : Set ℝ) (hKcompact : IsCompact K) {upper : ℝ}
    (hKupper : K ⊆ Set.Iic upper) (hupper : upper < gap) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ lambda ∈ K, ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant
      (continuousLinearMapCompression J Q (_root_.iteratedDeriv k S.limitResolvent lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ lambda ∈ K, ∀ z ∈ Z, continuousLinearMapRealResolventNorm
      (continuousLinearMapCompression J Q (_root_.iteratedDeriv k S.limitResolvent lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l, ∀ lambda ∈ K, ∀ z ∈ Z,
      |continuousLinearMapFiniteParameterRealResolventTaylorDysonTraceCoefficient V parameterOrder parameterDimension
          (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (F a) lambda)) H z 0 h -
        continuousLinearMapFiniteParameterRealResolventTaylorDysonTraceCoefficient V parameterOrder parameterDimension
          (continuousLinearMapCompression J Q (_root_.iteratedDeriv k S.limitResolvent lambda)) H z 0 h| < epsilon := by
  simpa [Real.norm_eq_abs, continuousLinearMapFiniteParameterRealResolventTaylorDysonTraceCoefficient] using
    S.iteratedDeriv_realResolventFiniteParameterTaylorResponse_tendsto_uniformOn_compact
      B L hLgap hLresolvent J Q (continuousLinearMapTrace (V := V))
      k parameterOrder parameterDimension H h K hKcompact hKupper hupper
      Z margin hmargin hlimitMargin M hM hlimitNorm

/-- Compact-uniform convergence of the complete finite basis-independent trace
Taylor-Dyson jet. -/
theorem iteratedDeriv_realResolventFiniteParameterTaylorTrace_tendsto_uniformOn_compact_rectangular
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (taylorOrder parameterOrder parameterDimension : ℕ)
    (H : Fin parameterDimension → (V →L[ℝ] V)) (h : Fin parameterDimension → ℝ)
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
      ∀ n : Fin (parameterOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
        |continuousLinearMapFiniteParameterRealResolventTaylorDysonTraceCoefficient V n.1 parameterDimension
            (continuousLinearMapCompression J Q (_root_.iteratedDeriv k.1 (F a) lambda)) H z 0 h -
          continuousLinearMapFiniteParameterRealResolventTaylorDysonTraceCoefficient V n.1 parameterDimension
            (continuousLinearMapCompression J Q (_root_.iteratedDeriv k.1 S.limitResolvent lambda)) H z 0 h| < epsilon := by
  simpa [Real.norm_eq_abs, continuousLinearMapFiniteParameterRealResolventTaylorDysonTraceCoefficient] using
    S.iteratedDeriv_realResolventFiniteParameterTaylorResponse_tendsto_uniformOn_compact_rectangular
      B L hLgap hLresolvent J Q (continuousLinearMapTrace (V := V))
      taylorOrder parameterOrder parameterDimension H h
      K hKcompact hKupper hupper Z margin hmargin hlimitMargin M hM hlimitNorm

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
