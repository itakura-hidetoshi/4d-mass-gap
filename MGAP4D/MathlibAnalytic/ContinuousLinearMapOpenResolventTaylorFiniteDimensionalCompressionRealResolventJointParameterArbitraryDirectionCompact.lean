import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterArbitraryDirectionResponse
import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventFiniteParameterObservableCompact
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

/-- Compact-uniform convergence of an arbitrary Banach-valued observation of a
fixed genuine joint Fréchet derivative in an arbitrary direction tuple. -/
theorem iteratedDeriv_realResolventJointArbitraryDirectionResponse_tendsto_uniformOn_compact
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (φ : (V →L[ℝ] V) →L[ℝ] W)
    (k m n : ℕ) (H : Fin m → (V →L[ℝ] V))
    (u : Fin n → (Fin (m + 1) → ℝ)) (K : Set ℝ) (hKcompact : IsCompact K)
    {upper : ℝ} (hKupper : K ⊆ Set.Iic upper) (hupper : upper < gap)
    (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ lambda ∈ K, ∀ z ∈ Z, margin ≤
      |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k S.limitResolvent lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ lambda ∈ K, ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k S.limitResolvent lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l, ∀ lambda ∈ K, ∀ z ∈ Z,
      ‖continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivativeLinearResponse
          φ m n (continuousLinearMapCompression J Q
            (_root_.iteratedDeriv k (F a) lambda)) H z 0 0 u -
        continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivativeLinearResponse
          φ m n (continuousLinearMapCompression J Q
            (_root_.iteratedDeriv k S.limitResolvent lambda)) H z 0 0 u‖ < epsilon := by
  simpa [continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivativeLinearResponse,
    continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivative] using
    S.iteratedDeriv_realResolventFiniteParameterMixedResponse_tendsto_uniformOn_compact
      B L hLgap hLresolvent J Q φ k (m + 1) n
      (continuousLinearMapJointSpectralOperatorDirectionFamily m H) u
      K hKcompact hKupper hupper Z margin hmargin hlimitMargin M hM hlimitNorm

/-- Simultaneous compact-uniform convergence on the finite ambient-order by
joint Fréchet-order rectangle for arbitrary direction tuples. -/
theorem iteratedDeriv_realResolventJointArbitraryDirectionResponse_tendsto_uniformOn_compact_rectangular
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (φ : (V →L[ℝ] V) →L[ℝ] W)
    (taylorOrder mixedOrder m : ℕ) (H : Fin m → (V →L[ℝ] V))
    (u : ∀ n : Fin (mixedOrder + 1), Fin n.1 → (Fin (m + 1) → ℝ))
    (K : Set ℝ) (hKcompact : IsCompact K) {upper : ℝ}
    (hKupper : K ⊆ Set.Iic upper) (hupper : upper < gap)
    (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k.1 S.limitResolvent lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k.1 S.limitResolvent lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l, ∀ k : Fin (taylorOrder + 1),
      ∀ n : Fin (mixedOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
        ‖continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivativeLinearResponse
            φ m n.1 (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k.1 (F a) lambda)) H z 0 0 (u n) -
          continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivativeLinearResponse
            φ m n.1 (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k.1 S.limitResolvent lambda)) H z 0 0 (u n)‖ < epsilon := by
  simpa [continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivativeLinearResponse,
    continuousLinearMapJointSpectralOperatorRealResolventSymmetricDerivative] using
    S.iteratedDeriv_realResolventFiniteParameterMixedResponse_tendsto_uniformOn_compact_rectangular
      B L hLgap hLresolvent J Q φ (m + 1) taylorOrder mixedOrder
      (continuousLinearMapJointSpectralOperatorDirectionFamily m H) u
      K hKcompact hKupper hupper Z margin hmargin hlimitMargin M hM hlimitNorm

/-- Compact-uniform convergence of the basis-independent trace of a fixed
genuine joint Fréchet derivative in arbitrary directions. -/
theorem iteratedDeriv_realResolventJointArbitraryDirectionTrace_tendsto_uniformOn_compact
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (k m n : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (u : Fin n → (Fin (m + 1) → ℝ))
    (K : Set ℝ) (hKcompact : IsCompact K) {upper : ℝ}
    (hKupper : K ⊆ Set.Iic upper) (hupper : upper < gap)
    (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ lambda ∈ K, ∀ z ∈ Z, margin ≤
      |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k S.limitResolvent lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ lambda ∈ K, ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k S.limitResolvent lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l, ∀ lambda ∈ K, ∀ z ∈ Z,
      |continuousLinearMapJointSpectralOperatorRealResolventSymmetricTraceDerivative
          V m n (continuousLinearMapCompression J Q
            (_root_.iteratedDeriv k (F a) lambda)) H z 0 0 u -
        continuousLinearMapJointSpectralOperatorRealResolventSymmetricTraceDerivative
          V m n (continuousLinearMapCompression J Q
            (_root_.iteratedDeriv k S.limitResolvent lambda)) H z 0 0 u| < epsilon := by
  simpa [continuousLinearMapJointSpectralOperatorRealResolventSymmetricTraceDerivative,
    Real.norm_eq_abs] using
    S.iteratedDeriv_realResolventJointArbitraryDirectionResponse_tendsto_uniformOn_compact
      B L hLgap hLresolvent J Q (continuousLinearMapTrace (V := V))
      k m n H u K hKcompact hKupper hupper Z margin hmargin hlimitMargin
      M hM hlimitNorm

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
