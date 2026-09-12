import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterResponse
import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventFiniteParameterObservableCompact
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- Arbitrary Banach-valued observation of a joint spectral/operator coordinate
mixed derivative at the joint origin. -/
def continuousLinearMapJointSpectralOperatorRealResolventCoordinateMixedResponse
    {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (φ : (V →L[ℝ] V) →L[ℝ] W) (m n : ℕ)
    (A : V →L[ℝ] V) (H : Fin m → (V →L[ℝ] V)) (z : ℝ)
    (κ : Fin n → Option (Fin m)) : W :=
  continuousLinearMapFiniteParameterRealResolventSymmetricDerivativeLinearResponse
    φ (m + 1) n A
    (continuousLinearMapJointSpectralOperatorDirectionFamily m H) z
    (continuousLinearMapJointSpectralOperatorCoordinateDirectionTuple m n κ)

namespace ContinuousLinearMapOpenTaylorStrongLimitData

variable {α E V W : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Compact-uniform convergence of an observed joint coordinate mixed
Fréchet derivative. -/
theorem iteratedDeriv_realResolventJointCoordinateMixedResponse_tendsto_uniformOn_compact
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (φ : (V →L[ℝ] V) →L[ℝ] W)
    (k m n : ℕ) (H : Fin m → (V →L[ℝ] V)) (κ : Fin n → Option (Fin m))
    (K : Set ℝ) (hKcompact : IsCompact K) {upper : ℝ}
    (hKupper : K ⊆ Set.Iic upper) (hupper : upper < gap) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ lambda ∈ K, ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant
      (continuousLinearMapCompression J Q (_root_.iteratedDeriv k S.limitResolvent lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ lambda ∈ K, ∀ z ∈ Z, continuousLinearMapRealResolventNorm
      (continuousLinearMapCompression J Q (_root_.iteratedDeriv k S.limitResolvent lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l, ∀ lambda ∈ K, ∀ z ∈ Z,
      ‖continuousLinearMapJointSpectralOperatorRealResolventCoordinateMixedResponse φ m n
          (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (F a) lambda)) H z κ -
        continuousLinearMapJointSpectralOperatorRealResolventCoordinateMixedResponse φ m n
          (continuousLinearMapCompression J Q (_root_.iteratedDeriv k S.limitResolvent lambda)) H z κ‖ < epsilon := by
  simpa [continuousLinearMapJointSpectralOperatorRealResolventCoordinateMixedResponse] using
    S.iteratedDeriv_realResolventFiniteParameterMixedResponse_tendsto_uniformOn_compact
      B L hLgap hLresolvent J Q φ k (m + 1) n
      (continuousLinearMapJointSpectralOperatorDirectionFamily m H)
      (continuousLinearMapJointSpectralOperatorCoordinateDirectionTuple m n κ)
      K hKcompact hKupper hupper Z margin hmargin hlimitMargin M hM hlimitNorm

/-- Compact-uniform convergence of a fixed observed joint normalized
Taylor-Dyson coefficient. -/
theorem iteratedDeriv_realResolventJointTaylorResponse_tendsto_uniformOn_compact
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (φ : (V →L[ℝ] V) →L[ℝ] W)
    (k parameterOrder m : ℕ) (H : Fin m → (V →L[ℝ] V)) (ds : ℝ)
    (h : Fin m → ℝ) (K : Set ℝ) (hKcompact : IsCompact K) {upper : ℝ}
    (hKupper : K ⊆ Set.Iic upper) (hupper : upper < gap) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ lambda ∈ K, ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant
      (continuousLinearMapCompression J Q (_root_.iteratedDeriv k S.limitResolvent lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ lambda ∈ K, ∀ z ∈ Z, continuousLinearMapRealResolventNorm
      (continuousLinearMapCompression J Q (_root_.iteratedDeriv k S.limitResolvent lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l, ∀ lambda ∈ K, ∀ z ∈ Z,
      ‖continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonResponse φ parameterOrder m
          (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (F a) lambda)) H z 0 ds 0 h -
        continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonResponse φ parameterOrder m
          (continuousLinearMapCompression J Q (_root_.iteratedDeriv k S.limitResolvent lambda)) H z 0 ds 0 h‖ < epsilon := by
  simpa [continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonResponse,
    continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonCoefficient] using
    S.iteratedDeriv_realResolventFiniteParameterTaylorResponse_tendsto_uniformOn_compact
      B L hLgap hLresolvent J Q φ k parameterOrder (m + 1)
      (continuousLinearMapJointSpectralOperatorDirectionFamily m H)
      (continuousLinearMapJointSpectralOperatorParameter m ds h)
      K hKcompact hKupper hupper Z margin hmargin hlimitMargin M hM hlimitNorm

/-- Simultaneous compact-uniform convergence of the complete finite observed
joint Taylor-Dyson jet. -/
theorem iteratedDeriv_realResolventJointTaylorResponse_tendsto_uniformOn_compact_rectangular
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (φ : (V →L[ℝ] V) →L[ℝ] W)
    (taylorOrder parameterOrder m : ℕ) (H : Fin m → (V →L[ℝ] V))
    (ds : ℝ) (h : Fin m → ℝ) (K : Set ℝ) (hKcompact : IsCompact K) {upper : ℝ}
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
        ‖continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonResponse φ n.1 m
            (continuousLinearMapCompression J Q (_root_.iteratedDeriv k.1 (F a) lambda)) H z 0 ds 0 h -
          continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonResponse φ n.1 m
            (continuousLinearMapCompression J Q (_root_.iteratedDeriv k.1 S.limitResolvent lambda)) H z 0 ds 0 h‖ < epsilon := by
  simpa [continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonResponse,
    continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonCoefficient] using
    S.iteratedDeriv_realResolventFiniteParameterTaylorResponse_tendsto_uniformOn_compact_rectangular
      B L hLgap hLresolvent J Q φ taylorOrder parameterOrder (m + 1)
      (continuousLinearMapJointSpectralOperatorDirectionFamily m H)
      (continuousLinearMapJointSpectralOperatorParameter m ds h)
      K hKcompact hKupper hupper Z margin hmargin hlimitMargin M hM hlimitNorm

/-- Compact-uniform convergence of a fixed basis-independent joint trace
Taylor-Dyson coefficient. -/
theorem iteratedDeriv_realResolventJointTaylorTrace_tendsto_uniformOn_compact
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (k parameterOrder m : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (ds : ℝ) (h : Fin m → ℝ)
    (K : Set ℝ) (hKcompact : IsCompact K) {upper : ℝ}
    (hKupper : K ⊆ Set.Iic upper) (hupper : upper < gap) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ lambda ∈ K, ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant
      (continuousLinearMapCompression J Q (_root_.iteratedDeriv k S.limitResolvent lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ lambda ∈ K, ∀ z ∈ Z, continuousLinearMapRealResolventNorm
      (continuousLinearMapCompression J Q (_root_.iteratedDeriv k S.limitResolvent lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l, ∀ lambda ∈ K, ∀ z ∈ Z,
      |continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonTraceCoefficient V parameterOrder m
          (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (F a) lambda)) H z 0 ds 0 h -
        continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonTraceCoefficient V parameterOrder m
          (continuousLinearMapCompression J Q (_root_.iteratedDeriv k S.limitResolvent lambda)) H z 0 ds 0 h| < epsilon := by
  simpa [continuousLinearMapJointSpectralOperatorRealResolventTaylorDysonTraceCoefficient,
    Real.norm_eq_abs] using
    S.iteratedDeriv_realResolventJointTaylorResponse_tendsto_uniformOn_compact
      B L hLgap hLresolvent J Q (continuousLinearMapTrace (V := V))
      k parameterOrder m H ds h K hKcompact hKupper hupper Z margin hmargin
      hlimitMargin M hM hlimitNorm

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
