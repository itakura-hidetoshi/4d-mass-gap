import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterMultilinearJetOperatorNormResponse
import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventStabilityCompact
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

/-- Compact-uniform operator-norm convergence of the complete joint
spectral/operator Fréchet multilinear carrier after arbitrary finite-dimensional
compression.  No direction tuple is chosen in this statement. -/
theorem iteratedDeriv_realResolventJointMultilinearCarrier_finiteDimensionalCompression_tendsto_uniformOn_compact_product
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (k m n : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (K : Set ℝ) (hKcompact : IsCompact K)
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
      ‖continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierFromResolvent
          m n H (continuousLinearMapRealResolvent
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) z) -
        continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierFromResolvent
          m n H (continuousLinearMapRealResolvent
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda)) z)‖ < epsilon := by
  let R : α → (ℝ × ℝ) → (V →L[ℝ] V) := fun a p =>
    continuousLinearMapRealResolvent
      (continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k (F a) p.1)) p.2
  let R0 : (ℝ × ℝ) → (V →L[ℝ] V) := fun p =>
    continuousLinearMapRealResolvent
      (continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k S.limitResolvent p.1)) p.2
  have hR0 : ∀ p ∈ K ×ˢ Z, ‖R0 p‖ ≤ M := by
    intro p hp
    simpa [R0, continuousLinearMapRealResolventNorm] using
      hlimitNorm p.1 hp.1 p.2 hp.2
  have hR : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ a in l, ∀ p ∈ K ×ˢ Z, ‖R a p - R0 p‖ < eta := by
    intro eta heta
    have h :=
      S.iteratedDeriv_realResolvent_finiteDimensionalCompression_tendsto_uniformOn_compact_product
        B L hLgap hLresolvent J Q k K hKcompact hKupper hupper Z
        margin hmargin hlimitMargin M hM hlimitNorm eta heta
    filter_upwards [h] with a ha
    intro p hp
    simpa [R, R0] using ha p.1 hp.1 p.2 hp.2
  have hcarrier :=
    finiteDimensional_continuousObservable_tendsto_uniformOn
      R R0
      (fun T : V →L[ℝ] V =>
        continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierFromResolvent
          m n H T)
      (continuous_continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierFromResolvent
        m n H)
      M hM hR0 hR
  intro epsilon hepsilon
  have h := hcarrier epsilon hepsilon
  filter_upwards [h] with a ha
  intro lambda hlambda z hz
  simpa [R, R0] using ha (lambda, z) ⟨hlambda, hz⟩

/-- Simultaneous compact-uniform convergence of the complete finite jet of
joint Fréchet multilinear carriers in their own operator norms. -/
theorem iteratedDeriv_realResolventJointMultilinearCarrier_finiteDimensionalCompression_tendsto_uniformOn_compact_product_rectangular
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (taylorOrder mixedOrder m : ℕ) (H : Fin m → (V →L[ℝ] V))
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
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l,
      ∀ k : Fin (taylorOrder + 1), ∀ n : Fin (mixedOrder + 1),
      ∀ lambda ∈ K, ∀ z ∈ Z,
        ‖continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierFromResolvent
            m n.1 H (continuousLinearMapRealResolvent
              (continuousLinearMapCompression J Q
                (_root_.iteratedDeriv k.1 (F a) lambda)) z) -
          continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierFromResolvent
            m n.1 H (continuousLinearMapRealResolvent
              (continuousLinearMapCompression J Q
                (_root_.iteratedDeriv k.1 S.limitResolvent lambda)) z)‖ < epsilon := by
  intro epsilon hepsilon
  let I := Fin (taylorOrder + 1) × Fin (mixedOrder + 1)
  let P : α → I → Prop := fun a kn =>
    ∀ lambda ∈ K, ∀ z ∈ Z,
      ‖continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierFromResolvent
          m kn.2.1 H (continuousLinearMapRealResolvent
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv kn.1.1 (F a) lambda)) z) -
        continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierFromResolvent
          m kn.2.1 H (continuousLinearMapRealResolvent
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv kn.1.1 S.limitResolvent lambda)) z)‖ < epsilon
  have hkn : ∀ kn : I, ∀ᶠ a in l, P a kn := by
    intro kn
    exact
      S.iteratedDeriv_realResolventJointMultilinearCarrier_finiteDimensionalCompression_tendsto_uniformOn_compact_product
        B L hLgap hLresolvent J Q kn.1.1 m kn.2.1 H K hKcompact
        hKupper hupper Z margin hmargin (hlimitMargin kn.1)
        M hM (hlimitNorm kn.1) epsilon hepsilon
  have hfinite : ∀ᶠ a in l, ∀ kn : I, P a kn := by
    change {a | ∀ kn : I, P a kn} ∈ l
    rw [show {a | ∀ kn : I, P a kn} =
      ⋂ kn ∈ (Finset.univ : Finset I), {a | P a kn} by
        ext a
        simp]
    exact (Filter.biInter_finset_mem (Finset.univ : Finset I)).2
      (fun kn _ => hkn kn)
  filter_upwards [hfinite] with a ha
  intro k n lambda hlambda z hz
  exact ha (k, n) lambda hlambda z hz

/-- Compact-uniform operator-norm convergence of a complete Banach-valued
observation of the joint Fréchet multilinear carrier. -/
theorem iteratedDeriv_realResolventJointMultilinearResponseCarrier_finiteDimensionalCompression_tendsto_uniformOn_compact_product
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (φ : (V →L[ℝ] V) →L[ℝ] W) (k m n : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (K : Set ℝ) (hKcompact : IsCompact K)
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
      ‖continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierFromResolvent
          φ m n H (continuousLinearMapRealResolvent
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) z) -
        continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierFromResolvent
          φ m n H (continuousLinearMapRealResolvent
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda)) z)‖ < epsilon := by
  let R : α → (ℝ × ℝ) → (V →L[ℝ] V) := fun a p =>
    continuousLinearMapRealResolvent
      (continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k (F a) p.1)) p.2
  let R0 : (ℝ × ℝ) → (V →L[ℝ] V) := fun p =>
    continuousLinearMapRealResolvent
      (continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k S.limitResolvent p.1)) p.2
  have hR0 : ∀ p ∈ K ×ˢ Z, ‖R0 p‖ ≤ M := by
    intro p hp
    simpa [R0, continuousLinearMapRealResolventNorm] using
      hlimitNorm p.1 hp.1 p.2 hp.2
  have hR : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ a in l, ∀ p ∈ K ×ˢ Z, ‖R a p - R0 p‖ < eta := by
    intro eta heta
    have h :=
      S.iteratedDeriv_realResolvent_finiteDimensionalCompression_tendsto_uniformOn_compact_product
        B L hLgap hLresolvent J Q k K hKcompact hKupper hupper Z
        margin hmargin hlimitMargin M hM hlimitNorm eta heta
    filter_upwards [h] with a ha
    intro p hp
    simpa [R, R0] using ha p.1 hp.1 p.2 hp.2
  have hresponse :=
    finiteDimensional_continuousObservable_tendsto_uniformOn
      R R0
      (fun T : V →L[ℝ] V =>
        continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierFromResolvent
          φ m n H T)
      (continuous_continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierFromResolvent
        φ m n H)
      M hM hR0 hR
  intro epsilon hepsilon
  have h := hresponse epsilon hepsilon
  filter_upwards [h] with a ha
  intro lambda hlambda z hz
  simpa [R, R0] using ha (lambda, z) ⟨hlambda, hz⟩

/-- Compact-uniform operator-norm convergence of the complete basis-independent
trace carrier. -/
theorem iteratedDeriv_realResolventJointMultilinearTraceCarrier_finiteDimensionalCompression_tendsto_uniformOn_compact_product
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (k m n : ℕ)
    (H : Fin m → (V →L[ℝ] V)) (K : Set ℝ) (hKcompact : IsCompact K)
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
      ‖continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierFromResolvent
          V m n H (continuousLinearMapRealResolvent
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) z) -
        continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierFromResolvent
          V m n H (continuousLinearMapRealResolvent
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda)) z)‖ < epsilon := by
  simpa [continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierFromResolvent] using
    S.iteratedDeriv_realResolventJointMultilinearResponseCarrier_finiteDimensionalCompression_tendsto_uniformOn_compact_product
      B L hLgap hLresolvent J Q (continuousLinearMapTrace (V := V))
      k m n H K hKcompact hKupper hupper Z margin hmargin
      hlimitMargin M hM hlimitNorm

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
