import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventOperatorPerturbationMixedDysonResponse
import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalContinuousObservableCore
import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventStabilityCompact
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

/-- Compact-uniform convergence of a fixed mixed-direction Dyson polarization
coefficient after arbitrary finite-dimensional compression. -/
theorem iteratedDeriv_realResolventOperatorMixedDysonCoefficient_finiteDimensionalCompression_tendsto_uniformOn_compact_product
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (k mixedOrder : ℕ) (H : Fin mixedOrder → (V →L[ℝ] V))
    (K : Set ℝ) (hKcompact : IsCompact K) {u : ℝ}
    (hKu : K ⊆ Set.Iic u) (hu : u < gap) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ lambda ∈ K, ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k S.limitResolvent lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ lambda ∈ K, ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k S.limitResolvent lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l,
      ∀ lambda ∈ K, ∀ z ∈ Z,
        ‖continuousLinearMapRealResolventOperatorMixedDysonCoefficient mixedOrder
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) H z -
          continuousLinearMapRealResolventOperatorMixedDysonCoefficient mixedOrder
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda)) H z‖ < epsilon := by
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
        B L hLgap hLresolvent J Q k K hKcompact hKu hu Z
        margin hmargin hlimitMargin M hM hlimitNorm eta heta
    filter_upwards [h] with a ha
    intro p hp
    simpa [R, R0] using ha p.1 hp.1 p.2 hp.2
  have hmixed :=
    finiteDimensional_continuousObservable_tendsto_uniformOn
      R R0
      (fun T : V →L[ℝ] V =>
        continuousLinearMapRealResolventMixedDysonCoefficientFromResolvent
          mixedOrder T H)
      (continuous_continuousLinearMapRealResolventMixedDysonCoefficientFromResolvent
        mixedOrder H)
      M hM hR0 hR
  intro epsilon hepsilon
  have h := hmixed epsilon hepsilon
  filter_upwards [h] with a ha
  intro lambda hlambda z hz
  have ha' := ha (lambda, z) ⟨hlambda, hz⟩
  simpa [R, R0,
    continuousLinearMapRealResolventOperatorMixedDysonCoefficient_eq_fromResolvent] using ha'

/-- Simultaneous compact-uniform convergence on the full finite rectangle of
Taylor derivative orders and mixed-direction polarization orders. -/
theorem iteratedDeriv_realResolventOperatorMixedDysonCoefficient_finiteDimensionalCompression_tendsto_uniformOn_compact_product_rectangular
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (taylorOrder mixedOrder : ℕ)
    (H : ∀ n : Fin (mixedOrder + 1), Fin n.1 → (V →L[ℝ] V))
    (K : Set ℝ) (hKcompact : IsCompact K) {u : ℝ}
    (hKu : K ⊆ Set.Iic u) (hu : u < gap) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
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
        ‖continuousLinearMapRealResolventOperatorMixedDysonCoefficient n.1
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k.1 (F a) lambda)) (H n) z -
          continuousLinearMapRealResolventOperatorMixedDysonCoefficient n.1
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k.1 S.limitResolvent lambda)) (H n) z‖ < epsilon := by
  intro epsilon hepsilon
  let I := Fin (taylorOrder + 1) × Fin (mixedOrder + 1)
  let P : α → I → Prop := fun a kn =>
    ∀ lambda ∈ K, ∀ z ∈ Z,
      ‖continuousLinearMapRealResolventOperatorMixedDysonCoefficient kn.2.1
          (continuousLinearMapCompression J Q
            (_root_.iteratedDeriv kn.1.1 (F a) lambda)) (H kn.2) z -
        continuousLinearMapRealResolventOperatorMixedDysonCoefficient kn.2.1
          (continuousLinearMapCompression J Q
            (_root_.iteratedDeriv kn.1.1 S.limitResolvent lambda)) (H kn.2) z‖ < epsilon
  have hkn : ∀ kn : I, ∀ᶠ a in l, P a kn := by
    intro kn
    exact
      S.iteratedDeriv_realResolventOperatorMixedDysonCoefficient_finiteDimensionalCompression_tendsto_uniformOn_compact_product
        B L hLgap hLresolvent J Q kn.1.1 kn.2.1 (H kn.2)
        K hKcompact hKu hu Z margin hmargin
        (hlimitMargin kn.1) M hM (hlimitNorm kn.1) epsilon hepsilon
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

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
