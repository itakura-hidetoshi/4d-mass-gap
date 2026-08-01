import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventOperatorPerturbationDysonResponse
import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalContinuousObservableCore
import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventStabilityCompact
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- For a fixed operator direction, every algebraic Dyson coefficient is
continuous in the resolvent variable. -/
theorem continuous_continuousLinearMapRealResolventDysonCoefficientFromFixedDirection
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (n : ℕ) (H : V →L[ℝ] V) :
    Continuous (fun R : V →L[ℝ] V =>
      continuousLinearMapRealResolventDysonCoefficientFromPair n R H) := by
  simpa [continuousLinearMapRealResolventDysonCoefficientFromPair] using
    (((continuous_id.mul continuous_const).pow n).mul continuous_id)

namespace ContinuousLinearMapOpenTaylorStrongLimitData

variable {α E V : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [FiniteDimensional ℝ V]

/-- Compact-uniform convergence of a fixed operator-perturbation Dyson
coefficient after arbitrary finite-dimensional compression. -/
theorem iteratedDeriv_realResolventOperatorDysonCoefficient_finiteDimensionalCompression_tendsto_uniformOn_compact_product
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (k dysonOrder : ℕ) (H : V →L[ℝ] V)
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
        ‖continuousLinearMapRealResolventOperatorDysonCoefficient dysonOrder
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) H z -
          continuousLinearMapRealResolventOperatorDysonCoefficient dysonOrder
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
  have hdyson :=
    finiteDimensional_continuousObservable_tendsto_uniformOn
      R R0
      (fun T : V →L[ℝ] V =>
        continuousLinearMapRealResolventDysonCoefficientFromPair dysonOrder T H)
      (continuous_continuousLinearMapRealResolventDysonCoefficientFromFixedDirection
        dysonOrder H)
      M hM hR0 hR
  intro epsilon hepsilon
  have h := hdyson epsilon hepsilon
  filter_upwards [h] with a ha
  intro lambda hlambda z hz
  have ha' := ha (lambda, z) ⟨hlambda, hz⟩
  simpa [R, R0, continuousLinearMapRealResolventDysonCoefficientFromPair,
    continuousLinearMapRealResolventOperatorDysonCoefficient] using ha'

/-- Simultaneous compact-uniform convergence on the full finite rectangle of
Taylor derivative orders and operator-perturbation Dyson orders. -/
theorem iteratedDeriv_realResolventOperatorDysonCoefficient_finiteDimensionalCompression_tendsto_uniformOn_compact_product_rectangular
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (taylorOrder dysonOrder : ℕ) (H : V →L[ℝ] V)
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
      ∀ k : Fin (taylorOrder + 1), ∀ n : Fin (dysonOrder + 1),
      ∀ lambda ∈ K, ∀ z ∈ Z,
        ‖continuousLinearMapRealResolventOperatorDysonCoefficient n.1
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k.1 (F a) lambda)) H z -
          continuousLinearMapRealResolventOperatorDysonCoefficient n.1
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k.1 S.limitResolvent lambda)) H z‖ < epsilon := by
  intro epsilon hepsilon
  let I := Fin (taylorOrder + 1) × Fin (dysonOrder + 1)
  let P : α → I → Prop := fun a kn =>
    ∀ lambda ∈ K, ∀ z ∈ Z,
      ‖continuousLinearMapRealResolventOperatorDysonCoefficient kn.2.1
          (continuousLinearMapCompression J Q
            (_root_.iteratedDeriv kn.1.1 (F a) lambda)) H z -
        continuousLinearMapRealResolventOperatorDysonCoefficient kn.2.1
          (continuousLinearMapCompression J Q
            (_root_.iteratedDeriv kn.1.1 S.limitResolvent lambda)) H z‖ < epsilon
  have hkn : ∀ kn : I, ∀ᶠ a in l, P a kn := by
    intro kn
    exact
      S.iteratedDeriv_realResolventOperatorDysonCoefficient_finiteDimensionalCompression_tendsto_uniformOn_compact_product
        B L hLgap hLresolvent J Q kn.1.1 kn.2.1 H
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
