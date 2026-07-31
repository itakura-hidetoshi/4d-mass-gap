import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventTraceResponse
import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventLinearResponseCompactRectangular
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

namespace ContinuousLinearMapOpenTaylorStrongLimitData

variable {α κ E V : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [FiniteDimensional ℝ V]

/-- Compact-uniform simultaneous convergence of the trace interpolant and its
exact trace remainder. -/
theorem iteratedDeriv_realResolventNewtonHermiteTracePair_finiteDimensionalCompression_tendsto_uniformOn_compact_product
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (k degree : ℕ)
    (K : Set ℝ) (hKcompact : IsCompact K) {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < gap)
    (nodes : κ → Fin (degree + 1) → ℝ) (eval : κ → ℝ) (T : Set κ) (Z : Set ℝ)
    (hnodes : ∀ q ∈ T, ∀ j, nodes q j ∈ Z) (heval : ∀ q ∈ T, eval q ∈ Z)
    (D : ℝ) (hD : 0 ≤ D) (hdist : ∀ q ∈ T, ∀ j, |eval q - nodes q j| ≤ D)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ lambda ∈ K, ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant
      (continuousLinearMapCompression J Q (_root_.iteratedDeriv k S.limitResolvent lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ lambda ∈ K, ∀ z ∈ Z, continuousLinearMapRealResolventNorm
      (continuousLinearMapCompression J Q (_root_.iteratedDeriv k S.limitResolvent lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l, ∀ lambda ∈ K, ∀ q ∈ T,
      ‖continuousLinearMapRealResolventTracePair
          (continuousLinearMapRealResolventNewtonHermitePair degree
            (continuousLinearMapCompression J Q (_root_.iteratedDeriv k (F a) lambda))
            (nodes q) (eval q)) -
        continuousLinearMapRealResolventTracePair
          (continuousLinearMapRealResolventNewtonHermitePair degree
            (continuousLinearMapCompression J Q (_root_.iteratedDeriv k S.limitResolvent lambda))
            (nodes q) (eval q))‖ < epsilon := by
  intro epsilon hepsilon
  have htransfer :=
    finiteDimensional_tracePair_tendsto_uniformOn
      (l := l) (s := K ×ˢ T)
      (fun a p => continuousLinearMapRealResolventNewtonHermitePair degree
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k (F a) p.1)) (nodes p.2) (eval p.2))
      (fun p => continuousLinearMapRealResolventNewtonHermitePair degree
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k S.limitResolvent p.1)) (nodes p.2) (eval p.2))
      (by
        intro eta heta
        have h :=
          S.iteratedDeriv_realResolventNewtonHermitePair_finiteDimensionalCompression_tendsto_uniformOn_compact_product
            B L hLgap hLresolvent J Q k degree K hKcompact hKu hu
            nodes eval T Z hnodes heval D hD hdist margin hmargin
            hlimitMargin M hM hlimitNorm eta heta
        filter_upwards [h] with a ha
        intro p hp
        exact ha p.1 hp.1 p.2 hp.2)
      epsilon hepsilon
  filter_upwards [htransfer] with a ha
  intro lambda hlambda q hq
  exact ha (lambda, q) ⟨hlambda, hq⟩

/-- Simultaneous compact-uniform trace convergence over the finite Taylor-order
by interpolation-degree rectangle. -/
theorem iteratedDeriv_realResolventNewtonHermiteTracePair_finiteDimensionalCompression_tendsto_uniformOn_compact_product_rectangular
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (taylorOrder interpolationOrder : ℕ)
    (K : Set ℝ) (hKcompact : IsCompact K) {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < gap)
    (nodes : ∀ d : Fin (interpolationOrder + 1), κ → Fin (d.1 + 1) → ℝ)
    (eval : Fin (interpolationOrder + 1) → κ → ℝ) (T : Set κ) (Z : Set ℝ)
    (hnodes : ∀ d q, q ∈ T → ∀ j, nodes d q j ∈ Z) (heval : ∀ d q, q ∈ T → eval d q ∈ Z)
    (D : ℝ) (hD : 0 ≤ D) (hdist : ∀ d q, q ∈ T → ∀ j, |eval d q - nodes d q j| ≤ D)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z, margin ≤ |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q (_root_.iteratedDeriv k.1 S.limitResolvent lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z, continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q (_root_.iteratedDeriv k.1 S.limitResolvent lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l, ∀ k : Fin (taylorOrder + 1), ∀ d : Fin (interpolationOrder + 1), ∀ lambda ∈ K, ∀ q ∈ T,
      ‖continuousLinearMapRealResolventTracePair (continuousLinearMapRealResolventNewtonHermitePair d.1 (continuousLinearMapCompression J Q (_root_.iteratedDeriv k.1 (F a) lambda)) (nodes d q) (eval d q)) - continuousLinearMapRealResolventTracePair (continuousLinearMapRealResolventNewtonHermitePair d.1 (continuousLinearMapCompression J Q (_root_.iteratedDeriv k.1 S.limitResolvent lambda)) (nodes d q) (eval d q))‖ < epsilon := by
  intro epsilon hepsilon
  let I := Fin (taylorOrder + 1) × Fin (interpolationOrder + 1)
  let P : α → I → Prop := fun a kd =>
    ∀ lambda ∈ K, ∀ q ∈ T,
      ‖continuousLinearMapRealResolventTracePair
          (continuousLinearMapRealResolventNewtonHermitePair kd.2.1
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv kd.1.1 (F a) lambda))
            (nodes kd.2 q) (eval kd.2 q)) -
        continuousLinearMapRealResolventTracePair
          (continuousLinearMapRealResolventNewtonHermitePair kd.2.1
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv kd.1.1 S.limitResolvent lambda))
            (nodes kd.2 q) (eval kd.2 q))‖ < epsilon
  have hkd : ∀ kd : I, ∀ᶠ a in l, P a kd := by
    intro kd
    exact
      S.iteratedDeriv_realResolventNewtonHermiteTracePair_finiteDimensionalCompression_tendsto_uniformOn_compact_product
        B L hLgap hLresolvent J Q kd.1.1 kd.2.1 K hKcompact hKu hu
        (nodes kd.2) (eval kd.2) T Z (hnodes kd.2) (heval kd.2)
        D hD (hdist kd.2) margin hmargin (hlimitMargin kd.1)
        M hM (hlimitNorm kd.1) epsilon hepsilon
  have hfinite : ∀ᶠ a in l, ∀ kd : I, P a kd := by
    change {a | ∀ kd : I, P a kd} ∈ l
    rw [show {a | ∀ kd : I, P a kd} =
      ⋂ kd ∈ (Finset.univ : Finset I), {a | P a kd} by
        ext a
        simp]
    exact (Filter.biInter_finset_mem (Finset.univ : Finset I)).2
      (fun kd _ => hkd kd)
  filter_upwards [hfinite] with a ha
  intro k d lambda hlambda q hq
  exact ha (k, d) lambda hlambda q hq

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
