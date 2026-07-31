import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventHermiteTransfer
import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventStabilityCompact
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

/-- Compact-uniform convergence of a normalized multipoint Hermite coefficient
for a fixed Taylor derivative and an arbitrary family of finite spectral-node
tuples contained in a common real resolvent set. -/
theorem iteratedDeriv_realResolventHermiteCoefficient_finiteDimensionalCompression_tendsto_uniformOn_compact_product
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (k order : ℕ)
    (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < gap)
    (nodes : κ → Fin (order + 1) → ℝ) (T : Set κ) (Z : Set ℝ)
    (hnodes : ∀ q ∈ T, ∀ j, nodes q j ∈ Z)
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
      ∀ lambda ∈ K, ∀ q ∈ T,
        ‖continuousLinearMapRealResolventHermiteCoefficient order
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k (F a) lambda)) (nodes q) -
          continuousLinearMapRealResolventHermiteCoefficient order
            (continuousLinearMapCompression J Q
              (_root_.iteratedDeriv k S.limitResolvent lambda)) (nodes q)‖ < epsilon := by
  let R : α → (ℝ × κ) → Fin (order + 1) → (V →L[ℝ] V) := fun a p j =>
    continuousLinearMapRealResolvent
      (continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k (F a) p.1)) (nodes p.2 j)
  let R0 : (ℝ × κ) → Fin (order + 1) → (V →L[ℝ] V) := fun p j =>
    continuousLinearMapRealResolvent
      (continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k S.limitResolvent p.1)) (nodes p.2 j)
  have hR0 : ∀ p ∈ K ×ˢ T, ∀ j, ‖R0 p j‖ ≤ M := by
    intro p hp j
    simpa [R0, continuousLinearMapRealResolventNorm] using
      hlimitNorm p.1 hp.1 (nodes p.2 j) (hnodes p.2 hp.2 j)
  have hR : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ a in l, ∀ p ∈ K ×ˢ T, ∀ j, ‖R a p j - R0 p j‖ < eta := by
    intro eta heta
    have h :=
      S.iteratedDeriv_realResolvent_finiteDimensionalCompression_tendsto_uniformOn_compact_product
        B L hLgap hLresolvent J Q k K hKcompact hKu hu Z
        margin hmargin hlimitMargin M hM hlimitNorm eta heta
    filter_upwards [h] with a ha
    intro p hp j
    simpa [R, R0] using
      ha p.1 hp.1 (nodes p.2 j) (hnodes p.2 hp.2 j)
  have hcoeff :=
    finiteDimensional_realResolventHermiteObservable_tendsto_uniformOn_of_componentwise
      order R R0 M hM hR0 hR
  intro epsilon hepsilon
  have h := hcoeff epsilon hepsilon
  filter_upwards [h] with a ha
  intro lambda hlambda q hq
  simpa [R, R0, continuousLinearMapRealResolventHermiteCoefficient] using
    ha (lambda, q) ⟨hlambda, hq⟩

/-- Compact-uniform simultaneous convergence of the complete normalized
Hermite jet through a fixed finite order for arbitrary finite spectral-node
families. -/
theorem iteratedDeriv_realResolventHermiteJet_finiteDimensionalCompression_tendsto_uniformOn_compact_product
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (k order : ℕ)
    (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < gap)
    (nodes : κ → Fin (order + 1) → ℝ) (T : Set κ) (Z : Set ℝ)
    (hnodes : ∀ q ∈ T, ∀ j, nodes q j ∈ Z)
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
      ∀ lambda ∈ K, ∀ q ∈ T,
        ‖continuousLinearMapRealResolventHermiteJet order
            (fun j => continuousLinearMapRealResolvent
              (continuousLinearMapCompression J Q
                (_root_.iteratedDeriv k (F a) lambda)) (nodes q j)) -
          continuousLinearMapRealResolventHermiteJet order
            (fun j => continuousLinearMapRealResolvent
              (continuousLinearMapCompression J Q
                (_root_.iteratedDeriv k S.limitResolvent lambda)) (nodes q j))‖ < epsilon := by
  let R : α → (ℝ × κ) → Fin (order + 1) → (V →L[ℝ] V) := fun a p j =>
    continuousLinearMapRealResolvent
      (continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k (F a) p.1)) (nodes p.2 j)
  let R0 : (ℝ × κ) → Fin (order + 1) → (V →L[ℝ] V) := fun p j =>
    continuousLinearMapRealResolvent
      (continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k S.limitResolvent p.1)) (nodes p.2 j)
  have hR0 : ∀ p ∈ K ×ˢ T, ∀ j, ‖R0 p j‖ ≤ M := by
    intro p hp j
    simpa [R0, continuousLinearMapRealResolventNorm] using
      hlimitNorm p.1 hp.1 (nodes p.2 j) (hnodes p.2 hp.2 j)
  have hR : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ a in l, ∀ p ∈ K ×ˢ T, ∀ j, ‖R a p j - R0 p j‖ < eta := by
    intro eta heta
    have h :=
      S.iteratedDeriv_realResolvent_finiteDimensionalCompression_tendsto_uniformOn_compact_product
        B L hLgap hLresolvent J Q k K hKcompact hKu hu Z
        margin hmargin hlimitMargin M hM hlimitNorm eta heta
    filter_upwards [h] with a ha
    intro p hp j
    simpa [R, R0] using
      ha p.1 hp.1 (nodes p.2 j) (hnodes p.2 hp.2 j)
  have hjet :=
    finiteDimensional_realResolventHermiteJet_tendsto_uniformOn_of_componentwise
      order R R0 M hM hR0 hR
  intro epsilon hepsilon
  have h := hjet epsilon hepsilon
  filter_upwards [h] with a ha
  intro lambda hlambda q hq
  simpa [R, R0] using ha (lambda, q) ⟨hlambda, hq⟩

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
