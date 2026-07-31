import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventSpectralJetTransfer
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

/-- Compact-uniform convergence of a fixed algebraic spectral jet of the true
compressed real resolvent for a fixed Taylor derivative. -/
theorem iteratedDeriv_realResolventSpectralJet_finiteDimensionalCompression_tendsto_uniformOn_compact_product
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (k spectralOrder : ℕ)
    (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < gap) (Z : Set ℝ)
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
        ‖continuousLinearMapRealResolventSpectralJet spectralOrder
            (continuousLinearMapRealResolvent
              (continuousLinearMapCompression J Q
                (_root_.iteratedDeriv k (F a) lambda)) z) -
          continuousLinearMapRealResolventSpectralJet spectralOrder
            (continuousLinearMapRealResolvent
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
    exact hlimitNorm p.1 hp.1 p.2 hp.2
  have hR : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ a in l, ∀ p ∈ K ×ˢ Z, ‖R a p - R0 p‖ < eta := by
    intro eta heta
    have h :=
      S.iteratedDeriv_realResolvent_finiteDimensionalCompression_tendsto_uniformOn_compact_product
        B L hLgap hLresolvent J Q k K hKcompact hKu hu Z
        margin hmargin hlimitMargin M hM hlimitNorm eta heta
    filter_upwards [h] with a ha
    intro p hp
    exact ha p.1 hp.1 p.2 hp.2
  have hjet := finiteDimensional_realResolventSpectralJet_tendsto_uniformOn
    R R0 spectralOrder M hM hR0 hR
  intro epsilon hepsilon
  have h := hjet epsilon hepsilon
  filter_upwards [h] with a ha
  intro lambda hlambda z hz
  exact ha (lambda, z) ⟨hlambda, hz⟩

/-- Compact-uniform simultaneous convergence of every algebraic spectral jet
through a fixed finite order. -/
theorem iteratedDeriv_realResolventSpectralJetVector_finiteDimensionalCompression_tendsto_uniformOn_compact_product
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (k spectralOrder : ℕ)
    (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < gap) (Z : Set ℝ)
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
        ‖continuousLinearMapRealResolventSpectralJetVector spectralOrder
            (continuousLinearMapRealResolvent
              (continuousLinearMapCompression J Q
                (_root_.iteratedDeriv k (F a) lambda)) z) -
          continuousLinearMapRealResolventSpectralJetVector spectralOrder
            (continuousLinearMapRealResolvent
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
    exact hlimitNorm p.1 hp.1 p.2 hp.2
  have hR : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ a in l, ∀ p ∈ K ×ˢ Z, ‖R a p - R0 p‖ < eta := by
    intro eta heta
    have h :=
      S.iteratedDeriv_realResolvent_finiteDimensionalCompression_tendsto_uniformOn_compact_product
        B L hLgap hLresolvent J Q k K hKcompact hKu hu Z
        margin hmargin hlimitMargin M hM hlimitNorm eta heta
    filter_upwards [h] with a ha
    intro p hp
    exact ha p.1 hp.1 p.2 hp.2
  have hjet := finiteDimensional_realResolventSpectralJetVector_tendsto_uniformOn
    R R0 spectralOrder M hM hR0 hR
  intro epsilon hepsilon
  have h := hjet epsilon hepsilon
  filter_upwards [h] with a ha
  intro lambda hlambda z hz
  exact ha (lambda, z) ⟨hlambda, hz⟩

/-- On an open common spectral region, the algebraic convergence is exactly
compact-uniform convergence of the true operator-norm spectral derivatives. -/
theorem iteratedDeriv_realResolvent_iteratedSpectralDeriv_finiteDimensionalCompression_tendsto_uniformOn_compact_product
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (k spectralOrder : ℕ)
    (K : Set ℝ) (hKcompact : IsCompact K)
    {u : ℝ} (hKu : K ⊆ Set.Iic u) (hu : u < gap)
    (U : Set ℝ) (hU : IsOpen U)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ lambda ∈ K, ∀ z ∈ U,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k S.limitResolvent lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ lambda ∈ K, ∀ z ∈ U,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q
          (_root_.iteratedDeriv k S.limitResolvent lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l,
      ∀ lambda ∈ K, ∀ z ∈ U,
        ‖_root_.iteratedDeriv spectralOrder
            (fun w => continuousLinearMapRealResolvent
              (continuousLinearMapCompression J Q
                (_root_.iteratedDeriv k (F a) lambda)) w) z -
          _root_.iteratedDeriv spectralOrder
            (fun w => continuousLinearMapRealResolvent
              (continuousLinearMapCompression J Q
                (_root_.iteratedDeriv k S.limitResolvent lambda)) w) z‖ < epsilon := by
  have hstable :=
    S.iteratedDeriv_realResolvent_finiteDimensionalCompression_eventually_stable_uniformOn_compact_product
      B L hLgap hLresolvent J Q k K hKcompact hKu hu U
      margin hmargin hlimitMargin M hM hlimitNorm 1 zero_lt_one
  have hjet :=
    S.iteratedDeriv_realResolventSpectralJet_finiteDimensionalCompression_tendsto_uniformOn_compact_product
      B L hLgap hLresolvent J Q k spectralOrder K hKcompact hKu hu U
      margin hmargin hlimitMargin M hM hlimitNorm
  intro epsilon hepsilon
  have hj := hjet epsilon hepsilon
  filter_upwards [hstable, hj] with a ha hja
  intro lambda hlambda z hz
  let Aa : V →L[ℝ] V := continuousLinearMapCompression J Q
    (_root_.iteratedDeriv k (F a) lambda)
  let A0 : V →L[ℝ] V := continuousLinearMapCompression J Q
    (_root_.iteratedDeriv k S.limitResolvent lambda)
  have hMa : 0 ≤ 2 * (M + 1) := by nlinarith
  have hunitA : ∀ w ∈ U, IsUnit (continuousLinearMapRealShift Aa w) := by
    intro w hw
    exact (ha lambda hlambda w hw).1
  have hnormA : ∀ w ∈ U,
      continuousLinearMapRealResolventNorm Aa w ≤ 2 * (M + 1) := by
    intro w hw
    exact (ha lambda hlambda w hw).2.1
  have hunit0 : ∀ w ∈ U, IsUnit (continuousLinearMapRealShift A0 w) := by
    intro w hw
    apply continuousLinearMapRealShift_isUnit_of_characteristicDeterminant_ne_zero
    intro hzero
    have hm := hlimitMargin lambda hlambda w hw
    rw [show continuousLinearMapCharacteristicDeterminant A0 w = 0 by simpa [A0] using hzero,
      abs_zero] at hm
    linarith
  have hnorm0 : ∀ w ∈ U, continuousLinearMapRealResolventNorm A0 w ≤ M := by
    intro w hw
    exact hlimitNorm lambda hlambda w hw
  have hAa := continuousLinearMapRealResolventSpectralJet_eq_iteratedDeriv
    Aa U (2 * (M + 1)) hU hMa hunitA hnormA spectralOrder hz
  have hA0 := continuousLinearMapRealResolventSpectralJet_eq_iteratedDeriv
    A0 U M hU hM hunit0 hnorm0 spectralOrder hz
  rw [← hAa, ← hA0]
  exact hja lambda hlambda z hz

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
