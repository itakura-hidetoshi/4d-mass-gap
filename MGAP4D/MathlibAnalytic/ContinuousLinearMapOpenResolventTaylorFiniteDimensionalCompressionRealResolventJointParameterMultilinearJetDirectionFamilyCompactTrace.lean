import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterMultilinearJetDirectionFamilyCompactResponse
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
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Compact-uniform convergence of the complete basis-independent trace jet
under simultaneous resolvent and direction-family motion. -/
theorem iteratedDeriv_realResolventJointMultilinearTraceCarrierRectangularJet_finiteDimensionalCompression_tendsto_uniformOn_compact_product_directionFamily_sup
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (taylorOrder mixedOrder m : ℕ)
    (H : α → Fin m → (V →L[ℝ] V)) (H0 : Fin m → (V →L[ℝ] V))
    (hH : Tendsto H l (𝓝 H0)) (K : Set ℝ) (hKcompact : IsCompact K)
    {upper : ℝ} (hKupper : K ⊆ Set.Iic upper) (hupper : upper < gap)
    (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant (continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k.1 S.limitResolvent lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm (continuousLinearMapCompression J Q
        (_root_.iteratedDeriv k.1 S.limitResolvent lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l, ∀ lambda ∈ K, ∀ z ∈ Z,
      continuousLinearMapJointMultilinearCarrierRectangularJetSupDistance
        (continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierRectangularJetFromResolventFamily
          V m taylorOrder mixedOrder (H a) (continuousLinearMapCompressedIteratedDerivRealResolventFamily
            J Q taylorOrder (F a) lambda z))
        (continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierRectangularJetFromResolventFamily
          V m taylorOrder mixedOrder H0 (continuousLinearMapCompressedIteratedDerivRealResolventFamily
            J Q taylorOrder S.limitResolvent lambda z)) < epsilon := by
  intro epsilon hepsilon
  let I := Fin (taylorOrder + 1) × Fin (mixedOrder + 1)
  let P : α → I → Prop := fun a kn => ∀ lambda ∈ K, ∀ z ∈ Z,
    ‖continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierFromResolvent
        V m kn.2.1 (H a) (continuousLinearMapCompressedRealResolventAt J Q
          (_root_.iteratedDeriv kn.1.1 (F a) lambda) z) -
      continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierFromResolvent
        V m kn.2.1 H0 (continuousLinearMapCompressedRealResolventAt J Q
          (_root_.iteratedDeriv kn.1.1 S.limitResolvent lambda) z)‖ < epsilon
  have hkn : ∀ kn : I, ∀ᶠ a in l, P a kn := by
    intro kn
    let R : α → (ℝ × ℝ) → (V →L[ℝ] V) := fun a p =>
      continuousLinearMapCompressedRealResolventAt J Q
        (_root_.iteratedDeriv kn.1.1 (F a) p.1) p.2
    let R0 : (ℝ × ℝ) → (V →L[ℝ] V) := fun p =>
      continuousLinearMapCompressedRealResolventAt J Q
        (_root_.iteratedDeriv kn.1.1 S.limitResolvent p.1) p.2
    have hR0 : ∀ p ∈ K ×ˢ Z, ‖R0 p‖ ≤ M := by
      intro p hp
      simpa [R0, continuousLinearMapCompressedRealResolventAt,
        continuousLinearMapRealResolventNorm] using
        hlimitNorm kn.1 p.1 hp.1 p.2 hp.2
    have hR : ∀ eta : ℝ, 0 < eta →
        ∀ᶠ a in l, ∀ p ∈ K ×ˢ Z, ‖R a p - R0 p‖ < eta := by
      intro eta heta
      have h :=
        S.iteratedDeriv_realResolvent_finiteDimensionalCompression_tendsto_uniformOn_compact_product
          B L hLgap hLresolvent J Q kn.1.1 K hKcompact hKupper hupper Z
          margin hmargin (hlimitMargin kn.1) M hM (hlimitNorm kn.1) eta heta
      filter_upwards [h] with a ha
      intro p hp
      simpa [R, R0, continuousLinearMapCompressedRealResolventAt] using
        ha p.1 hp.1 p.2 hp.2
    have hPhi : Continuous (fun p :
        (V →L[ℝ] V) × (Fin m → (V →L[ℝ] V)) =>
        continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierFromResolvent
          V m kn.2.1 p.2 p.1) := by
      simpa [continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierFromResolvent] using
        continuous_continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierFromResolvent_directionFamily
          (continuousLinearMapTrace (V := V)) m kn.2.1
    have hout := finiteDimensional_directionFamilyObservable_tendsto_uniformOn
      R R0 H H0
      (fun p =>
        continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierFromResolvent
          V m kn.2.1 p.2 p.1)
      hPhi M hM hR0 hR hH epsilon hepsilon
    filter_upwards [hout] with a ha
    intro lambda hlambda z hz
    simpa [P, R, R0] using ha (lambda, z) ⟨hlambda, hz⟩
  have hfinite : ∀ᶠ a in l, ∀ kn : I, P a kn := by
    change {a | ∀ kn : I, P a kn} ∈ l
    rw [show {a | ∀ kn : I, P a kn} =
      ⋂ kn ∈ (Finset.univ : Finset I), {a | P a kn} by
        ext a
        simp]
    exact (Filter.biInter_finset_mem (Finset.univ : Finset I)).2
      (fun kn _ => hkn kn)
  filter_upwards [hfinite] with a ha
  intro lambda hlambda z hz
  apply (continuousLinearMapJointMultilinearCarrierRectangularJetSupDistance_lt_iff
    (continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierRectangularJetFromResolventFamily
      V m taylorOrder mixedOrder (H a)
      (continuousLinearMapCompressedIteratedDerivRealResolventFamily
        J Q taylorOrder (F a) lambda z))
    (continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierRectangularJetFromResolventFamily
      V m taylorOrder mixedOrder H0
      (continuousLinearMapCompressedIteratedDerivRealResolventFamily
        J Q taylorOrder S.limitResolvent lambda z)) epsilon).2
  intro k n
  simpa [continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierRectangularJetFromResolventFamily,
    continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierCompleteJetFromResolvent,
    continuousLinearMapCompressedIteratedDerivRealResolventFamily,
    continuousLinearMapCompressedRealResolventAt] using
    ha (k, n) lambda hlambda z hz

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
