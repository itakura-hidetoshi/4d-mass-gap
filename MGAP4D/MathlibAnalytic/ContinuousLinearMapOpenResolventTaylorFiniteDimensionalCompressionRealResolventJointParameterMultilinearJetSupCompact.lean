import MGAP4D.MathlibAnalytic.ContinuousLinearMapFiniteDimensionalRealResolventJointParameterMultilinearJetSupCore
import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterMultilinearJetOperatorNormCompact
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

/-- The real resolvent of an arbitrary finite-dimensional compression. -/
def continuousLinearMapCompressedRealResolventAt
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (A : E →L[ℝ] E) (z : ℝ) : V →L[ℝ] V :=
  continuousLinearMapRealResolvent (continuousLinearMapCompression J Q A) z

/-- The finite family of compressed real resolvents of all ambient Taylor
orders through `taylorOrder`. -/
def continuousLinearMapCompressedIteratedDerivRealResolventFamily
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (taylorOrder : ℕ)
    (A : ℝ → E →L[ℝ] E) (lambda z : ℝ) :
    Fin (taylorOrder + 1) → (V →L[ℝ] V) :=
  fun k => continuousLinearMapCompressedRealResolventAt J Q
    (_root_.iteratedDeriv k.1 A lambda) z

/-- The compressed real resolvent of a Taylor partial sum. -/
def continuousLinearMapCompressedTaylorPartialSumRealResolventAt
    {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (A : ℝ → E →L[ℝ] E)
    (center target : ℝ) (degree : ℕ) (z : ℝ) : V →L[ℝ] V :=
  continuousLinearMapCompressedRealResolventAt J Q
    (continuousLinearMapTaylorPartialSum A center target degree) z

namespace ContinuousLinearMapOpenTaylorStrongLimitData

variable {α E V W : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Compact-uniform convergence of the complete finite Taylor-order by
joint-Fréchet-order carrier jet in its single rectangular maximum norm. -/
theorem iteratedDeriv_realResolventJointMultilinearCarrierRectangularJet_finiteDimensionalCompression_tendsto_uniformOn_compact_product_sup
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
        (continuousLinearMapCompression J Q (_root_.iteratedDeriv k.1 S.limitResolvent lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q (_root_.iteratedDeriv k.1 S.limitResolvent lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l, ∀ lambda ∈ K, ∀ z ∈ Z,
      continuousLinearMapJointMultilinearCarrierRectangularJetSupDistance
        (continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierRectangularJetFromResolventFamily
          m taylorOrder mixedOrder H
          (continuousLinearMapCompressedIteratedDerivRealResolventFamily J Q taylorOrder (F a) lambda z))
        (continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierRectangularJetFromResolventFamily
          m taylorOrder mixedOrder H
          (continuousLinearMapCompressedIteratedDerivRealResolventFamily J Q taylorOrder S.limitResolvent lambda z)) < epsilon := by
  intro epsilon hepsilon
  have h :=
    S.iteratedDeriv_realResolventJointMultilinearCarrier_finiteDimensionalCompression_tendsto_uniformOn_compact_product_rectangular
      B L hLgap hLresolvent J Q taylorOrder mixedOrder m H K hKcompact
      hKupper hupper Z margin hmargin hlimitMargin M hM hlimitNorm epsilon hepsilon
  filter_upwards [h] with a ha
  intro lambda hlambda z hz
  apply (continuousLinearMapJointMultilinearCarrierRectangularJetSupDistance_lt_iff _ _ epsilon).2
  intro k n
  simpa [continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierRectangularJetFromResolventFamily,
    continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierJetFromResolvent,
    continuousLinearMapCompressedIteratedDerivRealResolventFamily,
    continuousLinearMapCompressedRealResolventAt] using ha k n lambda hlambda z hz

/-- Compact-uniform convergence of a complete finite Banach-valued response
jet in one rectangular maximum norm. -/
theorem iteratedDeriv_realResolventJointMultilinearResponseCarrierRectangularJet_finiteDimensionalCompression_tendsto_uniformOn_compact_product_sup
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (φ : (V →L[ℝ] V) →L[ℝ] W)
    (taylorOrder mixedOrder m : ℕ) (H : Fin m → (V →L[ℝ] V))
    (K : Set ℝ) (hKcompact : IsCompact K) {upper : ℝ}
    (hKupper : K ⊆ Set.Iic upper) (hupper : upper < gap)
    (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q (_root_.iteratedDeriv k.1 S.limitResolvent lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q (_root_.iteratedDeriv k.1 S.limitResolvent lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l, ∀ lambda ∈ K, ∀ z ∈ Z,
      continuousLinearMapJointMultilinearCarrierRectangularJetSupDistance
        (continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierRectangularJetFromResolventFamily
          φ m taylorOrder mixedOrder H
          (continuousLinearMapCompressedIteratedDerivRealResolventFamily J Q taylorOrder (F a) lambda z))
        (continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierRectangularJetFromResolventFamily
          φ m taylorOrder mixedOrder H
          (continuousLinearMapCompressedIteratedDerivRealResolventFamily J Q taylorOrder S.limitResolvent lambda z)) < epsilon := by
  intro epsilon hepsilon
  let I := Fin (taylorOrder + 1) × Fin (mixedOrder + 1)
  let P : α → I → Prop := fun a kn => ∀ lambda ∈ K, ∀ z ∈ Z,
    ‖continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierFromResolvent
        φ m kn.2.1 H (continuousLinearMapRealResolvent
          (continuousLinearMapCompression J Q (_root_.iteratedDeriv kn.1.1 (F a) lambda)) z) -
      continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierFromResolvent
        φ m kn.2.1 H (continuousLinearMapRealResolvent
          (continuousLinearMapCompression J Q (_root_.iteratedDeriv kn.1.1 S.limitResolvent lambda)) z)‖ < epsilon
  have hkn : ∀ kn : I, ∀ᶠ a in l, P a kn := by
    intro kn
    exact S.iteratedDeriv_realResolventJointMultilinearResponseCarrier_finiteDimensionalCompression_tendsto_uniformOn_compact_product
      B L hLgap hLresolvent J Q φ kn.1.1 m kn.2.1 H K hKcompact hKupper hupper Z
      margin hmargin (hlimitMargin kn.1) M hM (hlimitNorm kn.1) epsilon hepsilon
  have hfinite : ∀ᶠ a in l, ∀ kn : I, P a kn := by
    change {a | ∀ kn : I, P a kn} ∈ l
    rw [show {a | ∀ kn : I, P a kn} = ⋂ kn ∈ (Finset.univ : Finset I), {a | P a kn} by
      ext a; simp]
    exact (Filter.biInter_finset_mem (Finset.univ : Finset I)).2 (fun kn _ => hkn kn)
  filter_upwards [hfinite] with a ha
  intro lambda hlambda z hz
  apply (continuousLinearMapJointMultilinearCarrierRectangularJetSupDistance_lt_iff _ _ epsilon).2
  intro k n
  simpa [continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierRectangularJetFromResolventFamily,
    continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierCompleteJetFromResolvent,
    continuousLinearMapCompressedIteratedDerivRealResolventFamily,
    continuousLinearMapCompressedRealResolventAt] using ha (k, n) lambda hlambda z hz

/-- Compact-uniform convergence of the complete basis-independent trace jet in
one rectangular maximum norm. -/
theorem iteratedDeriv_realResolventJointMultilinearTraceCarrierRectangularJet_finiteDimensionalCompression_tendsto_uniformOn_compact_product_sup
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
        (continuousLinearMapCompression J Q (_root_.iteratedDeriv k.1 S.limitResolvent lambda)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ k : Fin (taylorOrder + 1), ∀ lambda ∈ K, ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q (_root_.iteratedDeriv k.1 S.limitResolvent lambda)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ a in l, ∀ lambda ∈ K, ∀ z ∈ Z,
      continuousLinearMapJointMultilinearCarrierRectangularJetSupDistance
        (continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierRectangularJetFromResolventFamily
          V m taylorOrder mixedOrder H
          (continuousLinearMapCompressedIteratedDerivRealResolventFamily J Q taylorOrder (F a) lambda z))
        (continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierRectangularJetFromResolventFamily
          V m taylorOrder mixedOrder H
          (continuousLinearMapCompressedIteratedDerivRealResolventFamily J Q taylorOrder S.limitResolvent lambda z)) < epsilon := by
  intro epsilon hepsilon
  let I := Fin (taylorOrder + 1) × Fin (mixedOrder + 1)
  let P : α → I → Prop := fun a kn => ∀ lambda ∈ K, ∀ z ∈ Z,
    ‖continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierFromResolvent
        V m kn.2.1 H (continuousLinearMapRealResolvent
          (continuousLinearMapCompression J Q (_root_.iteratedDeriv kn.1.1 (F a) lambda)) z) -
      continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierFromResolvent
        V m kn.2.1 H (continuousLinearMapRealResolvent
          (continuousLinearMapCompression J Q (_root_.iteratedDeriv kn.1.1 S.limitResolvent lambda)) z)‖ < epsilon
  have hkn : ∀ kn : I, ∀ᶠ a in l, P a kn := by
    intro kn
    exact S.iteratedDeriv_realResolventJointMultilinearTraceCarrier_finiteDimensionalCompression_tendsto_uniformOn_compact_product
      B L hLgap hLresolvent J Q kn.1.1 m kn.2.1 H K hKcompact hKupper hupper Z
      margin hmargin (hlimitMargin kn.1) M hM (hlimitNorm kn.1) epsilon hepsilon
  have hfinite : ∀ᶠ a in l, ∀ kn : I, P a kn := by
    change {a | ∀ kn : I, P a kn} ∈ l
    rw [show {a | ∀ kn : I, P a kn} = ⋂ kn ∈ (Finset.univ : Finset I), {a | P a kn} by
      ext a; simp]
    exact (Filter.biInter_finset_mem (Finset.univ : Finset I)).2 (fun kn _ => hkn kn)
  filter_upwards [hfinite] with a ha
  intro lambda hlambda z hz
  apply (continuousLinearMapJointMultilinearCarrierRectangularJetSupDistance_lt_iff _ _ epsilon).2
  intro k n
  simpa [continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierRectangularJetFromResolventFamily,
    continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierRectangularJetFromResolventFamily,
    continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierCompleteJetFromResolvent,
    continuousLinearMapCompressedIteratedDerivRealResolventFamily,
    continuousLinearMapCompressedRealResolventAt] using ha (k, n) lambda hlambda z hz

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
