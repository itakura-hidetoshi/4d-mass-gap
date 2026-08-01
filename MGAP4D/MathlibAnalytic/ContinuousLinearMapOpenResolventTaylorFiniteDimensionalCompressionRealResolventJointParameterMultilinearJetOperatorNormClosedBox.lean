import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterMultilinearJetOperatorNormCompact
import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventStabilityClosedBox
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped BigOperators ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

namespace ContinuousLinearMapOpenTaylorStrongLimitData

variable {α β E V W : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Complete closed-box convergence of the full joint Fréchet multilinear
carrier in operator norm for arbitrary approximation-time and Taylor-degree
nets. -/
theorem taylorPartialSum_realResolventJointMultilinearCarrier_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (m n : ℕ) (H : Fin m → (V →L[ℝ] V))
    {f : Filter β} (a : β → α) (degree : β → ℕ) (ha : Tendsto a f l)
    (hdegree : Tendsto degree f atTop) (box : ContinuousLinearMapClosedTaylorParameterBox gap)
    (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤
      |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in f, ∀ p, box.Contains p → ∀ z ∈ Z,
      ‖continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierFromResolvent m n H
          (continuousLinearMapRealResolvent (continuousLinearMapCompression J Q
            (continuousLinearMapTaylorPartialSum (F (a b)) p.center p.target (degree b))) z) -
        continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierFromResolvent m n H
          (continuousLinearMapRealResolvent
            (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z)‖ < epsilon := by
  let R : β → (ContinuousLinearMapTaylorParameterPoint × ℝ) → (V →L[ℝ] V) := fun b q =>
    continuousLinearMapRealResolvent (continuousLinearMapCompression J Q
      (continuousLinearMapTaylorPartialSum
        (F (a b)) q.1.center q.1.target (degree b))) q.2
  let R0 : (ContinuousLinearMapTaylorParameterPoint × ℝ) → (V →L[ℝ] V) := fun q =>
    continuousLinearMapRealResolvent
      (continuousLinearMapCompression J Q (S.limitResolvent q.1.target)) q.2
  let I : Set (ContinuousLinearMapTaylorParameterPoint × ℝ) :=
    {q | box.Contains q.1 ∧ q.2 ∈ Z}
  have hR0 : ∀ q ∈ I, ‖R0 q‖ ≤ M := by
    intro q hq
    simpa [R0, continuousLinearMapRealResolventNorm] using
      hlimitNorm q.1 hq.1 q.2 hq.2
  have hR : ∀ eta : ℝ, 0 < eta → ∀ᶠ b in f, ∀ q ∈ I, ‖R b q - R0 q‖ < eta := by
    intro eta heta
    have h :=
      S.taylorPartialSum_realResolvent_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
        B L hLgap hLresolvent J Q a degree ha hdegree box Z margin hmargin
        hlimitMargin M hM hlimitNorm eta heta
    filter_upwards [h] with b hb
    intro q hq
    simpa [R, R0] using hb q.1 hq.1 q.2 hq.2
  have hcarrier :=
    finiteDimensional_continuousObservable_tendsto_uniformOn R R0
      (fun T : V →L[ℝ] V =>
        continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierFromResolvent
          m n H T)
      (continuous_continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierFromResolvent
        m n H) M hM hR0 hR
  intro epsilon hepsilon
  have h := hcarrier epsilon hepsilon
  filter_upwards [h] with b hb
  intro p hp z hz
  simpa [R, R0] using hb (p, z) ⟨hp, hz⟩

/-- Complete closed-box convergence of every component in a finite full-carrier
jet for arbitrary joint nets. -/
theorem taylorPartialSum_realResolventJointMultilinearCarrier_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint_rectangular
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (mixedOrder m : ℕ)
    (H : Fin m → (V →L[ℝ] V)) {f : Filter β} (a : β → α) (degree : β → ℕ)
    (ha : Tendsto a f l) (hdegree : Tendsto degree f atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤
      |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in f, ∀ n : Fin (mixedOrder + 1),
      ∀ p, box.Contains p → ∀ z ∈ Z,
        ‖continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierFromResolvent m n.1 H
            (continuousLinearMapRealResolvent (continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum (F (a b)) p.center p.target (degree b))) z) -
          continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierFromResolvent m n.1 H
            (continuousLinearMapRealResolvent
              (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z)‖ < epsilon := by
  intro epsilon hepsilon
  let P : β → Fin (mixedOrder + 1) → Prop := fun b n =>
    ∀ p, box.Contains p → ∀ z ∈ Z,
      ‖continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierFromResolvent m n.1 H
          (continuousLinearMapRealResolvent (continuousLinearMapCompression J Q
            (continuousLinearMapTaylorPartialSum (F (a b)) p.center p.target (degree b))) z) -
        continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierFromResolvent m n.1 H
          (continuousLinearMapRealResolvent
            (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z)‖ < epsilon
  have hn : ∀ n : Fin (mixedOrder + 1), ∀ᶠ b in f, P b n := by
    intro n
    exact
      S.taylorPartialSum_realResolventJointMultilinearCarrier_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
        B L hLgap hLresolvent J Q m n.1 H a degree ha hdegree box Z margin
        hmargin hlimitMargin M hM hlimitNorm epsilon hepsilon
  have hfinite : ∀ᶠ b in f, ∀ n : Fin (mixedOrder + 1), P b n := by
    change {b | ∀ n : Fin (mixedOrder + 1), P b n} ∈ f
    rw [show {b | ∀ n : Fin (mixedOrder + 1), P b n} =
      ⋂ n ∈ (Finset.univ : Finset (Fin (mixedOrder + 1))), {b | P b n} by
        ext b
        simp]
    exact (Filter.biInter_finset_mem
      (Finset.univ : Finset (Fin (mixedOrder + 1)))).2 (fun n _ => hn n)
  filter_upwards [hfinite] with b hb
  intro n p hp z hz
  exact hb n p hp z hz

/-- Complete closed-box convergence of a Banach-valued observation of the full
joint Fréchet carrier in its multilinear operator norm. -/
theorem taylorPartialSum_realResolventJointMultilinearResponseCarrier_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (φ : (V →L[ℝ] V) →L[ℝ] W)
    (m n : ℕ) (H : Fin m → (V →L[ℝ] V)) {f : Filter β}
    (a : β → α) (degree : β → ℕ) (ha : Tendsto a f l) (hdegree : Tendsto degree f atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤
      |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in f, ∀ p, box.Contains p → ∀ z ∈ Z,
      ‖continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierFromResolvent φ m n H
          (continuousLinearMapRealResolvent (continuousLinearMapCompression J Q
            (continuousLinearMapTaylorPartialSum (F (a b)) p.center p.target (degree b))) z) -
        continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierFromResolvent φ m n H
          (continuousLinearMapRealResolvent
            (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z)‖ < epsilon := by
  let R : β → (ContinuousLinearMapTaylorParameterPoint × ℝ) → (V →L[ℝ] V) := fun b q =>
    continuousLinearMapRealResolvent (continuousLinearMapCompression J Q
      (continuousLinearMapTaylorPartialSum
        (F (a b)) q.1.center q.1.target (degree b))) q.2
  let R0 : (ContinuousLinearMapTaylorParameterPoint × ℝ) → (V →L[ℝ] V) := fun q =>
    continuousLinearMapRealResolvent
      (continuousLinearMapCompression J Q (S.limitResolvent q.1.target)) q.2
  let I : Set (ContinuousLinearMapTaylorParameterPoint × ℝ) :=
    {q | box.Contains q.1 ∧ q.2 ∈ Z}
  have hR0 : ∀ q ∈ I, ‖R0 q‖ ≤ M := by
    intro q hq
    simpa [R0, continuousLinearMapRealResolventNorm] using
      hlimitNorm q.1 hq.1 q.2 hq.2
  have hR : ∀ eta : ℝ, 0 < eta → ∀ᶠ b in f, ∀ q ∈ I, ‖R b q - R0 q‖ < eta := by
    intro eta heta
    have h :=
      S.taylorPartialSum_realResolvent_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
        B L hLgap hLresolvent J Q a degree ha hdegree box Z margin hmargin
        hlimitMargin M hM hlimitNorm eta heta
    filter_upwards [h] with b hb
    intro q hq
    simpa [R, R0] using hb q.1 hq.1 q.2 hq.2
  have hresponse :=
    finiteDimensional_continuousObservable_tendsto_uniformOn R R0
      (fun T : V →L[ℝ] V =>
        continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierFromResolvent
          φ m n H T)
      (continuous_continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierFromResolvent
        φ m n H) M hM hR0 hR
  intro epsilon hepsilon
  have h := hresponse epsilon hepsilon
  filter_upwards [h] with b hb
  intro p hp z hz
  simpa [R, R0] using hb (p, z) ⟨hp, hz⟩

/-- Complete closed-box convergence of the full basis-independent trace
carrier. -/
theorem taylorPartialSum_realResolventJointMultilinearTraceCarrier_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (m n : ℕ) (H : Fin m → (V →L[ℝ] V))
    {f : Filter β} (a : β → α) (degree : β → ℕ) (ha : Tendsto a f l)
    (hdegree : Tendsto degree f atTop) (box : ContinuousLinearMapClosedTaylorParameterBox gap)
    (Z : Set ℝ) (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z, margin ≤
      |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in f, ∀ p, box.Contains p → ∀ z ∈ Z,
      ‖continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierFromResolvent V m n H
          (continuousLinearMapRealResolvent (continuousLinearMapCompression J Q
            (continuousLinearMapTaylorPartialSum (F (a b)) p.center p.target (degree b))) z) -
        continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierFromResolvent V m n H
          (continuousLinearMapRealResolvent
            (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z)‖ < epsilon := by
  simpa [continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierFromResolvent] using
    S.taylorPartialSum_realResolventJointMultilinearResponseCarrier_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
      B L hLgap hLresolvent J Q (continuousLinearMapTrace (V := V)) m n H
      a degree ha hdegree box Z margin hmargin hlimitMargin M hM hlimitNorm

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
