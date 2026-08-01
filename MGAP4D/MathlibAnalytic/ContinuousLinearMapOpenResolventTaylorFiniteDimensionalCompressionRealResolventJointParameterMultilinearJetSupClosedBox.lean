import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterMultilinearJetSupCompact
import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterMultilinearJetOperatorNormClosedBox
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

/-- Complete closed-box convergence of the entire finite joint Fréchet carrier
jet in one maximum component norm for arbitrary joint nets. -/
theorem taylorPartialSum_realResolventJointMultilinearCarrierJet_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint_sup
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
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in f, ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapJointMultilinearCarrierJetSupDistance
        (V := V) (W := V →L[ℝ] V)
        (continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierJetFromResolvent
          m (mixedOrder + 1) H
          (continuousLinearMapRealResolvent (continuousLinearMapCompression J Q
            (continuousLinearMapTaylorPartialSum (F (a b)) p.center p.target (degree b))) z))
        (continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierJetFromResolvent
          m (mixedOrder + 1) H
          (continuousLinearMapRealResolvent
            (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z)) < epsilon := by
  intro epsilon hepsilon
  have h :=
    S.taylorPartialSum_realResolventJointMultilinearCarrier_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint_rectangular
      B L hLgap hLresolvent J Q mixedOrder m H a degree ha hdegree box Z
      margin hmargin hlimitMargin M hM hlimitNorm epsilon hepsilon
  filter_upwards [h] with b hb
  intro p hp z hz
  apply (continuousLinearMapJointMultilinearCarrierJetSupDistance_lt_iff
    (V := V) (W := V →L[ℝ] V) _ _ epsilon).2
  intro n
  simpa [continuousLinearMapJointSpectralOperatorRealResolventMultilinearCarrierJetFromResolvent] using
    hb n p hp z hz

/-- Complete closed-box convergence of the entire finite Banach-valued
response jet in one maximum component norm. -/
theorem taylorPartialSum_realResolventJointMultilinearResponseCarrierJet_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint_sup
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (φ : (V →L[ℝ] V) →L[ℝ] W)
    (mixedOrder m : ℕ) (H : Fin m → (V →L[ℝ] V)) {f : Filter β}
    (a : β → α) (degree : β → ℕ) (ha : Tendsto a f l)
    (hdegree : Tendsto degree f atTop)
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
      continuousLinearMapJointMultilinearCarrierJetSupDistance
        (V := V) (W := W)
        (continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierCompleteJetFromResolvent
          φ m mixedOrder H
          (continuousLinearMapRealResolvent (continuousLinearMapCompression J Q
            (continuousLinearMapTaylorPartialSum (F (a b)) p.center p.target (degree b))) z))
        (continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierCompleteJetFromResolvent
          φ m mixedOrder H
          (continuousLinearMapRealResolvent
            (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z)) < epsilon := by
  intro epsilon hepsilon
  let P : β → Fin (mixedOrder + 1) → Prop := fun b n =>
    ∀ p, box.Contains p → ∀ z ∈ Z,
      ‖continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierFromResolvent
          φ m n.1 H (continuousLinearMapRealResolvent (continuousLinearMapCompression J Q
            (continuousLinearMapTaylorPartialSum (F (a b)) p.center p.target (degree b))) z) -
        continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierFromResolvent
          φ m n.1 H (continuousLinearMapRealResolvent
            (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z)‖ < epsilon
  have hn : ∀ n : Fin (mixedOrder + 1), ∀ᶠ b in f, P b n := by
    intro n
    exact
      S.taylorPartialSum_realResolventJointMultilinearResponseCarrier_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
        B L hLgap hLresolvent J Q φ m n.1 H a degree ha hdegree box Z
        margin hmargin hlimitMargin M hM hlimitNorm epsilon hepsilon
  have hfinite : ∀ᶠ b in f, ∀ n : Fin (mixedOrder + 1), P b n := by
    change {b | ∀ n : Fin (mixedOrder + 1), P b n} ∈ f
    rw [show {b | ∀ n : Fin (mixedOrder + 1), P b n} =
      ⋂ n ∈ (Finset.univ : Finset (Fin (mixedOrder + 1))), {b | P b n} by
        ext b
        simp]
    exact (Filter.biInter_finset_mem
      (Finset.univ : Finset (Fin (mixedOrder + 1)))).2 (fun n _ => hn n)
  filter_upwards [hfinite] with b hb
  intro p hp z hz
  apply (continuousLinearMapJointMultilinearCarrierJetSupDistance_lt_iff
    (V := V) (W := W) _ _ epsilon).2
  intro n
  simpa [continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierCompleteJetFromResolvent] using
    hb n p hp z hz

/-- Complete closed-box convergence of the entire basis-independent trace jet
in one maximum component norm. -/
theorem taylorPartialSum_realResolventJointMultilinearTraceCarrierJet_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint_sup
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
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in f, ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapJointMultilinearCarrierJetSupDistance
        (V := V) (W := ℝ)
        (continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierCompleteJetFromResolvent
          V m mixedOrder H
          (continuousLinearMapRealResolvent (continuousLinearMapCompression J Q
            (continuousLinearMapTaylorPartialSum (F (a b)) p.center p.target (degree b))) z))
        (continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierCompleteJetFromResolvent
          V m mixedOrder H
          (continuousLinearMapRealResolvent
            (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z)) < epsilon := by
  intro epsilon hepsilon
  let P : β → Fin (mixedOrder + 1) → Prop := fun b n =>
    ∀ p, box.Contains p → ∀ z ∈ Z,
      ‖continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierFromResolvent
          V m n.1 H (continuousLinearMapRealResolvent (continuousLinearMapCompression J Q
            (continuousLinearMapTaylorPartialSum (F (a b)) p.center p.target (degree b))) z) -
        continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierFromResolvent
          V m n.1 H (continuousLinearMapRealResolvent
            (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z)‖ < epsilon
  have hn : ∀ n : Fin (mixedOrder + 1), ∀ᶠ b in f, P b n := by
    intro n
    exact
      S.taylorPartialSum_realResolventJointMultilinearTraceCarrier_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
        B L hLgap hLresolvent J Q m n.1 H a degree ha hdegree box Z
        margin hmargin hlimitMargin M hM hlimitNorm epsilon hepsilon
  have hfinite : ∀ᶠ b in f, ∀ n : Fin (mixedOrder + 1), P b n := by
    change {b | ∀ n : Fin (mixedOrder + 1), P b n} ∈ f
    rw [show {b | ∀ n : Fin (mixedOrder + 1), P b n} =
      ⋂ n ∈ (Finset.univ : Finset (Fin (mixedOrder + 1))), {b | P b n} by
        ext b
        simp]
    exact (Filter.biInter_finset_mem
      (Finset.univ : Finset (Fin (mixedOrder + 1)))).2 (fun n _ => hn n)
  filter_upwards [hfinite] with b hb
  intro p hp z hz
  apply (continuousLinearMapJointMultilinearCarrierJetSupDistance_lt_iff
    (V := V) (W := ℝ) _ _ epsilon).2
  intro n
  simpa [continuousLinearMapJointSpectralOperatorRealResolventMultilinearTraceCarrierCompleteJetFromResolvent,
    continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierCompleteJetFromResolvent] using
    hb n p hp z hz

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
