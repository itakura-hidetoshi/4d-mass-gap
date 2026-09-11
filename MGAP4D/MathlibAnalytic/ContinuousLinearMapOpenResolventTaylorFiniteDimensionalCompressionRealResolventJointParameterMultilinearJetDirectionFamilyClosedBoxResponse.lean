import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventJointParameterMultilinearJetDirectionFamilyClosedBoxCarrier
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

/-- Complete closed-box convergence of the entire Banach-valued response jet
when approximation time, Taylor degree, and perturbation family vary jointly. -/
theorem taylorPartialSum_realResolventJointMultilinearResponseCarrierJet_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint_directionFamily_sup
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (φ : (V →L[ℝ] V) →L[ℝ] W)
    (mixedOrder m : ℕ) {f : Filter β} (a : β → α) (degree : β → ℕ)
    (H : β → Fin m → (V →L[ℝ] V)) (H0 : Fin m → (V →L[ℝ] V))
    (ha : Tendsto a f l) (hdegree : Tendsto degree f atTop) (hH : Tendsto H f (𝓝 H0))
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
      continuousLinearMapJointMultilinearCarrierJetSupDistance (V := V) (W := W)
        (continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierCompleteJetFromResolvent
          φ m mixedOrder (H b) (continuousLinearMapRealResolvent
            (continuousLinearMapCompression J Q (continuousLinearMapTaylorPartialSum
              (F (a b)) p.center p.target (degree b))) z))
        (continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierCompleteJetFromResolvent
          φ m mixedOrder H0 (continuousLinearMapRealResolvent
            (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z)) < epsilon := by
  let R : β → (ContinuousLinearMapTaylorParameterPoint × ℝ) → (V →L[ℝ] V) := fun b q =>
    continuousLinearMapRealResolvent (continuousLinearMapCompression J Q
      (continuousLinearMapTaylorPartialSum (F (a b)) q.1.center q.1.target (degree b))) q.2
  let R0 : (ContinuousLinearMapTaylorParameterPoint × ℝ) → (V →L[ℝ] V) := fun q =>
    continuousLinearMapRealResolvent
      (continuousLinearMapCompression J Q (S.limitResolvent q.1.target)) q.2
  let I : Set (ContinuousLinearMapTaylorParameterPoint × ℝ) :=
    {q | box.Contains q.1 ∧ q.2 ∈ Z}
  have hR0 : ∀ q ∈ I, ‖R0 q‖ ≤ M := by
    intro q hq
    simpa [R0, continuousLinearMapRealResolventNorm] using
      hlimitNorm q.1 hq.1 q.2 hq.2
  have hR : ∀ eta : ℝ, 0 < eta → ∀ᶠ b in f, ∀ q ∈ I,
      ‖R b q - R0 q‖ < eta := by
    intro eta heta
    have h :=
      S.taylorPartialSum_realResolvent_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
        B L hLgap hLresolvent J Q a degree ha hdegree box Z margin hmargin
        hlimitMargin M hM hlimitNorm eta heta
    filter_upwards [h] with b hb
    intro q hq
    simpa [R, R0] using hb q.1 hq.1 q.2 hq.2
  intro epsilon hepsilon
  let P : β → Fin (mixedOrder + 1) → Prop := fun b n => ∀ q ∈ I,
    ‖continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierFromResolvent
        φ m n.1 (H b) (R b q) -
      continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierFromResolvent
        φ m n.1 H0 (R0 q)‖ < epsilon
  have hn : ∀ n : Fin (mixedOrder + 1), ∀ᶠ b in f, P b n := by
    intro n
    have h := finiteDimensional_directionFamilyObservable_tendsto_uniformOn
      R R0 H H0
      (fun q =>
        continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierFromResolvent
          φ m n.1 q.2 q.1)
      (continuous_continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierFromResolvent_directionFamily
        φ m n.1)
      M hM hR0 hR hH epsilon hepsilon
    simpa [P] using h
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
  simpa [P, R, R0,
    continuousLinearMapJointSpectralOperatorRealResolventMultilinearResponseCarrierCompleteJetFromResolvent] using
    hb n (p, z) ⟨hp, hz⟩

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
