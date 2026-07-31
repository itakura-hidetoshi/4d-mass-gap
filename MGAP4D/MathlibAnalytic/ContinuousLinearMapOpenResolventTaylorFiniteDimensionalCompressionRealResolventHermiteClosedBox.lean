import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventHermiteCompact
import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventStabilityClosedBox
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

namespace ContinuousLinearMapOpenTaylorStrongLimitData

variable {α β κ E V : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [FiniteDimensional ℝ V]

/-- Uniform convergence of a fixed normalized multipoint Hermite coefficient
on a complete closed Taylor box for arbitrary joint time/Taylor-degree nets. -/
theorem taylorPartialSum_realResolventHermiteCoefficient_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (order : ℕ)
    {m : Filter β} (a : β → α) (degree : β → ℕ)
    (ha : Tendsto a m l) (hdegree : Tendsto degree m atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap)
    (nodes : κ → Fin (order + 1) → ℝ) (T : Set κ) (Z : Set ℝ)
    (hnodes : ∀ q ∈ T, ∀ j, nodes q j ∈ Z)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in m,
      ∀ p, box.Contains p → ∀ q ∈ T,
        ‖continuousLinearMapRealResolventHermiteCoefficient order
            (continuousLinearMapCompression J Q (continuousLinearMapTaylorPartialSum
              (F (a b)) p.center p.target (degree b))) (nodes q) -
          continuousLinearMapRealResolventHermiteCoefficient order
            (continuousLinearMapCompression J Q (S.limitResolvent p.target))
            (nodes q)‖ < epsilon := by
  let R : β → (ContinuousLinearMapTaylorParameterPoint × κ) →
      Fin (order + 1) → (V →L[ℝ] V) := fun b q j =>
    continuousLinearMapRealResolvent
      (continuousLinearMapCompression J Q
        (continuousLinearMapTaylorPartialSum
          (F (a b)) q.1.center q.1.target (degree b))) (nodes q.2 j)
  let R0 : (ContinuousLinearMapTaylorParameterPoint × κ) →
      Fin (order + 1) → (V →L[ℝ] V) := fun q j =>
    continuousLinearMapRealResolvent
      (continuousLinearMapCompression J Q
        (S.limitResolvent q.1.target)) (nodes q.2 j)
  let I : Set (ContinuousLinearMapTaylorParameterPoint × κ) :=
    {q | box.Contains q.1 ∧ q.2 ∈ T}
  have hR0 : ∀ q ∈ I, ∀ j, ‖R0 q j‖ ≤ M := by
    intro q hq j
    simpa [R0, continuousLinearMapRealResolventNorm] using
      hlimitNorm q.1 hq.1 (nodes q.2 j) (hnodes q.2 hq.2 j)
  have hR : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ b in m, ∀ q ∈ I, ∀ j, ‖R b q j - R0 q j‖ < eta := by
    intro eta heta
    have h :=
      S.taylorPartialSum_realResolvent_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
        B L hLgap hLresolvent J Q a degree ha hdegree box Z
        margin hmargin hlimitMargin M hM hlimitNorm eta heta
    filter_upwards [h] with b hb
    intro q hq j
    simpa [R, R0] using
      hb q.1 hq.1 (nodes q.2 j) (hnodes q.2 hq.2 j)
  have hcoeff :=
    finiteDimensional_realResolventHermiteObservable_tendsto_uniformOn_of_componentwise
      order R R0 M hM hR0 hR
  intro epsilon hepsilon
  have h := hcoeff epsilon hepsilon
  filter_upwards [h] with b hb
  intro p hp q hq
  simpa [R, R0, continuousLinearMapRealResolventHermiteCoefficient] using
    hb (p, q) ⟨hp, hq⟩

/-- Simultaneous uniform convergence of the complete normalized Hermite jet
through a fixed finite order on a complete closed Taylor box. -/
theorem taylorPartialSum_realResolventHermiteJet_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (order : ℕ)
    {m : Filter β} (a : β → α) (degree : β → ℕ)
    (ha : Tendsto a m l) (hdegree : Tendsto degree m atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap)
    (nodes : κ → Fin (order + 1) → ℝ) (T : Set κ) (Z : Set ℝ)
    (hnodes : ∀ q ∈ T, ∀ j, nodes q j ∈ Z)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in m,
      ∀ p, box.Contains p → ∀ q ∈ T,
        ‖continuousLinearMapRealResolventHermiteJet order (fun j =>
            continuousLinearMapRealResolvent
              (continuousLinearMapCompression J Q (continuousLinearMapTaylorPartialSum
                (F (a b)) p.center p.target (degree b))) (nodes q j)) -
          continuousLinearMapRealResolventHermiteJet order (fun j =>
            continuousLinearMapRealResolvent
              (continuousLinearMapCompression J Q (S.limitResolvent p.target))
              (nodes q j))‖ < epsilon := by
  let R : β → (ContinuousLinearMapTaylorParameterPoint × κ) →
      Fin (order + 1) → (V →L[ℝ] V) := fun b q j =>
    continuousLinearMapRealResolvent
      (continuousLinearMapCompression J Q
        (continuousLinearMapTaylorPartialSum
          (F (a b)) q.1.center q.1.target (degree b))) (nodes q.2 j)
  let R0 : (ContinuousLinearMapTaylorParameterPoint × κ) →
      Fin (order + 1) → (V →L[ℝ] V) := fun q j =>
    continuousLinearMapRealResolvent
      (continuousLinearMapCompression J Q
        (S.limitResolvent q.1.target)) (nodes q.2 j)
  let I : Set (ContinuousLinearMapTaylorParameterPoint × κ) :=
    {q | box.Contains q.1 ∧ q.2 ∈ T}
  have hR0 : ∀ q ∈ I, ∀ j, ‖R0 q j‖ ≤ M := by
    intro q hq j
    simpa [R0, continuousLinearMapRealResolventNorm] using
      hlimitNorm q.1 hq.1 (nodes q.2 j) (hnodes q.2 hq.2 j)
  have hR : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ b in m, ∀ q ∈ I, ∀ j, ‖R b q j - R0 q j‖ < eta := by
    intro eta heta
    have h :=
      S.taylorPartialSum_realResolvent_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
        B L hLgap hLresolvent J Q a degree ha hdegree box Z
        margin hmargin hlimitMargin M hM hlimitNorm eta heta
    filter_upwards [h] with b hb
    intro q hq j
    simpa [R, R0] using
      hb q.1 hq.1 (nodes q.2 j) (hnodes q.2 hq.2 j)
  have hjet :=
    finiteDimensional_realResolventHermiteJet_tendsto_uniformOn_of_componentwise
      order R R0 M hM hR0 hR
  intro epsilon hepsilon
  have h := hjet epsilon hepsilon
  filter_upwards [h] with b hb
  intro p hp q hq
  simpa [R, R0] using hb (p, q) ⟨hp, hq⟩

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
