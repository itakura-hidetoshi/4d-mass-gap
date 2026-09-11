import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventNewtonHermiteCompact
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

/-- Simultaneous uniform convergence of Newton-Hermite interpolants and their
exact remainders on a complete closed Taylor box for arbitrary joint time and
Taylor-degree nets, with no rate relation between the two nets. -/
theorem taylorPartialSum_realResolventNewtonHermitePair_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (interpolationDegree : ℕ)
    {m : Filter β} (a : β → α) (taylorDegree : β → ℕ)
    (ha : Tendsto a m l) (hdegree : Tendsto taylorDegree m atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap)
    (nodes : κ → Fin (interpolationDegree + 1) → ℝ) (eval : κ → ℝ)
    (T : Set κ) (Z : Set ℝ) (hnodes : ∀ q ∈ T, ∀ j, nodes q j ∈ Z)
    (heval : ∀ q ∈ T, eval q ∈ Z) (D : ℝ) (hD : 0 ≤ D)
    (hdist : ∀ q ∈ T, ∀ j, |eval q - nodes q j| ≤ D)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in m, ∀ p, box.Contains p → ∀ q ∈ T,
      ‖continuousLinearMapRealResolventNewtonHermitePair interpolationDegree
          (continuousLinearMapCompression J Q
            (continuousLinearMapTaylorPartialSum
              (F (a b)) p.center p.target (taylorDegree b))) (nodes q) (eval q) -
        continuousLinearMapRealResolventNewtonHermitePair interpolationDegree
          (continuousLinearMapCompression J Q (S.limitResolvent p.target))
          (nodes q) (eval q)‖ < epsilon := by
  let spectral : κ → Fin (interpolationDegree + 2) → ℝ := fun q =>
    continuousLinearMapFinAppend (nodes q) (eval q)
  let R : β → (ContinuousLinearMapTaylorParameterPoint × κ) →
      Fin (interpolationDegree + 2) → (V →L[ℝ] V) := fun b q j =>
    continuousLinearMapRealResolvent
      (continuousLinearMapCompression J Q
        (continuousLinearMapTaylorPartialSum
          (F (a b)) q.1.center q.1.target (taylorDegree b))) (spectral q.2 j)
  let R0 : (ContinuousLinearMapTaylorParameterPoint × κ) →
      Fin (interpolationDegree + 2) → (V →L[ℝ] V) := fun q j =>
    continuousLinearMapRealResolvent
      (continuousLinearMapCompression J Q (S.limitResolvent q.1.target))
      (spectral q.2 j)
  let I : Set (ContinuousLinearMapTaylorParameterPoint × κ) :=
    {q | box.Contains q.1 ∧ q.2 ∈ T}
  have hspectral : ∀ q ∈ T, ∀ j, spectral q j ∈ Z := by
    intro q hq j
    refine Fin.lastCases ?_ (fun r => ?_) j
    · simpa [spectral] using heval q hq
    · simpa [spectral] using hnodes q hq r
  have hR0 : ∀ q ∈ I, ∀ j, ‖R0 q j‖ ≤ M := by
    intro q hq j
    simpa [R0, continuousLinearMapRealResolventNorm] using
      hlimitNorm q.1 hq.1 (spectral q.2 j) (hspectral q.2 hq.2 j)
  have hR : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ b in m, ∀ q ∈ I, ∀ j, ‖R b q j - R0 q j‖ < eta := by
    intro eta heta
    have h :=
      S.taylorPartialSum_realResolvent_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
        B L hLgap hLresolvent J Q a taylorDegree ha hdegree box Z
        margin hmargin hlimitMargin M hM hlimitNorm eta heta
    filter_upwards [h] with b hb
    intro q hq j
    simpa [R, R0] using
      hb q.1 hq.1 (spectral q.2 j) (hspectral q.2 hq.2 j)
  have hpair :=
    finiteDimensional_realResolventNewtonHermitePair_variable_tendsto_uniformOn_of_componentwise
      interpolationDegree
      (fun q : ContinuousLinearMapTaylorParameterPoint × κ => nodes q.2)
      (fun q : ContinuousLinearMapTaylorParameterPoint × κ => eval q.2)
      D hD (fun q hq j => hdist q.2 hq.2 j) R R0 M hM hR0 hR
  intro epsilon hepsilon
  have h := hpair epsilon hepsilon
  filter_upwards [h] with b hb
  intro p hp q hq
  have hb' := hb (p, q) ⟨hp, hq⟩
  simpa [R, R0, spectral,
    continuousLinearMapRealResolventNewtonHermitePairObservable_eq] using hb'

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
