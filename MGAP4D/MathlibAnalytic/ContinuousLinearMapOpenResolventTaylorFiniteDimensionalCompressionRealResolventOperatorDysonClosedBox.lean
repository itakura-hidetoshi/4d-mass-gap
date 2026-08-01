import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventOperatorDysonCompact
import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventStabilityClosedBox
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

namespace ContinuousLinearMapOpenTaylorStrongLimitData

variable {α β E V : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [FiniteDimensional ℝ V]

/-- Uniform convergence of a fixed operator-perturbation Dyson coefficient on
a complete closed Taylor box for arbitrary joint time and Taylor-degree nets. -/
theorem taylorPartialSum_realResolventOperatorDysonCoefficient_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (dysonOrder : ℕ) (H : V →L[ℝ] V)
    {m : Filter β} (a : β → α) (taylorDegree : β → ℕ)
    (ha : Tendsto a m l) (hdegree : Tendsto taylorDegree m atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in m,
      ∀ p, box.Contains p → ∀ z ∈ Z,
        ‖continuousLinearMapRealResolventOperatorDysonCoefficient dysonOrder
            (continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (F (a b)) p.center p.target (taylorDegree b))) H z -
          continuousLinearMapRealResolventOperatorDysonCoefficient dysonOrder
            (continuousLinearMapCompression J Q (S.limitResolvent p.target)) H z‖ < epsilon := by
  let R : β → (ContinuousLinearMapTaylorParameterPoint × ℝ) →
      (V →L[ℝ] V) := fun b q =>
    continuousLinearMapRealResolvent
      (continuousLinearMapCompression J Q
        (continuousLinearMapTaylorPartialSum
          (F (a b)) q.1.center q.1.target (taylorDegree b))) q.2
  let R0 : (ContinuousLinearMapTaylorParameterPoint × ℝ) →
      (V →L[ℝ] V) := fun q =>
    continuousLinearMapRealResolvent
      (continuousLinearMapCompression J Q (S.limitResolvent q.1.target)) q.2
  let I : Set (ContinuousLinearMapTaylorParameterPoint × ℝ) :=
    {q | box.Contains q.1 ∧ q.2 ∈ Z}
  have hR0 : ∀ q ∈ I, ‖R0 q‖ ≤ M := by
    intro q hq
    simpa [R0, continuousLinearMapRealResolventNorm] using
      hlimitNorm q.1 hq.1 q.2 hq.2
  have hR : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ b in m, ∀ q ∈ I, ‖R b q - R0 q‖ < eta := by
    intro eta heta
    have h :=
      S.taylorPartialSum_realResolvent_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
        B L hLgap hLresolvent J Q a taylorDegree ha hdegree box Z
        margin hmargin hlimitMargin M hM hlimitNorm eta heta
    filter_upwards [h] with b hb
    intro q hq
    simpa [R, R0] using hb q.1 hq.1 q.2 hq.2
  have hdyson :=
    finiteDimensional_continuousObservable_tendsto_uniformOn
      R R0
      (fun T : V →L[ℝ] V =>
        continuousLinearMapRealResolventDysonCoefficientFromPair dysonOrder T H)
      (continuous_continuousLinearMapRealResolventDysonCoefficientFromFixedDirection
        dysonOrder H)
      M hM hR0 hR
  intro epsilon hepsilon
  have h := hdyson epsilon hepsilon
  filter_upwards [h] with b hb
  intro p hp z hz
  have hb' := hb (p, z) ⟨hp, hz⟩
  simpa [R, R0, continuousLinearMapRealResolventDysonCoefficientFromPair,
    continuousLinearMapRealResolventOperatorDysonCoefficient] using hb'

/-- Simultaneous closed-box convergence of the full finite operator Dyson jet
for arbitrary joint time and Taylor-degree nets. -/
theorem taylorPartialSum_realResolventOperatorDysonCoefficient_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint_rectangular
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (dysonOrder : ℕ) (H : V →L[ℝ] V)
    {m : Filter β} (a : β → α) (taylorDegree : β → ℕ)
    (ha : Tendsto a m l) (hdegree : Tendsto taylorDegree m atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap) (Z : Set ℝ)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ Z,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ Z,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in m,
      ∀ n : Fin (dysonOrder + 1), ∀ p, box.Contains p → ∀ z ∈ Z,
        ‖continuousLinearMapRealResolventOperatorDysonCoefficient n.1
            (continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (F (a b)) p.center p.target (taylorDegree b))) H z -
          continuousLinearMapRealResolventOperatorDysonCoefficient n.1
            (continuousLinearMapCompression J Q (S.limitResolvent p.target)) H z‖ < epsilon := by
  intro epsilon hepsilon
  let P : β → Fin (dysonOrder + 1) → Prop := fun b n =>
    ∀ p, box.Contains p → ∀ z ∈ Z,
      ‖continuousLinearMapRealResolventOperatorDysonCoefficient n.1
          (continuousLinearMapCompression J Q
            (continuousLinearMapTaylorPartialSum
              (F (a b)) p.center p.target (taylorDegree b))) H z -
        continuousLinearMapRealResolventOperatorDysonCoefficient n.1
          (continuousLinearMapCompression J Q (S.limitResolvent p.target)) H z‖ < epsilon
  have hn : ∀ n : Fin (dysonOrder + 1), ∀ᶠ b in m, P b n := by
    intro n
    exact
      S.taylorPartialSum_realResolventOperatorDysonCoefficient_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
        B L hLgap hLresolvent J Q n.1 H a taylorDegree ha hdegree
        box Z margin hmargin hlimitMargin M hM hlimitNorm epsilon hepsilon
  have hfinite : ∀ᶠ b in m, ∀ n : Fin (dysonOrder + 1), P b n := by
    change {b | ∀ n : Fin (dysonOrder + 1), P b n} ∈ m
    rw [show {b | ∀ n : Fin (dysonOrder + 1), P b n} =
      ⋂ n ∈ (Finset.univ : Finset (Fin (dysonOrder + 1))), {b | P b n} by
        ext b
        simp]
    exact (Filter.biInter_finset_mem
      (Finset.univ : Finset (Fin (dysonOrder + 1)))).2
      (fun n _ => hn n)
  filter_upwards [hfinite] with b hb
  intro n p hp z hz
  exact hb n p hp z hz

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
