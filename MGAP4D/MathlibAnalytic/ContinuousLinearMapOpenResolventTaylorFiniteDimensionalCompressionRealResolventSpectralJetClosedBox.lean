import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionRealResolventSpectralJetCompact
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

/-- Uniform convergence of a fixed algebraic spectral jet on a complete closed
Taylor box for arbitrary joint time/Taylor-degree nets. -/
theorem taylorPartialSum_realResolventSpectralJet_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (spectralOrder : ℕ)
    {m : Filter β} (a : β → α) (degree : β → ℕ)
    (ha : Tendsto a m l) (hdegree : Tendsto degree m atTop)
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
        ‖continuousLinearMapRealResolventSpectralJet spectralOrder
            (continuousLinearMapRealResolvent
              (continuousLinearMapCompression J Q
                (continuousLinearMapTaylorPartialSum
                  (F (a b)) p.center p.target (degree b))) z) -
          continuousLinearMapRealResolventSpectralJet spectralOrder
            (continuousLinearMapRealResolvent
              (continuousLinearMapCompression J Q
                (S.limitResolvent p.target)) z)‖ < epsilon := by
  let R := fun b q =>
    continuousLinearMapRealResolvent
      (continuousLinearMapCompression J Q
        (continuousLinearMapTaylorPartialSum
          (F (a b)) q.1.center q.1.target (degree b))) q.2
  let R0 := fun q =>
    continuousLinearMapRealResolvent
      (continuousLinearMapCompression J Q
        (S.limitResolvent q.1.target)) q.2
  let T := {q | box.Contains q.1 ∧ q.2 ∈ Z}
  have hR0 : ∀ q ∈ T, ‖R0 q‖ ≤ M := by
    intro q hq
    exact hlimitNorm q.1 hq.1 q.2 hq.2
  have hR : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ b in m, ∀ q ∈ T, ‖R b q - R0 q‖ < eta := by
    intro eta heta
    have h :=
      S.taylorPartialSum_realResolvent_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
        B L hLgap hLresolvent J Q a degree ha hdegree box Z
        margin hmargin hlimitMargin M hM hlimitNorm eta heta
    filter_upwards [h] with b hb
    intro q hq
    exact hb q.1 hq.1 q.2 hq.2
  have hjet := finiteDimensional_realResolventSpectralJet_tendsto_uniformOn
    R R0 spectralOrder M hM hR0 hR
  intro epsilon hepsilon
  have h := hjet epsilon hepsilon
  filter_upwards [h] with b hb
  intro p hp z hz
  exact hb (p, z) ⟨hp, hz⟩

/-- Simultaneous uniform convergence of all algebraic spectral jets through a
fixed finite order on a complete closed Taylor box. -/
theorem taylorPartialSum_realResolventSpectralJetVector_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (spectralOrder : ℕ)
    {m : Filter β} (a : β → α) (degree : β → ℕ)
    (ha : Tendsto a m l) (hdegree : Tendsto degree m atTop)
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
        ‖continuousLinearMapRealResolventSpectralJetVector spectralOrder
            (continuousLinearMapRealResolvent
              (continuousLinearMapCompression J Q
                (continuousLinearMapTaylorPartialSum
                  (F (a b)) p.center p.target (degree b))) z) -
          continuousLinearMapRealResolventSpectralJetVector spectralOrder
            (continuousLinearMapRealResolvent
              (continuousLinearMapCompression J Q
                (S.limitResolvent p.target)) z)‖ < epsilon := by
  let R := fun b q =>
    continuousLinearMapRealResolvent
      (continuousLinearMapCompression J Q
        (continuousLinearMapTaylorPartialSum
          (F (a b)) q.1.center q.1.target (degree b))) q.2
  let R0 := fun q =>
    continuousLinearMapRealResolvent
      (continuousLinearMapCompression J Q
        (S.limitResolvent q.1.target)) q.2
  let T := {q | box.Contains q.1 ∧ q.2 ∈ Z}
  have hR0 : ∀ q ∈ T, ‖R0 q‖ ≤ M := by
    intro q hq
    exact hlimitNorm q.1 hq.1 q.2 hq.2
  have hR : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ b in m, ∀ q ∈ T, ‖R b q - R0 q‖ < eta := by
    intro eta heta
    have h :=
      S.taylorPartialSum_realResolvent_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
        B L hLgap hLresolvent J Q a degree ha hdegree box Z
        margin hmargin hlimitMargin M hM hlimitNorm eta heta
    filter_upwards [h] with b hb
    intro q hq
    exact hb q.1 hq.1 q.2 hq.2
  have hjet := finiteDimensional_realResolventSpectralJetVector_tendsto_uniformOn
    R R0 spectralOrder M hM hR0 hR
  intro epsilon hepsilon
  have h := hjet epsilon hepsilon
  filter_upwards [h] with b hb
  intro p hp z hz
  exact hb (p, z) ⟨hp, hz⟩

/-- On an open common real spectral region, the closed-box joint limit is
exactly uniform convergence of the true operator-norm spectral derivatives. -/
theorem taylorPartialSum_realResolvent_iteratedSpectralDeriv_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V) (spectralOrder : ℕ)
    {m : Filter β} (a : β → α) (degree : β → ℕ)
    (ha : Tendsto a m l) (hdegree : Tendsto degree m atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap)
    (U : Set ℝ) (hU : IsOpen U)
    (margin : ℝ) (hmargin : 0 < margin)
    (hlimitMargin : ∀ p, box.Contains p → ∀ z ∈ U,
      margin ≤ |continuousLinearMapCharacteristicDeterminant
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z|)
    (M : ℝ) (hM : 0 ≤ M)
    (hlimitNorm : ∀ p, box.Contains p → ∀ z ∈ U,
      continuousLinearMapRealResolventNorm
        (continuousLinearMapCompression J Q (S.limitResolvent p.target)) z ≤ M) :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in m,
      ∀ p, box.Contains p → ∀ z ∈ U,
        ‖_root_.iteratedDeriv spectralOrder
            (fun w => continuousLinearMapRealResolvent
              (continuousLinearMapCompression J Q
                (continuousLinearMapTaylorPartialSum
                  (F (a b)) p.center p.target (degree b))) w) z -
          _root_.iteratedDeriv spectralOrder
            (fun w => continuousLinearMapRealResolvent
              (continuousLinearMapCompression J Q
                (S.limitResolvent p.target)) w) z‖ < epsilon := by
  have hstable :=
    S.taylorPartialSum_realResolvent_finiteDimensionalCompression_eventually_stable_uniform_closedBox_of_joint
      B L hLgap hLresolvent J Q a degree ha hdegree box U
      margin hmargin hlimitMargin M hM hlimitNorm 1 zero_lt_one
  have hjet :=
    S.taylorPartialSum_realResolventSpectralJet_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
      B L hLgap hLresolvent J Q spectralOrder a degree ha hdegree box U
      margin hmargin hlimitMargin M hM hlimitNorm
  intro epsilon hepsilon
  have hj := hjet epsilon hepsilon
  filter_upwards [hstable, hj] with b hb hbj
  intro p hp z hz
  let Ab : V →L[ℝ] V := continuousLinearMapCompression J Q
    (continuousLinearMapTaylorPartialSum
      (F (a b)) p.center p.target (degree b))
  let A0 : V →L[ℝ] V := continuousLinearMapCompression J Q
    (S.limitResolvent p.target)
  have hMb : 0 ≤ 2 * (M + 1) := by nlinarith
  have hunitB : ∀ w ∈ U, IsUnit (continuousLinearMapRealShift Ab w) := by
    intro w hw
    exact (hb p hp w hw).1
  have hnormB : ∀ w ∈ U,
      continuousLinearMapRealResolventNorm Ab w ≤ 2 * (M + 1) := by
    intro w hw
    exact (hb p hp w hw).2.1
  have hunit0 : ∀ w ∈ U, IsUnit (continuousLinearMapRealShift A0 w) := by
    intro w hw
    apply continuousLinearMapRealShift_isUnit_of_characteristicDeterminant_ne_zero
    exact abs_pos.mp (lt_of_lt_of_le hmargin (hlimitMargin p hp w hw))
  have hnorm0 : ∀ w ∈ U, continuousLinearMapRealResolventNorm A0 w ≤ M := by
    intro w hw
    exact hlimitNorm p hp w hw
  have hAb := continuousLinearMapRealResolventSpectralJet_eq_iteratedDeriv
    Ab U (2 * (M + 1)) hU hMb hunitB hnormB spectralOrder hz
  have hA0 := continuousLinearMapRealResolventSpectralJet_eq_iteratedDeriv
    A0 U M hU hM hunit0 hnorm0 spectralOrder hz
  rw [← hAb, ← hA0]
  exact hbj p hp z hz

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
