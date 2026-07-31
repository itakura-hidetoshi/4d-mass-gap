import MGAP4D.MathlibAnalytic.ContinuousLinearMapOpenResolventTaylorFiniteDimensionalCompressionDeterminantCompactJet
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 5000000

namespace ContinuousLinearMapOpenTaylorStrongLimitData

variable {α β E V W : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [FiniteDimensional ℝ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Every continuous observable of compressed Taylor partial sums converges
uniformly on a full closed Taylor box for arbitrary joint time/degree nets. -/
theorem taylorPartialSum_continuousObservable_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
    {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
    (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
    (L : ContinuousLinearMapOpenResolventNormBoundData E)
    (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
    (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
    (Phi : (V →L[ℝ] V) → W) (hPhi : Continuous Phi)
    {m : Filter β} (a : β → α) (degree : β → ℕ)
    (ha : Tendsto a m l) (hdegree : Tendsto degree m atTop)
    (box : ContinuousLinearMapClosedTaylorParameterBox gap) :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ b in m, ∀ p, box.Contains p →
        ‖Phi (continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (F (a b)) p.center p.target (degree b))) -
          Phi (continuousLinearMapCompression J Q
              (S.limitResolvent p.target))‖ < epsilon := by
  let upper : ℝ := box.lambdaMax + box.rMax
  let R : ℝ := ‖Q‖ * (gap - upper)⁻¹ * ‖J‖
  have hupper : upper < gap := by
    simpa [upper] using box.upper_lt_gap
  have hmargin : 0 < gap - upper := sub_pos.mpr hupper
  have hinv : 0 ≤ (gap - upper)⁻¹ := inv_nonneg.mpr hmargin.le
  have hR : 0 ≤ R := by
    dsimp [R]
    exact mul_nonneg (mul_nonneg (norm_nonneg Q) hinv) (norm_nonneg J)
  have hlimit : ∀ p ∈ {p | box.Contains p},
      ‖continuousLinearMapCompression J Q
          (S.limitResolvent p.target)‖ ≤ R := by
    intro p hp
    have h := L.resolvent_finiteDimensionalCompression_norm_le_on_Iic
      J Q (by simpa [hLgap] using hupper) (box.target_le_upper hp)
    simpa [R, upper, hLgap, hLresolvent] using h
  have hoperator : ∀ eta : ℝ, 0 < eta →
      ∀ᶠ b in m, ∀ p ∈ {p | box.Contains p},
        ‖continuousLinearMapCompression J Q
              (continuousLinearMapTaylorPartialSum
                (F (a b)) p.center p.target (degree b)) -
          continuousLinearMapCompression J Q
              (S.limitResolvent p.target)‖ < eta := by
    intro eta heta
    have h :=
      S.taylorPartialSum_tendsto_limitResolvent_finiteDimensionalCompression_uniform_parameterBox_of_joint
        B L hLgap hLresolvent J Q a degree ha hdegree
        box.delta_le_gap box.lambda_bounds box.lambdaMax_lt_delta
        box.rMax_nonneg box.rMax_lt_margin eta heta
    filter_upwards [h] with b hb
    intro p hp
    exact hb p.center p.radius p.target
      hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2
  exact finiteDimensional_continuousObservable_tendsto_uniformOn
    (l := m) (s := {p | box.Contains p})
    (fun b p => continuousLinearMapCompression J Q
      (continuousLinearMapTaylorPartialSum
        (F (a b)) p.center p.target (degree b)))
    (fun p => continuousLinearMapCompression J Q
      (S.limitResolvent p.target))
    Phi hPhi R hR hlimit hoperator

section ClosedBoxConsequences

variable {l : Filter α} {gap : ℝ} {F : α → ℝ → E →L[ℝ] E}
variable (S : ContinuousLinearMapOpenTaylorStrongLimitData l gap F)
variable (B : ContinuousLinearMapOpenResolventNormBoundFamilyData gap F)
variable (L : ContinuousLinearMapOpenResolventNormBoundData E)
variable (hLgap : L.gap = gap) (hLresolvent : L.resolvent = S.limitResolvent)
variable (J : V →L[ℝ] E) (Q : E →L[ℝ] V)
variable {m : Filter β} (a : β → α) (degree : β → ℕ)
variable (ha : Tendsto a m l) (hdegree : Tendsto degree m atTop)
variable (box : ContinuousLinearMapClosedTaylorParameterBox gap)

/-- Closed-box determinant convergence is fully uniform. -/
theorem taylorPartialSum_det_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint :
    ∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ b in m, ∀ p, box.Contains p →
      |(continuousLinearMapCompression J Q
            (continuousLinearMapTaylorPartialSum
              (F (a b)) p.center p.target (degree b))).det -
        (continuousLinearMapCompression J Q
            (S.limitResolvent p.target)).det| < epsilon := by
  simpa [Real.norm_eq_abs] using
    S.taylorPartialSum_continuousObservable_finiteDimensionalCompression_tendsto_uniform_closedBox_of_joint
      B L hLgap hLresolvent J Q (fun A : V →L[ℝ] V => A.det)
      ContinuousLinearMap.continuous_det a degree ha hdegree box

end ClosedBoxConsequences

end ContinuousLinearMapOpenTaylorStrongLimitData

end MathlibAnalytic
end MGAP4D
