import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryEndpointConditionalVarianceGapBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory Finset Preorder Function
open scoped ProbabilityTheory BigOperators

noncomputable section

namespace FiniteConditionalVarianceGap

/-- For a scalar decomposition `gap = native - cross`, positivity of the retained
part is exactly strict separation of the cross term from the native energy. -/
theorem pos_iff_cross_lt_native
    (native cross gap : ℝ)
    (hGap : gap = native - cross) :
    0 < gap ↔ cross < native := by
  rw [hGap]
  constructor <;> intro h <;> linarith

/-- Vanishing of a scalar retained gap is exactly saturation of the native energy
by the cross term. -/
theorem eq_zero_iff_cross_eq_native
    (native cross gap : ℝ)
    (hGap : gap = native - cross) :
    gap = 0 ↔ cross = native := by
  rw [hGap]
  constructor <;> intro h <;> linarith

/-- With positive native energy, a correlation bound is equivalent to comparison
of its normalized ratio with the proposed factor. -/
theorem cross_le_factor_iff_ratio_le
    (native cross ρ : ℝ)
    (hNative : 0 < native) :
    cross ≤ ρ * native ↔ cross / native ≤ ρ := by
  exact (div_le_iff₀ hNative).symm

/-- The normalized cross/native ratio lies strictly below one exactly when the
retained gap is strictly positive. -/
theorem ratio_lt_one_iff_gap_pos
    (native cross gap : ℝ)
    (hGap : gap = native - cross)
    (hNative : 0 < native) :
    cross / native < 1 ↔ 0 < gap := by
  rw [div_lt_iff₀ hNative]
  simpa using (pos_iff_cross_lt_native native cross gap hGap).symm

/-- Exact retained-fraction formula for a positive native energy. -/
theorem gap_eq_one_sub_ratio_mul_native
    (native cross gap : ℝ)
    (hGap : gap = native - cross)
    (hNative : 0 < native) :
    gap = (1 - cross / native) * native := by
  rw [hGap]
  calc
    native - cross = native - (cross / native) * native := by
      rw [div_mul_cancel₀ cross (ne_of_gt hNative)]
    _ = (1 - cross / native) * native := by ring

/-- For positive native energy, existence of some strict correlation factor is
exactly positivity of the retained conditional-variance gap. -/
theorem pos_iff_exists_strict_factor
    (native cross gap : ℝ)
    (hGap : gap = native - cross)
    (hNative : 0 < native) :
    0 < gap ↔ ∃ ρ : ℝ, ρ < 1 ∧ cross ≤ ρ * native := by
  constructor
  · intro hPos
    have hCrossLt : cross < native :=
      (pos_iff_cross_lt_native native cross gap hGap).mp hPos
    refine ⟨cross / native, ?_, ?_⟩
    · rw [div_lt_iff₀ hNative]
      simpa using hCrossLt
    · apply (div_le_iff₀ hNative).mp
      exact le_rfl
  · rintro ⟨ρ, hρ, hCross⟩
    have hScaled : ρ * native < native := by
      simpa using (mul_lt_mul_of_pos_right hρ hNative)
    have hCrossLt : cross < native := lt_of_le_of_lt hCross hScaled
    exact (pos_iff_cross_lt_native native cross gap hGap).mpr hCrossLt

end FiniteConditionalVarianceGap

/-- Exact normalized endpoint correlation ratio.  Its useful order properties are
stated under positivity of the native one-link energy. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointCorrelationRatioBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) : ℝ :=
  C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF
      target O /
    C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O

/-- Positive endpoint conditional variance is exactly strict non-saturation of the
native one-link pair energy by the endpoint cross moment. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF_pos_iff_cross_lt_native
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    0 < C.independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF
        target O ↔
      C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF
          target O <
        C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O := by
  apply FiniteConditionalVarianceGap.pos_iff_cross_lt_native
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF_eq_native_sub_cross
      C target O

/-- Zero endpoint conditional variance is exactly saturation of the native energy
by the endpoint cross moment. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF_eq_zero_iff_cross_eq_native
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF
        target O = 0 ↔
      C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF
          target O =
        C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O := by
  apply FiniteConditionalVarianceGap.eq_zero_iff_cross_eq_native
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF_eq_native_sub_cross
      C target O

/-- Positive global endpoint conditional variance is equivalent to positive iid
double-trajectory endpoint energy. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF_pos_iff_double_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    0 < C.independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF
        target O ↔
      0 < C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF
        target O := by
  rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF_eq_half_double]
  constructor <;> intro h <;> nlinarith

/-- Vanishing global endpoint conditional variance is equivalent to vanishing iid
double-trajectory endpoint energy. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF_eq_zero_iff_double_eq_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF
        target O = 0 ↔
      C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableJointEnergyBCF
        target O = 0 := by
  rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF_eq_half_double]
  constructor <;> intro h <;> nlinarith

/-- On one fixed original Gibbs pair, positive conditional variance is equivalent
to positive iid double-trajectory endpoint energy. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF_pos_iff_double_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    0 < C.independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF
        target O z ↔
      0 < C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF
        target O z := by
  rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF_eq_half_double]
  constructor <;> intro h <;> nlinarith

/-- On one fixed original Gibbs pair, zero conditional variance is equivalent to
zero iid double-trajectory endpoint energy. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF_eq_zero_iff_double_eq_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (z : C.base.Configuration × C.base.Configuration) :
    C.independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF
        target O z = 0 ↔
      C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableFiberEnergyBCF
        target O z = 0 := by
  rw [continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointFiberConditionalVarianceGapBCF_eq_half_double]
  constructor <;> intro h <;> nlinarith

/-- For positive native energy, the endpoint correlation ratio exactly recovers the
cross moment after multiplication by that native energy. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCorrelationRatioBCF_mul_native_eq_cross
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hNative :
      0 < C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O) :
    C.independentPairHybridTargetTrajectoryEndpointCorrelationRatioBCF target O *
        C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O =
      C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF
        target O := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointCorrelationRatioBCF
  exact div_mul_cancel₀ _ (ne_of_gt hNative)

/-- The endpoint conditional-variance gap is exactly the retained fraction
`1 - correlationRatio` of the positive native energy. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF_eq_one_sub_correlationRatio_mul_native
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hNative :
      0 < C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O) :
    C.independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF
        target O =
      (1 - C.independentPairHybridTargetTrajectoryEndpointCorrelationRatioBCF
          target O) *
        C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointCorrelationRatioBCF
  apply FiniteConditionalVarianceGap.gap_eq_one_sub_ratio_mul_native
  · exact
      continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF_eq_native_sub_cross
        C target O
  · exact hNative

/-- The exact endpoint correlation ratio is strictly below one exactly when the
endpoint conditional variance is positive. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointCorrelationRatioBCF_lt_one_iff_gap_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hNative :
      0 < C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O) :
    C.independentPairHybridTargetTrajectoryEndpointCorrelationRatioBCF target O < 1 ↔
      0 < C.independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF
        target O := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointCorrelationRatioBCF
  apply FiniteConditionalVarianceGap.ratio_lt_one_iff_gap_pos
  · exact
      continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF_eq_native_sub_cross
        C target O
  · exact hNative

/-- For positive native energy, any proposed endpoint correlation factor is valid
exactly when it dominates the exact correlation ratio. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryCross_le_rho_native_iff_correlationRatio_le
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (ρ : ℝ)
    (hNative :
      0 < C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O) :
    C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF
        target O ≤
      ρ * C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O ↔
    C.independentPairHybridTargetTrajectoryEndpointCorrelationRatioBCF target O ≤ ρ := by
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryEndpointCorrelationRatioBCF
  exact FiniteConditionalVarianceGap.cross_le_factor_iff_ratio_le
    _ _ ρ hNative

/-- For positive native one-link energy, a strict endpoint correlation factor exists
if and only if the endpoint conditional variance is positive. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF_pos_iff_exists_strict_correlation_factor
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hNative :
      0 < C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O) :
    0 < C.independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF
        target O ↔
      ∃ ρ : ℝ, ρ < 1 ∧
        C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF
            target O ≤
          ρ * C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O := by
  apply FiniteConditionalVarianceGap.pos_iff_exists_strict_factor
  · exact
      continuous_compact_oriented_independentPairHybridTargetTrajectoryEndpointConditionalVarianceGapBCF_eq_native_sub_cross
        C target O
  · exact hNative

/-- Exact normalized ratio of total endpoint cross moment to total native pair
energy.  Its useful order properties require positive total native energy. -/
def ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryTotalEndpointCorrelationRatioBCF
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) : ℝ :=
  (∑ target : C.base.geometry.Edge,
      C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF
        target O) /
    ∑ target : C.base.geometry.Edge,
      C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O

/-- For positive total native energy, the total endpoint correlation ratio exactly
recovers the summed cross moment. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryTotalEndpointCorrelationRatioBCF_mul_sum_native_eq_sum_cross
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hNative :
      0 < ∑ target : C.base.geometry.Edge,
        C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O) :
    C.independentPairHybridTargetTrajectoryTotalEndpointCorrelationRatioBCF O *
        (∑ target : C.base.geometry.Edge,
          C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O) =
      ∑ target : C.base.geometry.Edge,
        C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF
          target O := by
  classical
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryTotalEndpointCorrelationRatioBCF
  exact div_mul_cancel₀ _ (ne_of_gt hNative)

/-- The total conditional-variance gap is exactly the retained fraction of the
positive summed native energy. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryTotalEndpointConditionalVarianceGapBCF_eq_one_sub_correlationRatio_mul_sum_native
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hNative :
      0 < ∑ target : C.base.geometry.Edge,
        C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O) :
    C.independentPairHybridTargetTrajectoryTotalEndpointConditionalVarianceGapBCF O =
      (1 - C.independentPairHybridTargetTrajectoryTotalEndpointCorrelationRatioBCF O) *
        ∑ target : C.base.geometry.Edge,
          C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O := by
  classical
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryTotalEndpointCorrelationRatioBCF
  apply FiniteConditionalVarianceGap.gap_eq_one_sub_ratio_mul_native
  · exact
      continuous_compact_oriented_independentPairHybridTargetTrajectoryTotalEndpointConditionalVarianceGapBCF_eq_sum_native_sub_sum_cross
        C O
  · exact hNative

/-- The exact total endpoint correlation ratio is below one exactly when the total
conditional-variance gap is positive. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryTotalEndpointCorrelationRatioBCF_lt_one_iff_total_gap_pos
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hNative :
      0 < ∑ target : C.base.geometry.Edge,
        C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O) :
    C.independentPairHybridTargetTrajectoryTotalEndpointCorrelationRatioBCF O < 1 ↔
      0 < C.independentPairHybridTargetTrajectoryTotalEndpointConditionalVarianceGapBCF O := by
  classical
  unfold
    ContinuousCompactOrientedGaugeWilsonSystem.independentPairHybridTargetTrajectoryTotalEndpointCorrelationRatioBCF
  apply FiniteConditionalVarianceGap.ratio_lt_one_iff_gap_pos
  · exact
      continuous_compact_oriented_independentPairHybridTargetTrajectoryTotalEndpointConditionalVarianceGapBCF_eq_sum_native_sub_sum_cross
        C O
  · exact hNative

/-- Positive total conditional variance is equivalent to existence of some strict
correlation factor for the summed endpoint cross moment. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryTotalEndpointConditionalVarianceGapBCF_pos_iff_exists_strict_correlation_factor
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ)
    (hNative :
      0 < ∑ target : C.base.geometry.Edge,
        C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O) :
    0 < C.independentPairHybridTargetTrajectoryTotalEndpointConditionalVarianceGapBCF O ↔
      ∃ ρ : ℝ, ρ < 1 ∧
        (∑ target : C.base.geometry.Edge,
          C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF
            target O) ≤
          ρ * ∑ target : C.base.geometry.Edge,
            C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O := by
  classical
  apply FiniteConditionalVarianceGap.pos_iff_exists_strict_factor
  · exact
      continuous_compact_oriented_independentPairHybridTargetTrajectoryTotalEndpointConditionalVarianceGapBCF_eq_sum_native_sub_sum_cross
        C O
  · exact hNative

/-- Vanishing total conditional variance is exactly saturation of the summed native
energy by the summed endpoint cross moment. -/
theorem continuous_compact_oriented_independentPairHybridTargetTrajectoryTotalEndpointConditionalVarianceGapBCF_eq_zero_iff_sum_cross_eq_sum_native
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (O : BoundedContinuousFunction C.base.Configuration ℝ) :
    C.independentPairHybridTargetTrajectoryTotalEndpointConditionalVarianceGapBCF O = 0 ↔
      (∑ target : C.base.geometry.Edge,
        C.independentPairHybridTargetTrajectoryDoubleEndpointPairObservableCrossMomentBCF
          target O) =
        ∑ target : C.base.geometry.Edge,
          C.singleLinkHeatBathIndependentPairObservableEnergyBCF target O := by
  classical
  apply FiniteConditionalVarianceGap.eq_zero_iff_cross_eq_native
  exact
    continuous_compact_oriented_independentPairHybridTargetTrajectoryTotalEndpointConditionalVarianceGapBCF_eq_sum_native_sub_sum_cross
      C O

end

end MathlibAnalytic
end MGAP4D
