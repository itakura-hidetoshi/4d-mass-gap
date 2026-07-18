import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroFullCoordinateVacuumProjectionL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators

noncomputable section

set_option maxRecDepth 8192

/-- The defect of an orthogonal one-link conditional-expectation projection is
orthogonal to every vector fixed by that projection. -/
theorem continuous_compact_oriented_singleLinkHeatBathProjectionL2_defect_inner_eq_zero_of_fixed
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (f g : Lp ℝ 2 C.gibbsMeasure)
    (hFixed : C.singleLinkHeatBathProjectionL2 target g = g) :
    inner ℝ (f - C.singleLinkHeatBathProjectionL2 target f) g = 0 := by
  rw [inner_sub_left,
    continuous_compact_oriented_singleLinkHeatBathProjectionL2_inner_symm,
    hFixed, sub_self]

/-- At zero coupling, the tail defect after first projecting in `target` is
itself fixed by the `target` projection. -/
theorem continuous_compact_oriented_periodicCoordinateProjectionListL2_tailDefect_fixed_of_beta_eq_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hBeta : C.base.beta = 0)
    (target : C.base.geometry.Edge)
    (targets : List C.base.geometry.Edge)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    C.singleLinkHeatBathProjectionL2 target
        (C.singleLinkHeatBathProjectionL2 target f -
          C.periodicCoordinateProjectionListL2 targets
            (C.singleLinkHeatBathProjectionL2 target f)) =
      C.singleLinkHeatBathProjectionL2 target f -
        C.periodicCoordinateProjectionListL2 targets
          (C.singleLinkHeatBathProjectionL2 target f) := by
  rw [map_sub,
    continuous_compact_oriented_singleLinkHeatBathProjectionL2_apply_projection,
    continuous_compact_oriented_periodicCoordinateProjectionListL2_commute_of_beta_eq_zero
      C hBeta target targets
        (C.singleLinkHeatBathProjectionL2 target f),
    continuous_compact_oriented_singleLinkHeatBathProjectionL2_apply_projection]

/-- One step of a commuting orthogonal-projection sweep satisfies an exact
Pythagorean decomposition of the total defect. -/
theorem continuous_compact_oriented_periodicCoordinateProjectionListL2_cons_defect_norm_sq_eq_of_beta_eq_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hBeta : C.base.beta = 0)
    (target : C.base.geometry.Edge)
    (targets : List C.base.geometry.Edge)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    ‖f - C.periodicCoordinateProjectionListL2 (target :: targets) f‖ ^ 2 =
      ‖f - C.singleLinkHeatBathProjectionL2 target f‖ ^ 2 +
        ‖C.singleLinkHeatBathProjectionL2 target f -
          C.periodicCoordinateProjectionListL2 targets
            (C.singleLinkHeatBathProjectionL2 target f)‖ ^ 2 := by
  rw [continuous_compact_oriented_periodicCoordinateProjectionListL2_cons_apply]
  have hSplit :
      f - C.periodicCoordinateProjectionListL2 targets
          (C.singleLinkHeatBathProjectionL2 target f) =
        (f - C.singleLinkHeatBathProjectionL2 target f) +
          (C.singleLinkHeatBathProjectionL2 target f -
            C.periodicCoordinateProjectionListL2 targets
              (C.singleLinkHeatBathProjectionL2 target f)) := by
    abel
  have hFixed :=
    continuous_compact_oriented_periodicCoordinateProjectionListL2_tailDefect_fixed_of_beta_eq_zero
      C hBeta target targets f
  have hOrth :
      inner ℝ
          (f - C.singleLinkHeatBathProjectionL2 target f)
          (C.singleLinkHeatBathProjectionL2 target f -
            C.periodicCoordinateProjectionListL2 targets
              (C.singleLinkHeatBathProjectionL2 target f)) = 0 :=
    continuous_compact_oriented_singleLinkHeatBathProjectionL2_defect_inner_eq_zero_of_fixed
      C target f
      (C.singleLinkHeatBathProjectionL2 target f -
        C.periodicCoordinateProjectionListL2 targets
          (C.singleLinkHeatBathProjectionL2 target f)) hFixed
  rw [hSplit, norm_add_sq_real, hOrth]
  ring

/-- Projecting a local coordinate defect through another zero-coupling
coordinate projection cannot increase its `L²` norm. -/
theorem continuous_compact_oriented_singleLinkHeatBathProjectionL2_projectedDefect_norm_le_of_beta_eq_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hBeta : C.base.beta = 0)
    (target source : C.base.geometry.Edge)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    ‖C.singleLinkHeatBathProjectionL2 target f -
        C.singleLinkHeatBathProjectionL2 source
          (C.singleLinkHeatBathProjectionL2 target f)‖ ≤
      ‖f - C.singleLinkHeatBathProjectionL2 source f‖ := by
  calc
    ‖C.singleLinkHeatBathProjectionL2 target f -
        C.singleLinkHeatBathProjectionL2 source
          (C.singleLinkHeatBathProjectionL2 target f)‖ =
      ‖C.singleLinkHeatBathProjectionL2 target
        (f - C.singleLinkHeatBathProjectionL2 source f)‖ := by
          rw [map_sub,
            continuous_compact_oriented_singleLinkHeatBathProjectionL2_pairwise_comm_of_beta_eq_zero
              C hBeta target source f]
    _ ≤ ‖f - C.singleLinkHeatBathProjectionL2 source f‖ :=
      continuous_compact_oriented_singleLinkHeatBathProjectionL2_norm_le
        C target (f - C.singleLinkHeatBathProjectionL2 source f)

/-- Squared-norm form of contraction of a projected coordinate defect. -/
theorem continuous_compact_oriented_singleLinkHeatBathProjectionL2_projectedDefect_norm_sq_le_of_beta_eq_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hBeta : C.base.beta = 0)
    (target source : C.base.geometry.Edge)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    ‖C.singleLinkHeatBathProjectionL2 target f -
        C.singleLinkHeatBathProjectionL2 source
          (C.singleLinkHeatBathProjectionL2 target f)‖ ^ 2 ≤
      ‖f - C.singleLinkHeatBathProjectionL2 source f‖ ^ 2 := by
  have hNorm :=
    continuous_compact_oriented_singleLinkHeatBathProjectionL2_projectedDefect_norm_le_of_beta_eq_zero
      C hBeta target source f
  nlinarith [
    norm_nonneg
      (C.singleLinkHeatBathProjectionL2 target f -
        C.singleLinkHeatBathProjectionL2 source
          (C.singleLinkHeatBathProjectionL2 target f)),
    norm_nonneg (f - C.singleLinkHeatBathProjectionL2 source f)]

/-- The sum of all remaining coordinate defects cannot increase after applying
one commuting zero-coupling coordinate projection. -/
theorem continuous_compact_oriented_periodicCoordinateProjectionListL2_projectedDefectSum_le_of_beta_eq_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hBeta : C.base.beta = 0)
    (target : C.base.geometry.Edge)
    (targets : List C.base.geometry.Edge)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    (targets.map fun source =>
      ‖C.singleLinkHeatBathProjectionL2 target f -
        C.singleLinkHeatBathProjectionL2 source
          (C.singleLinkHeatBathProjectionL2 target f)‖ ^ 2).sum ≤
      (targets.map fun source =>
        ‖f - C.singleLinkHeatBathProjectionL2 source f‖ ^ 2).sum := by
  induction targets with
  | nil => simp
  | cons source rest ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add
        (continuous_compact_oriented_singleLinkHeatBathProjectionL2_projectedDefect_norm_sq_le_of_beta_eq_zero
          C hBeta target source f) ih

/-- Exact finite tensorization inequality for an ordered list of pairwise
commuting zero-coupling one-link orthogonal projections. -/
theorem continuous_compact_oriented_periodicCoordinateProjectionListL2_tensorization_of_beta_eq_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hBeta : C.base.beta = 0)
    (targets : List C.base.geometry.Edge)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    ‖f - C.periodicCoordinateProjectionListL2 targets f‖ ^ 2 ≤
      (targets.map fun target =>
        ‖f - C.singleLinkHeatBathProjectionL2 target f‖ ^ 2).sum := by
  induction targets generalizing f with
  | nil => simp
  | cons target rest ih =>
      rw [continuous_compact_oriented_periodicCoordinateProjectionListL2_cons_defect_norm_sq_eq_of_beta_eq_zero
        C hBeta target rest f]
      simp only [List.map_cons, List.sum_cons]
      exact add_le_add_left
        ((ih (C.singleLinkHeatBathProjectionL2 target f)).trans
          (continuous_compact_oriented_periodicCoordinateProjectionListL2_projectedDefectSum_le_of_beta_eq_zero
            C hBeta target rest f)) _

/-- The canonical physical-edge enumeration sums every edge exactly once. -/
theorem continuous_compact_oriented_periodicPhysicalEdgeEnumeration_map_sum
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (φ : C.base.geometry.Edge → ℝ) :
    (C.periodicPhysicalEdgeEnumeration.map φ).sum =
      ∑ target : C.base.geometry.Edge, φ target := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.periodicPhysicalEdgeEnumeration
  rw [List.map_ofFn, List.sum_ofFn]
  exact Fintype.sum_equiv
    (Fintype.equivFin C.base.geometry.Edge).symm
    (fun i => φ ((Fintype.equivFin C.base.geometry.Edge).symm i))
    φ (fun _ => rfl)

/-- At zero coupling, the defect from the complete finite coordinate sweep is
bounded by the sum of the original one-link projection defects. -/
theorem continuous_compact_oriented_periodicFullCoordinateProjectionL2_tensorization_of_beta_eq_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hBeta : C.base.beta = 0)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    ‖f - C.periodicFullCoordinateProjectionL2 f‖ ^ 2 ≤
      ∑ target : C.base.geometry.Edge,
        ‖f - C.singleLinkHeatBathProjectionL2 target f‖ ^ 2 := by
  calc
    ‖f - C.periodicFullCoordinateProjectionL2 f‖ ^ 2 ≤
        (C.periodicPhysicalEdgeEnumeration.map fun target =>
          ‖f - C.singleLinkHeatBathProjectionL2 target f‖ ^ 2).sum := by
      simpa [ContinuousCompactOrientedGaugeWilsonSystem.periodicFullCoordinateProjectionL2] using
        (continuous_compact_oriented_periodicCoordinateProjectionListL2_tensorization_of_beta_eq_zero
          C hBeta C.periodicPhysicalEdgeEnumeration f)
    _ = ∑ target : C.base.geometry.Edge,
        ‖f - C.singleLinkHeatBathProjectionL2 target f‖ ^ 2 :=
      continuous_compact_oriented_periodicPhysicalEdgeEnumeration_map_sum C _

/-- Fluctuation-projection form of beta-zero finite tensorization. -/
theorem continuous_compact_oriented_periodicFullCoordinateProjectionL2_tensorization_fluctuation_of_beta_eq_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hBeta : C.base.beta = 0)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    ‖f - C.periodicFullCoordinateProjectionL2 f‖ ^ 2 ≤
      ∑ target : C.base.geometry.Edge,
        ‖C.singleLinkHeatBathFluctuationL2 target f‖ ^ 2 := by
  simpa only [continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply] using
    continuous_compact_oriented_periodicFullCoordinateProjectionL2_tensorization_of_beta_eq_zero
      C hBeta f

/-- Finite-volume beta-zero heat-bath Poincare inequality with constant `1`,
written as distance to the normalized Gibbs-vacuum line. -/
theorem continuous_compact_oriented_heatBathPoincare_one_of_beta_eq_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hBeta : C.base.beta = 0)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    ‖f - inner ℝ C.gibbsVacuumL2 f • C.gibbsVacuumL2‖ ^ 2 ≤
      inner ℝ (C.heatBathHamiltonianL2 f) f := by
  rw [← continuous_compact_oriented_periodicFullCoordinateProjectionL2_eq_vacuumProjection_of_beta_eq_zero
      C hBeta f,
    continuous_compact_oriented_heatBathHamiltonianL2_quadraticForm]
  exact
    continuous_compact_oriented_periodicFullCoordinateProjectionL2_tensorization_fluctuation_of_beta_eq_zero
      C hBeta f

/-- Centered-vector form of the finite-volume beta-zero heat-bath Poincare
inequality with constant `1`. -/
theorem continuous_compact_oriented_heatBathPoincare_one_centered_of_beta_eq_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hBeta : C.base.beta = 0)
    (f : Lp ℝ 2 C.gibbsMeasure)
    (hCentered : inner ℝ C.gibbsVacuumL2 f = 0) :
    ‖f‖ ^ 2 ≤ inner ℝ (C.heatBathHamiltonianL2 f) f := by
  simpa [hCentered] using
    continuous_compact_oriented_heatBathPoincare_one_of_beta_eq_zero
      C hBeta f

/-- The actual side-three periodic `SU(2)` full coordinate product satisfies
exact finite tensorization. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_fullCoordinateProjectionL2_tensorization
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    ‖f -
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicFullCoordinateProjectionL2 f‖ ^ 2 ≤
      ∑ target :
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge,
        ‖periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
          target f‖ ^ 2 := by
  exact
    continuous_compact_oriented_periodicFullCoordinateProjectionL2_tensorization_fluctuation_of_beta_eq_zero
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero f

/-- The actual side-three periodic `SU(2)` beta-zero endpoint system satisfies
the heat-bath Poincare inequality with constant `1`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_heatBathPoincare_one
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    ‖f - inner ℝ
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2 f •
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2‖ ^ 2 ≤
      inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2 f) f := by
  exact
    continuous_compact_oriented_heatBathPoincare_one_of_beta_eq_zero
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero f

/-- Centered-vector form of the actual beta-zero heat-bath Poincare inequality
with constant `1`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_heatBathPoincare_one_centered
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (hCentered : inner ℝ
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2 f = 0) :
    ‖f‖ ^ 2 ≤ inner ℝ
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2 f) f := by
  exact
    continuous_compact_oriented_heatBathPoincare_one_centered_of_beta_eq_zero
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero f hCentered

/-- Compact receipt for exact beta-zero tensorization and the resulting
finite-volume heat-bath Poincare constant `1`. This does not assert a
random-scan `323/324` rate, a positive variational lower edge, volume
uniformity, nonzero-beta control, a continuum limit, or a Yang--Mills mass gap. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCoordinateProjectionTensorizationL2Receipt :
    Prop :=
  (∀ f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
    ‖f -
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicFullCoordinateProjectionL2 f‖ ^ 2 ≤
      ∑ target :
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge,
        ‖periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
          target f‖ ^ 2) ∧
  (∀ f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
    ‖f - inner ℝ
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2 f •
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2‖ ^ 2 ≤
      inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2 f) f)

/-- The actual beta-zero coordinate tensorization and Poincare receipt is
proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCoordinateProjectionTensorizationL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCoordinateProjectionTensorizationL2Receipt := by
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_fullCoordinateProjectionL2_tensorization,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_heatBathPoincare_one⟩

end

end MathlibAnalytic
end MGAP4D
