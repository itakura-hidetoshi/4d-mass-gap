import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroCoordinateProjectionCommutationL2
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicHamiltonianKernelIntersectionBCF
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set

noncomputable section

set_option maxRecDepth 8192

/-- Ordered composition of a finite list of exact one-link heat-bath projections.
The head projection is applied first and the remaining projections are then
applied recursively. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.periodicCoordinateProjectionListL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    List C.base.geometry.Edge →
      Lp ℝ 2 C.gibbsMeasure →L[ℝ] Lp ℝ 2 C.gibbsMeasure
  | [] => ContinuousLinearMap.id ℝ (Lp ℝ 2 C.gibbsMeasure)
  | target :: targets =>
      (C.periodicCoordinateProjectionListL2 targets).comp
        (C.singleLinkHeatBathProjectionL2 target)

@[simp]
theorem continuous_compact_oriented_periodicCoordinateProjectionListL2_nil_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    C.periodicCoordinateProjectionListL2 [] f = f := by
  rfl

@[simp]
theorem continuous_compact_oriented_periodicCoordinateProjectionListL2_cons_apply
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (targets : List C.base.geometry.Edge)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    C.periodicCoordinateProjectionListL2 (target :: targets) f =
      C.periodicCoordinateProjectionListL2 targets
        (C.singleLinkHeatBathProjectionL2 target f) := by
  rfl

/-- At zero Wilson coupling, any one-link projection commutes through an ordered
finite list of one-link projections. -/
theorem continuous_compact_oriented_periodicCoordinateProjectionListL2_commute_of_beta_eq_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hBeta : C.base.beta = 0)
    (target : C.base.geometry.Edge)
    (targets : List C.base.geometry.Edge)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    C.singleLinkHeatBathProjectionL2 target
        (C.periodicCoordinateProjectionListL2 targets f) =
      C.periodicCoordinateProjectionListL2 targets
        (C.singleLinkHeatBathProjectionL2 target f) := by
  induction targets generalizing f with
  | nil => rfl
  | cons source rest ih =>
      calc
        C.singleLinkHeatBathProjectionL2 target
            (C.periodicCoordinateProjectionListL2 (source :: rest) f) =
          C.singleLinkHeatBathProjectionL2 target
            (C.periodicCoordinateProjectionListL2 rest
              (C.singleLinkHeatBathProjectionL2 source f)) := by
            rfl
        _ = C.periodicCoordinateProjectionListL2 rest
              (C.singleLinkHeatBathProjectionL2 target
                (C.singleLinkHeatBathProjectionL2 source f)) :=
          ih (C.singleLinkHeatBathProjectionL2 source f)
        _ = C.periodicCoordinateProjectionListL2 rest
              (C.singleLinkHeatBathProjectionL2 source
                (C.singleLinkHeatBathProjectionL2 target f)) := by
          rw [continuous_compact_oriented_singleLinkHeatBathProjectionL2_pairwise_comm_of_beta_eq_zero
            C hBeta target source f]
        _ = C.periodicCoordinateProjectionListL2 (source :: rest)
              (C.singleLinkHeatBathProjectionL2 target f) := by
          rfl

/-- If a target occurs in the list, the zero-coupling list product is fixed by
that target projection. -/
theorem continuous_compact_oriented_periodicCoordinateProjectionListL2_fixed_of_mem_of_beta_eq_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hBeta : C.base.beta = 0)
    (target : C.base.geometry.Edge)
    (targets : List C.base.geometry.Edge)
    (hTarget : target ∈ targets)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    C.singleLinkHeatBathProjectionL2 target
        (C.periodicCoordinateProjectionListL2 targets f) =
      C.periodicCoordinateProjectionListL2 targets f := by
  induction targets generalizing f with
  | nil => simp at hTarget
  | cons source rest ih =>
      simp only [List.mem_cons] at hTarget
      rcases hTarget with rfl | hTarget
      · calc
          C.singleLinkHeatBathProjectionL2 source
              (C.periodicCoordinateProjectionListL2 (source :: rest) f) =
            C.singleLinkHeatBathProjectionL2 source
              (C.periodicCoordinateProjectionListL2 rest
                (C.singleLinkHeatBathProjectionL2 source f)) := by
              rfl
          _ = C.periodicCoordinateProjectionListL2 rest
                (C.singleLinkHeatBathProjectionL2 source
                  (C.singleLinkHeatBathProjectionL2 source f)) :=
            continuous_compact_oriented_periodicCoordinateProjectionListL2_commute_of_beta_eq_zero
              C hBeta source rest
                (C.singleLinkHeatBathProjectionL2 source f)
          _ = C.periodicCoordinateProjectionListL2 rest
                (C.singleLinkHeatBathProjectionL2 source f) := by
            rw [continuous_compact_oriented_singleLinkHeatBathProjectionL2_apply_projection]
          _ = C.periodicCoordinateProjectionListL2 (source :: rest) f := by
            rfl
      · exact ih hTarget (C.singleLinkHeatBathProjectionL2 source f)

/-- A list product fixes a vector already fixed by every projection appearing in
that list. -/
theorem continuous_compact_oriented_periodicCoordinateProjectionListL2_apply_eq_self_of_forall_mem_fixed
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (targets : List C.base.geometry.Edge)
    (f : Lp ℝ 2 C.gibbsMeasure)
    (hFixed : ∀ target ∈ targets,
      C.singleLinkHeatBathProjectionL2 target f = f) :
    C.periodicCoordinateProjectionListL2 targets f = f := by
  induction targets with
  | nil => rfl
  | cons source rest ih =>
      rw [continuous_compact_oriented_periodicCoordinateProjectionListL2_cons_apply,
        hFixed source (by simp)]
      apply ih
      intro target hTarget
      exact hFixed target (by simp [hTarget])

/-- Canonical finite enumeration of every physical positive-link edge. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.periodicPhysicalEdgeEnumeration
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    List C.base.geometry.Edge :=
  List.ofFn fun i : Fin (Fintype.card C.base.geometry.Edge) =>
    (Fintype.equivFin C.base.geometry.Edge).symm i

/-- Every physical edge occurs in the canonical finite enumeration. -/
theorem continuous_compact_oriented_periodicPhysicalEdgeEnumeration_mem
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge) :
    target ∈ C.periodicPhysicalEdgeEnumeration := by
  classical
  simp [ContinuousCompactOrientedGaugeWilsonSystem.periodicPhysicalEdgeEnumeration]

/-- Ordered product of all exact one-link heat-bath projections. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.periodicFullCoordinateProjectionL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    Lp ℝ 2 C.gibbsMeasure →L[ℝ] Lp ℝ 2 C.gibbsMeasure :=
  C.periodicCoordinateProjectionListL2 C.periodicPhysicalEdgeEnumeration

/-- At zero coupling, the output of the full coordinate-projection product is
fixed by every physical-link heat-bath projection. -/
theorem continuous_compact_oriented_periodicFullCoordinateProjectionL2_commonFixed_of_beta_eq_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hBeta : C.base.beta = 0)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    C.periodicLocalHeatBathCommonFixedL2
      (C.periodicFullCoordinateProjectionL2 f) := by
  intro target
  exact
    continuous_compact_oriented_periodicCoordinateProjectionListL2_fixed_of_mem_of_beta_eq_zero
      C hBeta target C.periodicPhysicalEdgeEnumeration
      (continuous_compact_oriented_periodicPhysicalEdgeEnumeration_mem C target) f

/-- The full coordinate-projection product fixes every common fixed vector. -/
theorem continuous_compact_oriented_periodicFullCoordinateProjectionL2_apply_eq_self_of_commonFixed
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : Lp ℝ 2 C.gibbsMeasure)
    (hFixed : C.periodicLocalHeatBathCommonFixedL2 f) :
    C.periodicFullCoordinateProjectionL2 f = f := by
  unfold ContinuousCompactOrientedGaugeWilsonSystem.periodicFullCoordinateProjectionL2
  apply
    continuous_compact_oriented_periodicCoordinateProjectionListL2_apply_eq_self_of_forall_mem_fixed
  intro target _hTarget
  exact hFixed target

/-- At zero coupling, fixedness under the full finite product is exactly common
fixedness under every one-link projection. -/
theorem continuous_compact_oriented_periodicFullCoordinateProjectionL2_apply_eq_self_iff_commonFixed_of_beta_eq_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hBeta : C.base.beta = 0)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    C.periodicFullCoordinateProjectionL2 f = f ↔
      C.periodicLocalHeatBathCommonFixedL2 f := by
  constructor
  · intro hProduct
    have hOutput :=
      continuous_compact_oriented_periodicFullCoordinateProjectionL2_commonFixed_of_beta_eq_zero
        C hBeta f
    intro target
    have hTarget := hOutput target
    rwa [hProduct] at hTarget
  · intro hFixed
    exact
      continuous_compact_oriented_periodicFullCoordinateProjectionL2_apply_eq_self_of_commonFixed
        C f hFixed

/-- At zero coupling, the full finite product is idempotent.  Its range is the
common fixed space. -/
theorem continuous_compact_oriented_periodicFullCoordinateProjectionL2_idempotent_of_beta_eq_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hBeta : C.base.beta = 0) :
    C.periodicFullCoordinateProjectionL2.comp
        C.periodicFullCoordinateProjectionL2 =
      C.periodicFullCoordinateProjectionL2 := by
  apply ContinuousLinearMap.ext
  intro f
  rw [ContinuousLinearMap.comp_apply]
  exact
    continuous_compact_oriented_periodicFullCoordinateProjectionL2_apply_eq_self_of_commonFixed
      C (C.periodicFullCoordinateProjectionL2 f)
      (continuous_compact_oriented_periodicFullCoordinateProjectionL2_commonFixed_of_beta_eq_zero
        C hBeta f)

/-- At zero coupling, membership in the native heat-bath Hamiltonian kernel is
exactly fixedness under the full finite coordinate-projection product. -/
theorem continuous_compact_oriented_periodicKernelIntersection_hamiltonian_eq_zero_iff_fullCoordinateProjection_fixed_of_beta_eq_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hBeta : C.base.beta = 0)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    C.heatBathHamiltonianL2 f = 0 ↔
      C.periodicFullCoordinateProjectionL2 f = f := by
  exact
    (continuous_compact_oriented_periodicKernelIntersection_hamiltonian_eq_zero_iff_commonFixed
      C f).trans
      (continuous_compact_oriented_periodicFullCoordinateProjectionL2_apply_eq_self_iff_commonFixed_of_beta_eq_zero
        C hBeta f).symm

/-- The actual side-three periodic `SU(2)` full coordinate product always lands
in the exact common fixed space. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_fullCoordinateProjectionL2_commonFixed
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicLocalHeatBathCommonFixedL2
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicFullCoordinateProjectionL2 f) := by
  exact
    continuous_compact_oriented_periodicFullCoordinateProjectionL2_commonFixed_of_beta_eq_zero
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero f

/-- The actual full coordinate product is idempotent. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_fullCoordinateProjectionL2_idempotent :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicFullCoordinateProjectionL2.comp
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicFullCoordinateProjectionL2 =
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicFullCoordinateProjectionL2 := by
  exact
    continuous_compact_oriented_periodicFullCoordinateProjectionL2_idempotent_of_beta_eq_zero
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero

/-- For the actual side-three periodic `SU(2)` endpoint system, Hamiltonian zero
is exactly fixedness under one complete finite sweep of all `324` commuting
coordinate projections. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_hamiltonian_eq_zero_iff_fullCoordinateProjection_fixed
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2 f = 0 ↔
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicFullCoordinateProjectionL2 f = f := by
  exact
    continuous_compact_oriented_periodicKernelIntersection_hamiltonian_eq_zero_iff_fullCoordinateProjection_fixed_of_beta_eq_zero
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero f

/-- Compact receipt for the beta-zero full coordinate-projection product layer.
This identifies its range with the exact Hamiltonian kernel, but does not yet
identify that range with the Gibbs-vacuum line and does not assert variance
tensorization or the `323/324` random-scan bound. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCoordinateProjectionProductL2Receipt :
    Prop :=
  (∀ f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicLocalHeatBathCommonFixedL2
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicFullCoordinateProjectionL2 f)) ∧
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicFullCoordinateProjectionL2.comp
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicFullCoordinateProjectionL2 =
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicFullCoordinateProjectionL2 ∧
  (∀ f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2 f = 0 ↔
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicFullCoordinateProjectionL2 f = f)

/-- The actual beta-zero full coordinate-projection product receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCoordinateProjectionProductL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCoordinateProjectionProductL2Receipt := by
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_fullCoordinateProjectionL2_commonFixed,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_fullCoordinateProjectionL2_idempotent,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_hamiltonian_eq_zero_iff_fullCoordinateProjection_fixed⟩

end

end MathlibAnalytic
end MGAP4D