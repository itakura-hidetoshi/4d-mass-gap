import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicHamiltonianKernelIntersectionBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators

noncomputable section

set_option maxRecDepth 8192

/-- The closed Gibbs `L²` subspace consisting of vectors measurable with
respect to every physical-link off-link sigma-algebra. -/
noncomputable def
    ContinuousCompactOrientedGaugeWilsonSystem.periodicAllOffLinkMeasurableL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    Submodule ℝ (Lp ℝ 2 C.gibbsMeasure) :=
  ⨅ target : C.base.geometry.Edge,
    lpMeas ℝ ℝ (C.base.offLinkMeasurableSpace target) 2 C.gibbsMeasure

/-- A nonzero vacuum-orthogonal vector belonging to every off-link measurable
`L²` subspace. -/
def ContinuousCompactOrientedGaugeWilsonSystem.periodicVacuumOrthogonalNonzeroAllOffLinkMeasurableL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem) : Prop :=
  ∃ f : Lp ℝ 2 C.gibbsMeasure,
    f ∈ C.VacuumOrthogonalL2 ∧
      f ≠ 0 ∧
        f ∈ C.periodicAllOffLinkMeasurableL2

/-- A one-link heat-bath conditional expectation fixes exactly the vectors in
the corresponding off-link measurable `L²` subspace. -/
theorem continuous_compact_oriented_periodicOffLinkIntersection_projection_eq_self_iff_mem_lpMeas
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    C.singleLinkHeatBathProjectionL2 target f = f ↔
      f ∈ lpMeas ℝ ℝ (C.base.offLinkMeasurableSpace target)
        2 C.gibbsMeasure := by
  let hm := compact_oriented_offLinkMeasurableSpace_le C.base target
  constructor
  · intro hFixed
    let q : lpMeas ℝ ℝ (C.base.offLinkMeasurableSpace target)
        2 C.gibbsMeasure :=
      condExpL2 ℝ ℝ hm f
    have hCoe : (q : Lp ℝ 2 C.gibbsMeasure) = f := by
      simpa [q, hm,
        continuous_compact_oriented_singleLinkHeatBathProjectionL2_apply] using
        hFixed
    have hMem :
        (q : Lp ℝ 2 C.gibbsMeasure) ∈
          lpMeas ℝ ℝ (C.base.offLinkMeasurableSpace target)
            2 C.gibbsMeasure :=
      q.property
    rw [hCoe] at hMem
    exact hMem
  · intro hMem
    let q : lpMeas ℝ ℝ (C.base.offLinkMeasurableSpace target)
        2 C.gibbsMeasure :=
      ⟨f, hMem⟩
    have hq :
        (condExpL2 ℝ ℝ hm (q : Lp ℝ 2 C.gibbsMeasure) :
          lpMeas ℝ ℝ (C.base.offLinkMeasurableSpace target)
            2 C.gibbsMeasure) = q := by
      unfold condExpL2
      exact Submodule.orthogonalProjection_mem_subspace_eq_self q
    have hCoe := congrArg
      (fun x : lpMeas ℝ ℝ (C.base.offLinkMeasurableSpace target)
          2 C.gibbsMeasure =>
        (x : Lp ℝ 2 C.gibbsMeasure)) hq
    rw [continuous_compact_oriented_singleLinkHeatBathProjectionL2_apply]
    simpa [q, hm] using hCoe

/-- Membership in the all-off-link subspace is pointwise membership in every
single-link off-link measurable subspace. -/
theorem continuous_compact_oriented_periodicOffLinkIntersection_mem_iff
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    f ∈ C.periodicAllOffLinkMeasurableL2 ↔
      ∀ target : C.base.geometry.Edge,
        f ∈ lpMeas ℝ ℝ (C.base.offLinkMeasurableSpace target)
          2 C.gibbsMeasure := by
  simp [ContinuousCompactOrientedGaugeWilsonSystem.periodicAllOffLinkMeasurableL2]

/-- The common heat-bath fixed-space predicate is exactly membership in the
intersection of all off-link measurable `L²` subspaces. -/
theorem continuous_compact_oriented_periodicOffLinkIntersection_commonFixed_iff_mem
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    C.periodicLocalHeatBathCommonFixedL2 f ↔
      f ∈ C.periodicAllOffLinkMeasurableL2 := by
  constructor
  · intro hFixed
    apply
      (continuous_compact_oriented_periodicOffLinkIntersection_mem_iff C f).2
    intro target
    exact
      (continuous_compact_oriented_periodicOffLinkIntersection_projection_eq_self_iff_mem_lpMeas
        C target f).1 (hFixed target)
  · intro hMem target
    exact
      (continuous_compact_oriented_periodicOffLinkIntersection_projection_eq_self_iff_mem_lpMeas
        C target f).2
        ((continuous_compact_oriented_periodicOffLinkIntersection_mem_iff C f).1
          hMem target)

/-- The native heat-bath Hamiltonian vector vanishes exactly on the intersection
of all off-link measurable `L²` subspaces. -/
theorem continuous_compact_oriented_periodicOffLinkIntersection_hamiltonian_eq_zero_iff_mem
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    C.heatBathHamiltonianL2 f = 0 ↔
      f ∈ C.periodicAllOffLinkMeasurableL2 := by
  exact
    (continuous_compact_oriented_periodicKernelIntersection_hamiltonian_eq_zero_iff_commonFixed
      C f).trans
      (continuous_compact_oriented_periodicOffLinkIntersection_commonFixed_iff_mem
        C f)

/-- The Hamiltonian quadratic form vanishes exactly on the same all-off-link
measurable intersection. -/
theorem continuous_compact_oriented_periodicOffLinkIntersection_quadratic_eq_zero_iff_mem
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    inner ℝ (C.heatBathHamiltonianL2 f) f = 0 ↔
      f ∈ C.periodicAllOffLinkMeasurableL2 := by
  exact
    (continuous_compact_oriented_periodicKernelIntersection_quadratic_eq_zero_iff_commonFixed
      C f).trans
      (continuous_compact_oriented_periodicOffLinkIntersection_commonFixed_iff_mem
        C f)

/-- Submodule-level kernel identity: the finite-volume heat-bath Hamiltonian
kernel is the intersection of the physical-link off-link measurable spaces. -/
theorem continuous_compact_oriented_periodicOffLinkIntersection_hamiltonian_ker_eq
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    C.heatBathHamiltonianL2.ker = C.periodicAllOffLinkMeasurableL2 := by
  ext f
  change C.heatBathHamiltonianL2 f = 0 ↔
    f ∈ C.periodicAllOffLinkMeasurableL2
  exact
    continuous_compact_oriented_periodicOffLinkIntersection_hamiltonian_eq_zero_iff_mem
      C f

/-- A nonzero exact zero mode in the vacuum-orthogonal sector is exactly a
nonzero vacuum-orthogonal vector measurable with respect to every off-link
sigma-algebra. -/
theorem continuous_compact_oriented_periodicOffLinkIntersection_exactZeroMode_iff_nonzeroAllOffLinkMeasurable
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    C.periodicVacuumOrthogonalExactZeroModeL2 ↔
      C.periodicVacuumOrthogonalNonzeroAllOffLinkMeasurableL2 := by
  constructor
  · rintro ⟨f, hfOrth, hfNe, hfZero⟩
    exact ⟨f, hfOrth, hfNe,
      (continuous_compact_oriented_periodicOffLinkIntersection_hamiltonian_eq_zero_iff_mem
        C f).1 hfZero⟩
  · rintro ⟨f, hfOrth, hfNe, hfMem⟩
    exact ⟨f, hfOrth, hfNe,
      (continuous_compact_oriented_periodicOffLinkIntersection_hamiltonian_eq_zero_iff_mem
        C f).2 hfMem⟩

/-- Actual side-three periodic `SU(2)` Hamiltonian-kernel membership is exactly
membership in every physical-link off-link measurable `L²` space. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_hamiltonian_eq_zero_iff_all_offLink_measurable
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2 f = 0 ↔
      f ∈ periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicAllOffLinkMeasurableL2 := by
  exact
    continuous_compact_oriented_periodicOffLinkIntersection_hamiltonian_eq_zero_iff_mem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem f

/-- Actual side-three periodic `SU(2)` submodule-level kernel identity. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_hamiltonian_ker_eq_all_offLink_measurable :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2.ker =
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicAllOffLinkMeasurableL2 := by
  exact
    continuous_compact_oriented_periodicOffLinkIntersection_hamiltonian_ker_eq
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem

/-- In the actual vacuum-orthogonal sector, exact zero modes are precisely
nonzero vectors in the all-off-link measurable intersection. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_exactZeroMode_iff_nonzeroAllOffLinkMeasurable :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalExactZeroModeL2 ↔
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalNonzeroAllOffLinkMeasurableL2 := by
  exact
    continuous_compact_oriented_periodicOffLinkIntersection_exactZeroMode_iff_nonzeroAllOffLinkMeasurable
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem

/-- Excluding exact zero modes is equivalent to saying that the actual
vacuum-orthogonal sector contains no nonzero vector measurable with respect to
every off-link sigma-algebra.  This remains weaker than approximate-mode
exclusion. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_no_exactZeroMode_iff_no_nonzeroAllOffLinkMeasurable :
    ¬ periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalExactZeroModeL2 ↔
      ¬ periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalNonzeroAllOffLinkMeasurableL2 := by
  exact not_congr
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_exactZeroMode_iff_nonzeroAllOffLinkMeasurable

/-- Compact proof-facing package for the actual off-link measurable
intersection frontier. -/
def periodicHypercubicThreeSpecialUnitaryTwoOffLinkMeasurableIntersectionReceipt : Prop :=
  (∀ f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2 f = 0 ↔
      f ∈ periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicAllOffLinkMeasurableL2) ∧
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2.ker =
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicAllOffLinkMeasurableL2) ∧
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalExactZeroModeL2 ↔
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalNonzeroAllOffLinkMeasurableL2) ∧
    (¬ periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalExactZeroModeL2 ↔
      ¬ periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalNonzeroAllOffLinkMeasurableL2)

/-- The actual finite-volume Hamiltonian kernel has now been realized as an
intersection of concrete `lpMeas` submodules.  Triviality of this intersection
inside the vacuum-orthogonal sector, approximate-zero-mode exclusion, and a
positive Poincare constant remain unproved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoOffLinkMeasurableIntersectionReceipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoOffLinkMeasurableIntersectionReceipt := by
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_hamiltonian_eq_zero_iff_all_offLink_measurable,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_hamiltonian_ker_eq_all_offLink_measurable,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_exactZeroMode_iff_nonzeroAllOffLinkMeasurable,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_no_exactZeroMode_iff_no_nonzeroAllOffLinkMeasurable⟩

end

end MathlibAnalytic
end MGAP4D
