import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicRayleighInfimumApproximateZeroModesBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators

noncomputable section

set_option maxRecDepth 8192

/-- A Gibbs `L²` vector is a common local heat-bath fixed vector when every
one-link conditional-expectation projection fixes it. -/
def ContinuousCompactOrientedGaugeWilsonSystem.periodicLocalHeatBathCommonFixedL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : Lp ℝ 2 C.gibbsMeasure) : Prop :=
  ∀ target : C.base.geometry.Edge,
    C.singleLinkHeatBathProjectionL2 target f = f

/-- A nonzero exact Hamiltonian zero mode in the Gibbs-vacuum orthogonal
sector.  This is an exact eigenvector condition, not an approximate-mode
condition. -/
def ContinuousCompactOrientedGaugeWilsonSystem.periodicVacuumOrthogonalExactZeroModeL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem) : Prop :=
  ∃ f : Lp ℝ 2 C.gibbsMeasure,
    f ∈ C.VacuumOrthogonalL2 ∧
      f ≠ 0 ∧
        C.heatBathHamiltonianL2 f = 0

/-- A nonzero Gibbs-vacuum orthogonal vector fixed by every local heat-bath
conditional expectation. -/
def ContinuousCompactOrientedGaugeWilsonSystem.periodicVacuumOrthogonalNonzeroCommonFixedL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem) : Prop :=
  ∃ f : Lp ℝ 2 C.gibbsMeasure,
    f ∈ C.VacuumOrthogonalL2 ∧
      f ≠ 0 ∧
        C.periodicLocalHeatBathCommonFixedL2 f

/-- A local fluctuation vanishes exactly when the corresponding conditional
expectation fixes the vector. -/
theorem continuous_compact_oriented_periodicKernelIntersection_fluctuation_eq_zero_iff_projection_eq_self
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (target : C.base.geometry.Edge)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    C.singleLinkHeatBathFluctuationL2 target f = 0 ↔
      C.singleLinkHeatBathProjectionL2 target f = f := by
  rw [continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply]
  constructor
  · intro hZero
    exact (sub_eq_zero.mp hZero).symm
  · intro hFixed
    rw [hFixed, sub_self]

/-- The finite-volume Hamiltonian quadratic form vanishes exactly when every
local projection residual vanishes. -/
theorem continuous_compact_oriented_periodicKernelIntersection_quadratic_eq_zero_iff_all_fluctuations_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    inner ℝ (C.heatBathHamiltonianL2 f) f = 0 ↔
      ∀ target : C.base.geometry.Edge,
        C.singleLinkHeatBathFluctuationL2 target f = 0 := by
  classical
  constructor
  · intro hEnergy target
    have hSum :
        (∑ edge : C.base.geometry.Edge,
          ‖C.singleLinkHeatBathFluctuationL2 edge f‖ ^ 2) = 0 := by
      rw [← continuous_compact_oriented_heatBathHamiltonianL2_quadraticForm]
      exact hEnergy
    have hLe :
        ‖C.singleLinkHeatBathFluctuationL2 target f‖ ^ 2 ≤
          ∑ edge : C.base.geometry.Edge,
            ‖C.singleLinkHeatBathFluctuationL2 edge f‖ ^ 2 := by
      exact Finset.single_le_sum
        (fun edge _ =>
          sq_nonneg ‖C.singleLinkHeatBathFluctuationL2 edge f‖)
        (Finset.mem_univ target)
    rw [hSum] at hLe
    have hNorm :
        ‖C.singleLinkHeatBathFluctuationL2 target f‖ = 0 := by
      nlinarith [norm_nonneg
        (C.singleLinkHeatBathFluctuationL2 target f)]
    exact norm_eq_zero.mp hNorm
  · intro hResidual
    rw [continuous_compact_oriented_heatBathHamiltonianL2_quadraticForm]
    simp [hResidual]

/-- The Hamiltonian vector itself vanishes exactly when all local fluctuation
projections vanish. -/
theorem continuous_compact_oriented_periodicKernelIntersection_hamiltonian_eq_zero_iff_all_fluctuations_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    C.heatBathHamiltonianL2 f = 0 ↔
      ∀ target : C.base.geometry.Edge,
        C.singleLinkHeatBathFluctuationL2 target f = 0 := by
  classical
  constructor
  · intro hHamiltonian
    apply
      (continuous_compact_oriented_periodicKernelIntersection_quadratic_eq_zero_iff_all_fluctuations_zero
        C f).1
    rw [hHamiltonian, inner_zero_left]
  · intro hResidual
    rw [continuous_compact_oriented_heatBathHamiltonianL2_apply]
    simp [hResidual]

/-- All local residuals vanish exactly when the vector is fixed by every local
conditional expectation. -/
theorem continuous_compact_oriented_periodicKernelIntersection_all_fluctuations_zero_iff_commonFixed
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    (∀ target : C.base.geometry.Edge,
      C.singleLinkHeatBathFluctuationL2 target f = 0) ↔
      C.periodicLocalHeatBathCommonFixedL2 f := by
  constructor
  · intro hResidual target
    exact
      (continuous_compact_oriented_periodicKernelIntersection_fluctuation_eq_zero_iff_projection_eq_self
        C target f).1 (hResidual target)
  · intro hFixed target
    exact
      (continuous_compact_oriented_periodicKernelIntersection_fluctuation_eq_zero_iff_projection_eq_self
        C target f).2 (hFixed target)

/-- Exact quadratic zero is the intersection of the local fixed spaces. -/
theorem continuous_compact_oriented_periodicKernelIntersection_quadratic_eq_zero_iff_commonFixed
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    inner ℝ (C.heatBathHamiltonianL2 f) f = 0 ↔
      C.periodicLocalHeatBathCommonFixedL2 f := by
  exact
    (continuous_compact_oriented_periodicKernelIntersection_quadratic_eq_zero_iff_all_fluctuations_zero
      C f).trans
      (continuous_compact_oriented_periodicKernelIntersection_all_fluctuations_zero_iff_commonFixed
        C f)

/-- The operator kernel is exactly the intersection of all local
conditional-expectation fixed spaces. -/
theorem continuous_compact_oriented_periodicKernelIntersection_hamiltonian_eq_zero_iff_commonFixed
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    C.heatBathHamiltonianL2 f = 0 ↔
      C.periodicLocalHeatBathCommonFixedL2 f := by
  exact
    (continuous_compact_oriented_periodicKernelIntersection_hamiltonian_eq_zero_iff_all_fluctuations_zero
      C f).trans
      (continuous_compact_oriented_periodicKernelIntersection_all_fluctuations_zero_iff_commonFixed
        C f)

/-- For this finite sum of orthogonal-projection defects, quadratic zero and
operator-kernel membership coincide. -/
theorem continuous_compact_oriented_periodicKernelIntersection_quadratic_eq_zero_iff_hamiltonian_eq_zero
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (f : Lp ℝ 2 C.gibbsMeasure) :
    inner ℝ (C.heatBathHamiltonianL2 f) f = 0 ↔
      C.heatBathHamiltonianL2 f = 0 := by
  exact
    (continuous_compact_oriented_periodicKernelIntersection_quadratic_eq_zero_iff_commonFixed
      C f).trans
      (continuous_compact_oriented_periodicKernelIntersection_hamiltonian_eq_zero_iff_commonFixed
        C f).symm

/-- A nonzero exact zero mode in the vacuum-orthogonal sector is precisely a
nonzero common fixed vector there. -/
theorem continuous_compact_oriented_periodicKernelIntersection_exactZeroMode_iff_nonzeroCommonFixed
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    C.periodicVacuumOrthogonalExactZeroModeL2 ↔
      C.periodicVacuumOrthogonalNonzeroCommonFixedL2 := by
  constructor
  · rintro ⟨f, hfOrth, hfNe, hfZero⟩
    exact ⟨f, hfOrth, hfNe,
      (continuous_compact_oriented_periodicKernelIntersection_hamiltonian_eq_zero_iff_commonFixed
        C f).1 hfZero⟩
  · rintro ⟨f, hfOrth, hfNe, hfFixed⟩
    exact ⟨f, hfOrth, hfNe,
      (continuous_compact_oriented_periodicKernelIntersection_hamiltonian_eq_zero_iff_commonFixed
        C f).2 hfFixed⟩

/-- Actual side-three periodic `SU(2)` quadratic zero is exactly simultaneous
vanishing of every physical-link heat-bath residual. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_quadratic_eq_zero_iff_all_local_fluctuations_zero
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2 f)
        f = 0 ↔
      ∀ target :
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge,
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
          target f = 0 := by
  exact
    continuous_compact_oriented_periodicKernelIntersection_quadratic_eq_zero_iff_all_fluctuations_zero
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem f

/-- Actual side-three periodic `SU(2)` Hamiltonian-kernel membership is exactly
common fixedness under all physical-link conditional expectations. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_hamiltonian_eq_zero_iff_commonFixed
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2 f = 0 ↔
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicLocalHeatBathCommonFixedL2 f := by
  exact
    continuous_compact_oriented_periodicKernelIntersection_hamiltonian_eq_zero_iff_commonFixed
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem f

/-- In the actual vacuum-orthogonal sector, a nonzero exact Hamiltonian zero
mode exists exactly when a nonzero common local heat-bath fixed vector exists. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_exactZeroMode_iff_nonzeroCommonFixed :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalExactZeroModeL2 ↔
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalNonzeroCommonFixedL2 := by
  exact
    continuous_compact_oriented_periodicKernelIntersection_exactZeroMode_iff_nonzeroCommonFixed
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem

/-- Excluding exact zero-energy vectors is equivalent to excluding nonzero
common fixed vectors in the actual vacuum-orthogonal sector.  This excludes
exact zero modes only; it does not exclude approximate zero modes. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_no_exactZeroMode_iff_no_nonzeroCommonFixed :
    ¬ periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalExactZeroModeL2 ↔
      ¬ periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalNonzeroCommonFixedL2 := by
  exact not_congr
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_exactZeroMode_iff_nonzeroCommonFixed

/-- Compact proof-facing package for the actual finite-volume kernel
intersection frontier. -/
def periodicHypercubicThreeSpecialUnitaryTwoHamiltonianKernelIntersectionReceipt : Prop :=
  (∀ f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
    inner ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2 f)
        f = 0 ↔
      ∀ target :
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge,
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
          target f = 0) ∧
    (∀ f : Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2 f = 0 ↔
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicLocalHeatBathCommonFixedL2 f) ∧
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalExactZeroModeL2 ↔
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalNonzeroCommonFixedL2) ∧
    (¬ periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalExactZeroModeL2 ↔
      ¬ periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalNonzeroCommonFixedL2)

/-- The actual finite-volume heat-bath kernel is the common fixed-space
intersection, and exact zero-mode exclusion is exactly common-fixed-vector
exclusion.  Approximate zero-mode exclusion and a positive Poincare constant
remain unproved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoHamiltonianKernelIntersectionReceipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoHamiltonianKernelIntersectionReceipt := by
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_quadratic_eq_zero_iff_all_local_fluctuations_zero,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_hamiltonian_eq_zero_iff_commonFixed,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_exactZeroMode_iff_nonzeroCommonFixed,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_no_exactZeroMode_iff_no_nonzeroCommonFixed⟩

end

end MathlibAnalytic
end MGAP4D
