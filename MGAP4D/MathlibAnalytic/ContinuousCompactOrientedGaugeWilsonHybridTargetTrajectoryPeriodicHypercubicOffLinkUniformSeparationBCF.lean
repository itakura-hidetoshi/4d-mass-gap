import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicApproximateOffLinkFixedBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators

noncomputable section

set_option maxRecDepth 8192

/-- Uniform quantitative separation from simultaneous off-link fixedness on the
Gibbs-vacuum orthogonal unit sphere.  At least one physical-link conditional
expectation must move every such unit vector by a fixed positive amount. -/
def ContinuousCompactOrientedGaugeWilsonSystem.periodicVacuumOrthogonalUnitOffLinkUniformSeparationL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem) : Prop :=
  ∃ δ : ℝ,
    0 < δ ∧
      ∀ f : Lp ℝ 2 C.gibbsMeasure,
        f ∈ C.VacuumOrthogonalL2 →
          ‖f‖ = 1 →
            ∃ target : C.base.geometry.Edge,
              δ ≤ ‖f - C.singleLinkHeatBathProjectionL2 target f‖

/-- A positive heat-bath quadratic lower bound on the Gibbs-vacuum orthogonal
unit sphere.  This is a finite-volume coercivity condition, not a proof that
such a constant exists for the actual system. -/
def ContinuousCompactOrientedGaugeWilsonSystem.periodicVacuumOrthogonalUnitHeatBathCoerciveL2
    (C : ContinuousCompactOrientedGaugeWilsonSystem) : Prop :=
  ∃ κ : ℝ,
    0 < κ ∧
      ∀ f : Lp ℝ 2 C.gibbsMeasure,
        f ∈ C.VacuumOrthogonalL2 →
          ‖f‖ = 1 →
            κ ≤ inner ℝ (C.heatBathHamiltonianL2 f) f

/-- Failure of the approximate common-fixed-vector obstruction is exactly a
uniform local-defect separation constant on the vacuum-orthogonal unit sphere. -/
theorem continuous_compact_oriented_periodicOffLinkUniformSeparation_not_approximateOffLinkFixed_iff
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    ¬ C.periodicVacuumOrthogonalUnitApproximateOffLinkFixedL2 ↔
      C.periodicVacuumOrthogonalUnitOffLinkUniformSeparationL2 := by
  classical
  constructor
  · intro hNoApproximate
    by_contra hNoSeparation
    apply hNoApproximate
    unfold
      ContinuousCompactOrientedGaugeWilsonSystem.periodicVacuumOrthogonalUnitOffLinkUniformSeparationL2
      at hNoSeparation
    push_neg at hNoSeparation
    intro ε hε
    exact hNoSeparation ε hε
  · rintro ⟨δ, hδPos, hSeparation⟩ hApproximate
    rcases hApproximate δ hδPos with
      ⟨f, hfOrth, hfNorm, hfFixed⟩
    rcases hSeparation f hfOrth hfNorm with ⟨target, hLower⟩
    exact (not_lt_of_ge hLower) (hfFixed target)

/-- A uniform lower bound on one local projection defect yields a positive
Hamiltonian quadratic lower bound by the exact finite sum-of-squares identity. -/
theorem continuous_compact_oriented_periodicOffLinkUniformSeparation_implies_heatBathCoercive
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    C.periodicVacuumOrthogonalUnitOffLinkUniformSeparationL2 →
      C.periodicVacuumOrthogonalUnitHeatBathCoerciveL2 := by
  classical
  rintro ⟨δ, hδPos, hSeparation⟩
  refine ⟨δ ^ 2, sq_pos_of_pos hδPos, ?_⟩
  intro f hfOrth hfNorm
  rcases hSeparation f hfOrth hfNorm with ⟨target, hTarget⟩
  rw [continuous_compact_oriented_heatBathHamiltonianL2_quadraticForm]
  have hTargetFluctuation :
      δ ≤ ‖C.singleLinkHeatBathFluctuationL2 target f‖ := by
    simpa [continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply] using
      hTarget
  have hTargetSq :
      δ ^ 2 ≤ ‖C.singleLinkHeatBathFluctuationL2 target f‖ ^ 2 := by
    nlinarith [norm_nonneg
      (C.singleLinkHeatBathFluctuationL2 target f)]
  have hTermLe :
      ‖C.singleLinkHeatBathFluctuationL2 target f‖ ^ 2 ≤
        ∑ edge : C.base.geometry.Edge,
          ‖C.singleLinkHeatBathFluctuationL2 edge f‖ ^ 2 := by
    exact Finset.single_le_sum
      (fun edge _ =>
        sq_nonneg ‖C.singleLinkHeatBathFluctuationL2 edge f‖)
      (Finset.mem_univ target)
  exact hTargetSq.trans hTermLe

/-- Conversely, a positive Hamiltonian lower bound forces at least one local
projection defect to be uniformly large.  The finite-link conversion uses the
scale `sqrt (κ / (|E| + 1))`. -/
theorem continuous_compact_oriented_periodicOffLinkUniformSeparation_heatBathCoercive_implies
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    C.periodicVacuumOrthogonalUnitHeatBathCoerciveL2 →
      C.periodicVacuumOrthogonalUnitOffLinkUniformSeparationL2 := by
  classical
  rintro ⟨κ, hκPos, hCoercive⟩
  let N : ℝ := Fintype.card C.base.geometry.Edge
  have hNNonneg : 0 ≤ N := by
    dsimp [N]
    positivity
  have hNPlusPos : 0 < N + 1 := by
    linarith
  have hQuotPos : 0 < κ / (N + 1) :=
    div_pos hκPos hNPlusPos
  let δ : ℝ := Real.sqrt (κ / (N + 1))
  have hδPos : 0 < δ := by
    dsimp [δ]
    exact Real.sqrt_pos.2 hQuotPos
  have hδSq : δ ^ 2 = κ / (N + 1) := by
    dsimp [δ]
    exact Real.sq_sqrt (le_of_lt hQuotPos)
  refine ⟨δ, hδPos, ?_⟩
  intro f hfOrth hfNorm
  by_contra hNoTarget
  push_neg at hNoTarget
  have hEach :
      ∀ target : C.base.geometry.Edge,
        ‖C.singleLinkHeatBathFluctuationL2 target f‖ ^ 2 ≤
          κ / (N + 1) := by
    intro target
    have hNormLt :
        ‖C.singleLinkHeatBathFluctuationL2 target f‖ < δ := by
      simpa [continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply] using
        hNoTarget target
    have hSqLt :
        ‖C.singleLinkHeatBathFluctuationL2 target f‖ ^ 2 < δ ^ 2 := by
      nlinarith [norm_nonneg
        (C.singleLinkHeatBathFluctuationL2 target f)]
    exact le_of_lt (by simpa [hδSq] using hSqLt)
  have hSumLe :
      (∑ target : C.base.geometry.Edge,
          ‖C.singleLinkHeatBathFluctuationL2 target f‖ ^ 2) ≤
        N * (κ / (N + 1)) := by
    calc
      (∑ target : C.base.geometry.Edge,
          ‖C.singleLinkHeatBathFluctuationL2 target f‖ ^ 2) ≤
          ∑ _target : C.base.geometry.Edge, κ / (N + 1) := by
            exact Finset.sum_le_sum fun target _ => hEach target
      _ = N * (κ / (N + 1)) := by
        simp [N]
  have hNBound : N * (κ / (N + 1)) < κ := by
    have hStep :
        N * (κ / (N + 1)) <
          (N + 1) * (κ / (N + 1)) :=
      mul_lt_mul_of_pos_right (lt_add_one N) hQuotPos
    have hCancel :
        (N + 1) * (κ / (N + 1)) = κ := by
      field_simp [ne_of_gt hNPlusPos]
    rw [hCancel] at hStep
    exact hStep
  have hEnergyLower := hCoercive f hfOrth hfNorm
  rw [continuous_compact_oriented_heatBathHamiltonianL2_quadraticForm] at hEnergyLower
  exact (not_lt_of_ge hEnergyLower) (lt_of_le_of_lt hSumLe hNBound)

/-- For a finite physical-link family, uniform separation by one local defect
and positive heat-bath coercivity are equivalent quantitative conditions. -/
theorem continuous_compact_oriented_periodicOffLinkUniformSeparation_iff_heatBathCoercive
    (C : ContinuousCompactOrientedGaugeWilsonSystem) :
    C.periodicVacuumOrthogonalUnitOffLinkUniformSeparationL2 ↔
      C.periodicVacuumOrthogonalUnitHeatBathCoerciveL2 := by
  exact ⟨
    continuous_compact_oriented_periodicOffLinkUniformSeparation_implies_heatBathCoercive C,
    continuous_compact_oriented_periodicOffLinkUniformSeparation_heatBathCoercive_implies C⟩

/-- With a nonempty vacuum-orthogonal unit energy set, strict positivity of the
Rayleigh infimum is exactly uniform quantitative off-link separation. -/
theorem continuous_compact_oriented_periodicOffLinkUniformSeparation_rayleighInfimum_pos_iff
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hNonempty :
      C.periodicVacuumOrthogonalUnitRayleighEnergySet.Nonempty) :
    0 < C.periodicVacuumOrthogonalUnitRayleighInfimum ↔
      C.periodicVacuumOrthogonalUnitOffLinkUniformSeparationL2 := by
  exact
    (continuous_compact_oriented_periodicVacuumOrthogonalUnitRayleighInfimum_pos_iff_not_approximateZeroEnergy
      C hNonempty).trans
      ((not_congr
        (continuous_compact_oriented_periodicApproximateOffLinkFixed_approximateZeroEnergy_iff C)).trans
        (continuous_compact_oriented_periodicOffLinkUniformSeparation_not_approximateOffLinkFixed_iff C))

/-- Equivalently, strict positivity of the Rayleigh infimum is exactly a
positive heat-bath quadratic lower bound on the vacuum-orthogonal unit sphere. -/
theorem continuous_compact_oriented_periodicOffLinkUniformSeparation_rayleighInfimum_pos_iff_heatBathCoercive
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (hNonempty :
      C.periodicVacuumOrthogonalUnitRayleighEnergySet.Nonempty) :
    0 < C.periodicVacuumOrthogonalUnitRayleighInfimum ↔
      C.periodicVacuumOrthogonalUnitHeatBathCoerciveL2 := by
  exact
    (continuous_compact_oriented_periodicOffLinkUniformSeparation_rayleighInfimum_pos_iff
      C hNonempty).trans
      (continuous_compact_oriented_periodicOffLinkUniformSeparation_iff_heatBathCoercive C)

/-- Actual side-three periodic `SU(2)` strict positivity is exactly uniform
separation by at least one physical-link projection defect. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_rayleighInfimum_pos_iff_offLinkUniformSeparation :
    0 <
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitRayleighInfimum ↔
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitOffLinkUniformSeparationL2 := by
  exact
    continuous_compact_oriented_periodicOffLinkUniformSeparation_rayleighInfimum_pos_iff
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_vacuumOrthogonalUnitRayleighEnergySet_nonempty

/-- Actual side-three periodic `SU(2)` strict positivity is equivalently a
positive heat-bath coercivity constant on the vacuum-orthogonal unit sphere. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_rayleighInfimum_pos_iff_heatBathCoercive :
    0 <
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitRayleighInfimum ↔
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitHeatBathCoerciveL2 := by
  exact
    continuous_compact_oriented_periodicOffLinkUniformSeparation_rayleighInfimum_pos_iff_heatBathCoercive
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_vacuumOrthogonalUnitRayleighEnergySet_nonempty

/-- Compact proof-facing package for the actual quantitative separation
frontier. -/
def periodicHypercubicThreeSpecialUnitaryTwoOffLinkUniformSeparationReceipt : Prop :=
  (0 <
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitRayleighInfimum ↔
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitOffLinkUniformSeparationL2) ∧
  (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitOffLinkUniformSeparationL2 ↔
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitHeatBathCoerciveL2) ∧
  (0 <
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitRayleighInfimum ↔
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.periodicVacuumOrthogonalUnitHeatBathCoerciveL2)

/-- The actual finite-volume positive-gap frontier is now exactly a uniform
local-defect separation/coercivity statement.  This theorem does not establish
that the separation constant exists, nor any volume-uniform or continuum bound. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoOffLinkUniformSeparationReceipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoOffLinkUniformSeparationReceipt := by
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_rayleighInfimum_pos_iff_offLinkUniformSeparation,
    continuous_compact_oriented_periodicOffLinkUniformSeparation_iff_heatBathCoercive
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_rayleighInfimum_pos_iff_heatBathCoercive⟩

end

end MathlibAnalytic
end MGAP4D
