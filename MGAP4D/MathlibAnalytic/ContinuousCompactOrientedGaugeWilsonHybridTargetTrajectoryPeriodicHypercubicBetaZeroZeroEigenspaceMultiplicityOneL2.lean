import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroFullSpectrumIntegerGridL2
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set

noncomputable section

set_option maxRecDepth 8192

/-- Scalar multiplication of the normalized Gibbs vacuum, bundled into the actual
beta-zero heat-bath zero eigenspace. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumToZeroEigenspaceLinearMapL2 :
    ℝ →ₗ[ℝ]
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceL2 0 where
  toFun a := ⟨
    a • periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2,
    by
      rw [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceL2,
        Module.End.mem_genEigenspace_one]
      change
        a • periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2 = 0
      rw [continuous_compact_oriented_heatBathHamiltonianL2_vacuum, smul_zero]⟩
  map_add' a b := by
    apply Subtype.ext
    simp [add_smul]
  map_smul' c a := by
    apply Subtype.ext
    simp [smul_smul]

/-- The vacuum-line map is injective because the normalized Gibbs vacuum has
unit norm. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumToZeroEigenspaceLinearMapL2_injective :
    Function.Injective
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumToZeroEigenspaceLinearMapL2 := by
  intro a b hab
  have hVal :
      a • periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2 =
        b • periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2 :=
    congrArg Subtype.val hab
  have hInner := congrArg
    (fun f : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure =>
      inner ℝ periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2 f)
    hVal
  simpa [real_inner_smul_right, real_inner_self_eq_norm_sq,
    continuous_compact_oriented_gibbsVacuumL2_norm] using hInner

/-- Every vector in the actual beta-zero zero eigenspace is its Gibbs-vacuum
coefficient times the normalized vacuum. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumToZeroEigenspaceLinearMapL2_surjective :
    Function.Surjective
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumToZeroEigenspaceLinearMapL2 := by
  intro f
  refine ⟨
    inner ℝ periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsVacuumL2
      (f : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure),
    ?_⟩
  apply Subtype.ext
  have hfMem :
      (f : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) ∈
        Module.End.genEigenspace
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2.toLinearMap
          (0 : ℝ) 1 := by
    simpa [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceL2]
      using f.property
  have hfEigen := Module.End.mem_genEigenspace_one.mp hfMem
  have hfZero :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2
          (f : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) = 0 := by
    simpa using hfEigen
  have hVacuumLine :=
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathHamiltonianL2_eq_zero_iff_eq_inner_smul_vacuum
      (f : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)).mp
      hfZero
  exact hVacuumLine.symm

/-- Explicit linear equivalence between the scalar field and the actual
beta-zero heat-bath zero eigenspace. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroZeroEigenspaceLinearEquivL2 :
    ℝ ≃ₗ[ℝ]
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceL2 0 :=
  LinearEquiv.ofBijective
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumToZeroEigenspaceLinearMapL2
    ⟨
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumToZeroEigenspaceLinearMapL2_injective,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumToZeroEigenspaceLinearMapL2_surjective⟩

/-- The actual beta-zero heat-bath zero eigenspace has exact Cardinal rank one. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_rank_zero_heatBathCardinalityEigenspaceL2_eq_one :
    Module.rank ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceL2 0) =
      1 := by
  rw [← periodicHypercubicThreeSpecialUnitaryTwoBetaZeroZeroEigenspaceLinearEquivL2.rank_eq]
  exact CommSemiring.rank_self ℝ

/-- The range of the cardinality-zero projector has exact Cardinal rank one. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_rank_range_zero_fluctuationCardinalityProjectorL2_eq_one :
    Module.rank ℝ
        (LinearMap.range
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            0).toLinearMap) =
      1 := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_range_fluctuationCardinalityProjectorL2_eq_heatBathCardinalityEigenspaceL2
    0 (by omega)]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_rank_zero_heatBathCardinalityEigenspaceL2_eq_one

/-- The cardinality-zero joint-sector sum has exact Cardinal rank one. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_rank_zero_fluctuationCardinalityJointSectorSumSubmoduleL2_eq_one :
    Module.rank ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityJointSectorSumSubmoduleL2
          0) =
      1 := by
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityJointSectorSumSubmoduleL2_eq_heatBathCardinalityEigenspaceL2
    0 (by omega)]
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_rank_zero_heatBathCardinalityEigenspaceL2_eq_one

/-- Compact receipt for the exact multiplicity-one vacuum sector. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroZeroEigenspaceMultiplicityOneL2Receipt :
    Prop :=
  Function.Bijective
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumToZeroEigenspaceLinearMapL2 ∧
    Module.rank ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceL2 0) =
      1 ∧
    Module.rank ℝ
        (LinearMap.range
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            0).toLinearMap) =
      1 ∧
    Module.rank ℝ
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityJointSectorSumSubmoduleL2
          0) =
      1

/-- The exact multiplicity-one vacuum-sector receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroZeroEigenspaceMultiplicityOneL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroZeroEigenspaceMultiplicityOneL2Receipt := by
  exact ⟨
    ⟨
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumToZeroEigenspaceLinearMapL2_injective,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroVacuumToZeroEigenspaceLinearMapL2_surjective⟩,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_rank_zero_heatBathCardinalityEigenspaceL2_eq_one,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_rank_range_zero_fluctuationCardinalityProjectorL2_eq_one,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_rank_zero_fluctuationCardinalityJointSectorSumSubmoduleL2_eq_one⟩

end

end MathlibAnalytic
end MGAP4D
