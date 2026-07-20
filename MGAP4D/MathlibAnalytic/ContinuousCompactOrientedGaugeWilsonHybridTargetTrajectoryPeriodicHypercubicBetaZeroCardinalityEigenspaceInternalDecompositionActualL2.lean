import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroCardinalityEigenspaceInternalDecompositionGenericL2

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators DirectSum Function

noncomputable section

set_option maxRecDepth 8192

local instance periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_cardinalityInternalDecompositionEdgeDecidableEq :
    DecidableEq
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge :=
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_cardinalityRangeEdgeDecidableEq

/-- The actual beta-zero heat-bath eigenspaces indexed by `k = 0, ..., 324`. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceFamilyL2 :
    Fin 325 →
      Submodule ℝ
        (Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :=
  fun k =>
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceL2
      k.1

/-- The actual integer heat-bath eigenspaces are supremum-independent. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathCardinalityEigenspaceFamilyL2_iSupIndep :
    iSupIndep
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceFamilyL2 := by
  let H : Module.End ℝ
      (Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.heatBathHamiltonianL2.toLinearMap
  have hAll :
      iSupIndep (fun μ : ℝ => Module.End.genEigenspace H μ 1) :=
    Module.End.independent_genEigenspace H 1
  have hCastInjective :
      Function.Injective (fun k : Fin 325 => (k.1 : ℝ)) := by
    intro a b hab
    have hVal : a.val = b.val := Nat.cast_inj.mp hab
    exact Fin.ext hVal
  simpa [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceFamilyL2,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceL2,
    H, Function.comp_def]
    using hAll.comp hCastInjective

/-- The actual integer heat-bath eigenspaces span the full Gibbs `L²` space. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_iSup_heatBathCardinalityEigenspaceFamilyL2_eq_top :
    (⨆ k : Fin 325,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceFamilyL2
        k) = ⊤ := by
  classical
  apply le_antisymm
  · exact le_top
  · intro f _hf
    have hDecomp :=
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_sum_range_fluctuationCardinalityProjectorL2_apply_eq
        f
    rw [← hDecomp]
    refine
      (⨆ k : Fin 325,
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceFamilyL2
          k).sum_mem ?_
    intro k hk
    have hkLt : k < 325 := Finset.mem_range.mp hk
    have hkLe : k ≤ 324 := by omega
    have hRangeMem :
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            k f ∈
          LinearMap.range
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
              k).toLinearMap := by
      exact ⟨f, rfl⟩
    have hEigMem :
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            k f ∈
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceFamilyL2
            ⟨k, hkLt⟩ := by
      rw [periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceFamilyL2]
      rw [← periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_range_fluctuationCardinalityProjectorL2_eq_heatBathCardinalityEigenspaceL2
        k hkLe]
      exact hRangeMem
    exact
      (le_iSup
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceFamilyL2
        ⟨k, hkLt⟩)
        hEigMem

/-- The actual beta-zero integer heat-bath eigenspaces form an internal direct
sum decomposition of the full Gibbs `L²` space. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathCardinalityEigenspaceFamilyL2_isInternal :
    DirectSum.IsInternal
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceFamilyL2 := by
  exact
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathCardinalityEigenspaceFamilyL2_iSupIndep
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_iSup_heatBathCardinalityEigenspaceFamilyL2_eq_top

/-- The internal decomposition as an explicit linear equivalence from the
external direct sum of all 325 integer eigenspaces to the full Gibbs `L²`
space. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceDirectSumLinearEquivL2 :
    (⨁ k : Fin 325,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceFamilyL2
        k) ≃ₗ[ℝ]
      Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure :=
  LinearEquiv.ofBijective
    (DirectSum.coeLinearMap
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceFamilyL2)
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathCardinalityEigenspaceFamilyL2_isInternal

end

end MathlibAnalytic
end MGAP4D
