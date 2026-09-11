import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroCardinalityEigenspaceInternalDecompositionActualL2
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators DirectSum Function

noncomputable section

/-- The total number of explicit centered-product modes, summed over all
cardinalities, is `2^324`. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZero_sum_range_choose_324_eq_two_pow_324 :
    (∑ k ∈ Finset.range 325, Nat.choose 324 k) = 2 ^ 324 := by
  simpa using Nat.sum_range_choose 324

/-- The full actual Gibbs `L²` space has Cardinal rank at least `2^324`,
witnessed by the linearly independent centered-product modes indexed by every
subset of the 324 physical links. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_two_pow_324_le_rank_gibbsL2 :
    ((2 ^ 324 : ℕ) : Cardinal) ≤
      Module.rank ℝ
        (Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) := by
  have hRank :=
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFiniteSetProductModeL2_linearIndependent.cardinal_le_rank
  simpa [Cardinal.mk_fintype, Fintype.card_finset,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_edgeCard_eq_324]
    using hRank

/-- Compact receipt for the actual internal eigenspace decomposition and the
global Boolean-cube rank lower bound. -/
def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityEigenspaceInternalDecompositionL2Receipt :
    Prop :=
  iSupIndep
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceFamilyL2 ∧
    (⨆ k : Fin 325,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceFamilyL2
        k) = ⊤ ∧
    DirectSum.IsInternal
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroHeatBathCardinalityEigenspaceFamilyL2 ∧
    (∑ k ∈ Finset.range 325, Nat.choose 324 k) = 2 ^ 324 ∧
    ((2 ^ 324 : ℕ) : Cardinal) ≤
      Module.rank ℝ
        (Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)

/-- The internal eigenspace decomposition and global `2^324` rank lower-bound
receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityEigenspaceInternalDecompositionL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCardinalityEigenspaceInternalDecompositionL2Receipt := by
  exact ⟨
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathCardinalityEigenspaceFamilyL2_iSupIndep,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_iSup_heatBathCardinalityEigenspaceFamilyL2_eq_top,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_heatBathCardinalityEigenspaceFamilyL2_isInternal,
    periodicHypercubicThreeSpecialUnitaryTwoBetaZero_sum_range_choose_324_eq_two_pow_324,
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_two_pow_324_le_rank_gibbsL2⟩

end

end MathlibAnalytic
end MGAP4D
