import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroCenteredWilsonCoordinateFiniteSetBCF
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

local instance periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_finiteSetModeEdgeDecidableEq :
    DecidableEq
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge :=
  Classical.decEq _

/-- Gibbs `L²` representative of the centered coordinate product over a finite
selected set. -/
noncomputable def periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFiniteSetProductModeL2
    (s : Finset
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge) :
    Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure :=
  periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF
    (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF s)

/-- Every finite-set product mode is nonzero, including the empty-set vacuum
mode. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFiniteSetProductModeL2_ne_zero
    (s : Finset
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFiniteSetProductModeL2 s ≠ 0 := by
  intro hZero
  have hToLp :
      BoundedContinuousFunction.toLp
          2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure
          ℝ
          (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF s) =
        BoundedContinuousFunction.toLp
          2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure
          ℝ
          0 := by
    change
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF
          (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF s) =
        0 at hZero
    simpa [ContinuousCompactOrientedGaugeWilsonSystem.gibbsL2RepresentativeBCF]
      using hZero
  have hBCF :
      periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF s =
        0 :=
    (BoundedContinuousFunction.toLp_injective
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
      hToLp
  exact
    periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF_ne_zero
      s hBCF

/-- Every selected fluctuation projection fixes the finite-set product mode. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFiniteSetProductModeL2_fluctuation_eq_self_of_mem
    (s : Finset
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (edge : periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hEdge : edge ∈ s) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        edge
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFiniteSetProductModeL2 s) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFiniteSetProductModeL2 s := by
  rw [continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply]
  have hProjection :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionL2
          edge
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFiniteSetProductModeL2 s) =
        0 := by
    change
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionL2
          edge
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF
            (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF s)) =
        0
    rw [
      continuous_compact_oriented_singleLinkHeatBathProjectionL2_gibbsL2RepresentativeBCF_of_beta_eq_zero
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
        edge
        (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF s)]
    have hBCF :
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionBCFOfBetaZero
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
            edge
            (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF s) =
          0 := by
      ext A
      exact congrFun
        (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF_projection_eq_zero_of_mem
          s edge hEdge) A
    rw [hBCF]
    simp [ContinuousCompactOrientedGaugeWilsonSystem.gibbsL2RepresentativeBCF]
  rw [hProjection, sub_zero]

/-- Every unselected fluctuation projection annihilates the finite-set product
mode. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFiniteSetProductModeL2_fluctuation_eq_zero_of_not_mem
    (s : Finset
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (edge : periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge)
    (hEdge : edge ∉ s) :
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathFluctuationL2
        edge
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFiniteSetProductModeL2 s) =
      0 := by
  rw [continuous_compact_oriented_singleLinkHeatBathFluctuationL2_apply]
  have hProjection :
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionL2
          edge
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFiniteSetProductModeL2 s) =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFiniteSetProductModeL2 s := by
    change
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionL2
          edge
          (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF
            (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF s)) =
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsL2RepresentativeBCF
          (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF s)
    rw [
      continuous_compact_oriented_singleLinkHeatBathProjectionL2_gibbsL2RepresentativeBCF_of_beta_eq_zero
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
        edge
        (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF s)]
    have hBCF :
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.singleLinkHeatBathProjectionBCFOfBetaZero
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_beta_eq_zero
            edge
            (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF s) =
          periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF s := by
      ext A
      exact congrFun
        (periodicHypercubicThreeSpecialUnitaryTwoCenteredWilsonCoordinateFiniteSetBCF_projection_eq_self_of_not_mem
          s edge hEdge) A
    rw [hBCF]
  rw [hProjection, sub_self]

/-- The finite-set product mode has the exact fluctuation profile of its
selected set. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_finiteSetProductModeL2_mem_fluctuationJointSector
    (s : Finset
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFiniteSetProductModeL2 s ∈
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.fluctuationJointSectorSubmoduleL2
        s := by
  rw [continuous_compact_oriented_fluctuationJointSectorSubmoduleL2_mem_iff]
  exact ⟨
    fun edge hEdge =>
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFiniteSetProductModeL2_fluctuation_eq_self_of_mem
        s edge hEdge,
    fun edge hEdge =>
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFiniteSetProductModeL2_fluctuation_eq_zero_of_not_mem
        s edge hEdge⟩

/-- The actual beta-zero cardinality-`s.card` projector fixes the finite-set
product mode. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_card_apply_finiteSetProductMode_eq
    (s : Finset
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
        s.card
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFiniteSetProductModeL2 s) =
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFiniteSetProductModeL2 s := by
  exact
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_apply_eq_self_of_mem_jointSector
      s.card s rfl
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_finiteSetProductModeL2_mem_fluctuationJointSector
        s)

/-- Every actual cardinality indexed by a finite selected set has a nonzero
projector. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_card_ne_zero
    (s : Finset
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.base.geometry.Edge) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
      s.card ≠ 0 := by
  intro hZero
  have hApply := congrArg
    (fun T :
      Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure →L[ℝ]
        Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure =>
      T (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFiniteSetProductModeL2 s))
    hZero
  have hProjectedZero :
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          s.card
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFiniteSetProductModeL2 s) =
        0 := by
    simpa using hApply
  have hProjectedSelf :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_card_apply_finiteSetProductMode_eq
      s
  exact
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFiniteSetProductModeL2_ne_zero
      s (hProjectedSelf.symm.trans hProjectedZero)

end

end MathlibAnalytic
end MGAP4D
