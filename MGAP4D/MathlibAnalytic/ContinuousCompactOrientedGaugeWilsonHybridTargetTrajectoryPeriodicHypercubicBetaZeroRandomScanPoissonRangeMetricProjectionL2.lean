import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonHybridTargetTrajectoryPeriodicHypercubicBetaZeroRandomScanPoissonLeastSquaresL2
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators Function

noncomputable section

set_option maxRecDepth 8192

/-- A point of a set is closest to a datum when it realizes no larger distance
than any other point of the set. -/
def IsClosestPointToSet
    {E : Type*}
    [NormedAddCommGroup E]
    (s : Set E)
    (f p : E) : Prop :=
  p ∈ s ∧ ∀ q ∈ s, ‖f - p‖ ≤ ‖f - q‖

/-- A nonnegative-number-free exact-distance receipt: the proposed distance is a
lower bound for all points of the set and is attained by one point. -/
def IsExactDistanceToSet
    {E : Type*}
    [NormedAddCommGroup E]
    (s : Set E)
    (f : E)
    (d : ℝ) : Prop :=
  (∀ q ∈ s, d ≤ ‖f - q‖) ∧ ∃ p ∈ s, ‖f - p‖ = d

/-- A closest point whose equality case determines the point is the unique
closest point. -/
theorem existsUnique_isClosestPointToSet_of_eq
    {E : Type*}
    [NormedAddCommGroup E]
    (s : Set E)
    (f p : E)
    (hp : IsClosestPointToSet s f p)
    (hEquality : ∀ q ∈ s, ‖f - q‖ = ‖f - p‖ → q = p) :
    ∃! q, IsClosestPointToSet s f q := by
  refine ⟨p, hp, ?_⟩
  intro q hq
  apply hEquality q hq.1
  exact le_antisymm (hq.2 p hp.1) (hp.2 q hq.1)

/-- Every closest point realizes the exact distance given by its residual norm. -/
theorem isExactDistanceToSet_norm_of_isClosestPointToSet
    {E : Type*}
    [NormedAddCommGroup E]
    (s : Set E)
    (f p : E)
    (hp : IsClosestPointToSet s f p) :
    IsExactDistanceToSet s f ‖f - p‖ := by
  constructor
  · intro q hq
    exact hp.2 q hq
  · exact ⟨p, hp.1, rfl⟩

/-- Orthogonal centering of any datum belongs to the ambient beta-zero Poisson
range, with preimage given by the generalized inverse. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringEndL2_apply_mem_randomScanPoissonOperatorL2_range
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f ∈
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2.toLinearMap.range := by
  refine
    ⟨periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
        f,
      ?_⟩
  rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_generalizedInverse_eq_sub_vacuumProjector,
    ← periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringEndL2_apply]

/-- The distance from a datum to its centered image is exactly the norm of its
unavoidable cardinality-zero vacuum component. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_sub_centeringEndL2_apply_eq_norm_vacuumProjector
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    ‖f - periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f‖ =
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
        0 f‖ := by
  have hResidual :
      f - periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f =
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 f := by
    rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringEndL2_apply]
    abel
  rw [hResidual]

/-- Orthogonal centering is no farther from the datum than any point in the
ambient beta-zero Poisson range. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_sub_centeringEndL2_apply_le_norm_sub_of_mem_randomScanPoissonOperatorL2_range
    (f q : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (hq : q ∈
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2.toLinearMap.range) :
    ‖f - periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f‖ ≤
      ‖f - q‖ := by
  rcases hq with ⟨u, rfl⟩
  have hMinimum :=
    periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoisson_leastSquaresResidual_generalizedInverse_le
      f u
  calc
    ‖f - periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f‖ =
        ‖f -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
              f)‖ := by
        rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_generalizedInverse_eq_sub_vacuumProjector,
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringEndL2_apply]
    _ ≤
        ‖f -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            u‖ := hMinimum

/-- Equality with the centered-distance minimum occurs exactly at the centered
point itself. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_sub_eq_norm_sub_centeringEndL2_apply_iff_eq_centeringEndL2_apply_of_mem_randomScanPoissonOperatorL2_range
    (f q : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure)
    (hq : q ∈
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2.toLinearMap.range) :
    ‖f - q‖ =
        ‖f - periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f‖ ↔
      q = periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f := by
  rcases hq with ⟨u, rfl⟩
  constructor
  · intro hNorm
    apply
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoisson_residual_eq_minimum_iff_poisson_eq_centering
        f u).1
    calc
      ‖f -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            u‖ =
        ‖f - periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f‖ := hNorm
      _ =
        ‖f -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
              f)‖ := by
          rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_generalizedInverse_eq_sub_vacuumProjector,
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringEndL2_apply]
  · intro hImage
    have hMinimum :=
      (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_randomScanPoisson_residual_eq_minimum_iff_poisson_eq_centering
        f u).2 hImage
    calc
      ‖f -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            u‖ =
        ‖f -
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2
            (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
              f)‖ := hMinimum
      _ =
        ‖f - periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f‖ := by
          rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_generalizedInverse_eq_sub_vacuumProjector,
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringEndL2_apply]

/-- Orthogonal centering is a closest point in the actual beta-zero Poisson
range. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringEndL2_apply_isClosestPointTo_randomScanPoissonOperatorL2_range
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    IsClosestPointToSet
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2.toLinearMap.range :
        Set (Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure))
      f
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f) := by
  constructor
  · exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringEndL2_apply_mem_randomScanPoissonOperatorL2_range
        f
  · intro q hq
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_sub_centeringEndL2_apply_le_norm_sub_of_mem_randomScanPoissonOperatorL2_range
        f q hq

/-- Orthogonal centering is the unique closest point in the actual beta-zero
Poisson range. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_existsUnique_isClosestPointTo_randomScanPoissonOperatorL2_range
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    ∃! q,
      IsClosestPointToSet
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2.toLinearMap.range :
          Set (Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure))
        f q := by
  apply existsUnique_isClosestPointToSet_of_eq
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2.toLinearMap.range :
      Set (Lp ℝ 2
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure))
    f
    (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f)
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringEndL2_apply_isClosestPointTo_randomScanPoissonOperatorL2_range
      f)
  intro q hq hNorm
  exact
    (periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_sub_eq_norm_sub_centeringEndL2_apply_iff_eq_centeringEndL2_apply_of_mem_randomScanPoissonOperatorL2_range
      f q hq).1 hNorm

/-- The exact distance to the actual beta-zero Poisson range is the norm of the
cardinality-zero vacuum component, and this distance is attained at centering. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_vacuumProjectorNorm_isExactDistanceTo_randomScanPoissonOperatorL2_range
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    IsExactDistanceToSet
      (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2.toLinearMap.range :
        Set (Lp ℝ 2
          periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure))
      f
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
        0 f‖ := by
  constructor
  · intro q hq
    rw [← periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_sub_centeringEndL2_apply_eq_norm_vacuumProjector]
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_sub_centeringEndL2_apply_le_norm_sub_of_mem_randomScanPoissonOperatorL2_range
        f q hq
  · refine
      ⟨periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f,
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringEndL2_apply_mem_randomScanPoissonOperatorL2_range
          f,
        ?_⟩
    exact
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_sub_centeringEndL2_apply_eq_norm_vacuumProjector
        f

/-- The exact distance to the Poisson range vanishes exactly for data already in
the Poisson range. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_vacuumProjector_eq_zero_iff_mem_randomScanPoissonOperatorL2_range
    (f : Lp ℝ 2
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure) :
    ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
        0 f‖ = 0 ↔
      f ∈
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2.toLinearMap.range := by
  constructor
  · intro hNorm
    have hProjector :
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
            0 f = 0 :=
      norm_eq_zero.mp hNorm
    refine
      ⟨periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonGeneralizedInverseL2
          f,
        ?_⟩
    rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_randomScanPoissonOperatorL2_apply_generalizedInverse_eq_sub_vacuumProjector,
      hProjector, sub_zero]
  · rintro ⟨u, rfl⟩
    rw [periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_fluctuationCardinalityProjectorL2_zero_apply_eq_inner_smul_vacuum,
      periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_inner_vacuum_randomScanPoissonOperatorL2_apply_eq_zero,
      zero_smul, norm_zero]

/-- Structured receipt for the exact metric-projection geometry of the actual
beta-zero Poisson range. -/
structure periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonRangeMetricProjectionL2Receipt :
    Prop where
  centering_mem_range :
    ∀ f : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      periodicHypercubicThreeSpecialUnitaryTwoBetaZeroCenteringEndL2 f ∈
        periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2.toLinearMap.range
  unique_closest_point :
    ∀ f : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      ∃! q,
        IsClosestPointToSet
          (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2.toLinearMap.range :
            Set (Lp ℝ 2
              periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure))
          f q
  exact_distance :
    ∀ f : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      IsExactDistanceToSet
        (periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2.toLinearMap.range :
          Set (Lp ℝ 2
            periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure))
        f
        ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 f‖
  zero_distance_iff_mem_range :
    ∀ f : Lp ℝ 2 periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem.gibbsMeasure,
      ‖periodicHypercubicThreeSpecialUnitaryTwoBetaZeroFluctuationCardinalityProjectorL2
          0 f‖ = 0 ↔
        f ∈
          periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonOperatorL2.toLinearMap.range

/-- The exact beta-zero Poisson range metric-projection receipt is proved. -/
theorem periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonRangeMetricProjectionL2Receipt_proved :
    periodicHypercubicThreeSpecialUnitaryTwoBetaZeroRandomScanPoissonRangeMetricProjectionL2Receipt := by
  refine
    { centering_mem_range :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_centeringEndL2_apply_mem_randomScanPoissonOperatorL2_range
      unique_closest_point :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_existsUnique_isClosestPointTo_randomScanPoissonOperatorL2_range
      exact_distance :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_vacuumProjectorNorm_isExactDistanceTo_randomScanPoissonOperatorL2_range
      zero_distance_iff_mem_range :=
        periodicHypercubicThreeSpecialUnitaryTwoEndpointSystem_betaZero_norm_vacuumProjector_eq_zero_iff_mem_randomScanPoissonOperatorL2_range }

end

end MathlibAnalytic
end MGAP4D
