import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinTwoUnitRangeThreePoint

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- The zero range vector and the first distinguished range vector have positive
distance. -/
theorem concrete_l2_mathlib_fin_two_unit_zero_first_range_dist_pos
    (k n : ℕ) :
    0 < dist (concreteL2MathlibFinTwoUnitZeroRangeVector k n)
        (concreteL2MathlibFinTwoUnitFirstRangeVector k n) := by
  exact dist_pos.mpr (concrete_l2_mathlib_fin_two_unit_zero_range_vector_ne_first k n)

/-- The zero range vector and the second distinguished range vector have positive
distance. -/
theorem concrete_l2_mathlib_fin_two_unit_zero_second_range_dist_pos
    (k n : ℕ) :
    0 < dist (concreteL2MathlibFinTwoUnitZeroRangeVector k n)
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) := by
  exact dist_pos.mpr (concrete_l2_mathlib_fin_two_unit_zero_range_vector_ne_second k n)

/-- The first and second distinguished range vectors have positive distance when
the selected indices are distinct. -/
theorem concrete_l2_mathlib_fin_two_unit_first_second_range_dist_pos
    {k n : ℕ} (hkn : k ≠ n) :
    0 < dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) :=
  concrete_l2_mathlib_fin_two_unit_range_vectors_dist_pos hkn

/-- The zero range vector and the first distinguished range vector have nonzero
distance. -/
theorem concrete_l2_mathlib_fin_two_unit_zero_first_range_dist_ne_zero
    (k n : ℕ) :
    dist (concreteL2MathlibFinTwoUnitZeroRangeVector k n)
        (concreteL2MathlibFinTwoUnitFirstRangeVector k n) ≠ 0 := by
  exact ne_of_gt (concrete_l2_mathlib_fin_two_unit_zero_first_range_dist_pos k n)

/-- The zero range vector and the second distinguished range vector have nonzero
distance. -/
theorem concrete_l2_mathlib_fin_two_unit_zero_second_range_dist_ne_zero
    (k n : ℕ) :
    dist (concreteL2MathlibFinTwoUnitZeroRangeVector k n)
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ≠ 0 := by
  exact ne_of_gt (concrete_l2_mathlib_fin_two_unit_zero_second_range_dist_pos k n)

/-- For distinct selected indices, all three pairwise distances among `0`, `e_k`,
and `e_n` inside the range are positive. -/
theorem concrete_l2_mathlib_fin_two_unit_range_three_point_pairwise_dist_pos
    {k n : ℕ} (hkn : k ≠ n) :
    0 < dist (concreteL2MathlibFinTwoUnitZeroRangeVector k n)
        (concreteL2MathlibFinTwoUnitFirstRangeVector k n) ∧
    0 < dist (concreteL2MathlibFinTwoUnitZeroRangeVector k n)
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ∧
    0 < dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) := by
  exact ⟨
    concrete_l2_mathlib_fin_two_unit_zero_first_range_dist_pos k n,
    concrete_l2_mathlib_fin_two_unit_zero_second_range_dist_pos k n,
    concrete_l2_mathlib_fin_two_unit_first_second_range_dist_pos hkn⟩

/-- The distance from zero to the first distinguished range vector is one. -/
theorem concrete_l2_mathlib_fin_two_unit_zero_first_range_dist_eq_one
    (k n : ℕ) :
    dist (concreteL2MathlibFinTwoUnitZeroRangeVector k n)
        (concreteL2MathlibFinTwoUnitFirstRangeVector k n) = 1 := by
  rw [dist_zero_left]
  exact concrete_l2_mathlib_fin_two_unit_first_range_vector_norm_eq_one k n

/-- The distance from zero to the second distinguished range vector is one. -/
theorem concrete_l2_mathlib_fin_two_unit_zero_second_range_dist_eq_one
    (k n : ℕ) :
    dist (concreteL2MathlibFinTwoUnitZeroRangeVector k n)
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) = 1 := by
  rw [dist_zero_left]
  exact concrete_l2_mathlib_fin_two_unit_second_range_vector_norm_eq_one k n

/-- Adapter predicate for the metric three-point witness surface of the two-unit
synthesis range. -/
def concreteL2MathlibFinTwoUnitRangeThreePointMetricAdapter : Prop :=
  (∀ k n : ℕ,
    dist (concreteL2MathlibFinTwoUnitZeroRangeVector k n)
      (concreteL2MathlibFinTwoUnitFirstRangeVector k n) = 1) ∧
  (∀ k n : ℕ,
    dist (concreteL2MathlibFinTwoUnitZeroRangeVector k n)
      (concreteL2MathlibFinTwoUnitSecondRangeVector k n) = 1) ∧
  (∀ {k n : ℕ}, k ≠ n →
    0 < dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
      (concreteL2MathlibFinTwoUnitSecondRangeVector k n)) ∧
  (∀ {k n : ℕ}, k ≠ n →
    0 < dist (concreteL2MathlibFinTwoUnitZeroRangeVector k n)
      (concreteL2MathlibFinTwoUnitFirstRangeVector k n) ∧
    0 < dist (concreteL2MathlibFinTwoUnitZeroRangeVector k n)
      (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ∧
    0 < dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
      (concreteL2MathlibFinTwoUnitSecondRangeVector k n))

/-- Adapter theorem for the metric three-point witness surface of the two-unit
synthesis range. -/
theorem concrete_l2_mathlib_fin_two_unit_range_three_point_metric_adapter_ready :
    concreteL2MathlibFinTwoUnitRangeThreePointMetricAdapter := by
  exact ⟨
    by intro k n; exact concrete_l2_mathlib_fin_two_unit_zero_first_range_dist_eq_one k n,
    by intro k n; exact concrete_l2_mathlib_fin_two_unit_zero_second_range_dist_eq_one k n,
    by intro k n hkn; exact concrete_l2_mathlib_fin_two_unit_first_second_range_dist_pos hkn,
    by intro k n hkn; exact concrete_l2_mathlib_fin_two_unit_range_three_point_pairwise_dist_pos hkn⟩

/-- Surface for the metric three-point witness in the two-unit synthesis range.

The range-level points `0`, `e_k`, and `e_n` are metrically separated; distances
from zero to the two unit vectors are exactly one, and for `k ≠ n` all three
pairwise distances are positive. -/
structure ConcreteL2MathlibFinTwoUnitRangeThreePointMetricSurface where
  rangeThreePointReady : concreteAnalyticSpineL2MathlibFinTwoUnitRangeThreePointSurfaceReady
  rangeThreePointMetricAdapter : concreteL2MathlibFinTwoUnitRangeThreePointMetricAdapter
  boundaryNotFiniteDimensionalTheorem : Prop
  boundaryNotGeneralFiniteFamilyLinearIndependence : Prop
  boundaryNotBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop

/-- Concrete metric three-point witness surface for the two-unit synthesis range. -/
def concreteL2MathlibFinTwoUnitRangeThreePointMetricSurface :
    ConcreteL2MathlibFinTwoUnitRangeThreePointMetricSurface :=
  { rangeThreePointReady :=
      concrete_analytic_spine_l2_mathlib_fin_two_unit_range_three_point_surface_ready
    rangeThreePointMetricAdapter :=
      concrete_l2_mathlib_fin_two_unit_range_three_point_metric_adapter_ready
    boundaryNotFiniteDimensionalTheorem := True
    boundaryNotGeneralFiniteFamilyLinearIndependence := True
    boundaryNotBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True }

/-- Readiness for the metric three-point witness surface of the two-unit synthesis
range. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitRangeThreePointMetricSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitRangeThreePointSurfaceReady ∧
  concreteL2MathlibFinTwoUnitRangeThreePointMetricAdapter ∧
  concreteL2MathlibFinTwoUnitRangeThreePointMetricSurface.boundaryNotFiniteDimensionalTheorem ∧
  concreteL2MathlibFinTwoUnitRangeThreePointMetricSurface.boundaryNotGeneralFiniteFamilyLinearIndependence ∧
  concreteL2MathlibFinTwoUnitRangeThreePointMetricSurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibFinTwoUnitRangeThreePointMetricSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinTwoUnitRangeThreePointMetricSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinTwoUnitRangeThreePointMetricSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinTwoUnitRangeThreePointMetricSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinTwoUnitRangeThreePointMetricSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinTwoUnitRangeThreePointMetricSurface.boundaryNotSpectralAtomTheorem

/-- Readiness theorem for the metric three-point witness surface of the two-unit
synthesis range. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_range_three_point_metric_surface_ready :
    concreteAnalyticSpineL2MathlibFinTwoUnitRangeThreePointMetricSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinTwoUnitRangeThreePointMetricSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_two_unit_range_three_point_surface_ready <|
      And.intro concrete_l2_mathlib_fin_two_unit_range_three_point_metric_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the metric three-point witness surface of the two-unit
synthesis range. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitRangeThreePointMetricHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitRangeThreePointMetricSurfaceReady

/-- Boundary theorem for the metric three-point witness surface of the two-unit
synthesis range. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_range_three_point_metric_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinTwoUnitRangeThreePointMetricHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_two_unit_range_three_point_metric_surface_ready

end

end MathlibAnalytic
end MGAP4D
