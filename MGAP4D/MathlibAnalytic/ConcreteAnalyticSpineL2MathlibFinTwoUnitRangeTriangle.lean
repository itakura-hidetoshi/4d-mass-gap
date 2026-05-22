import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinTwoUnitRangeThreePointMetric

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- The triangle inequality for the three distinguished range points
`0`, `e_k`, and `e_n`. -/
theorem concrete_l2_mathlib_fin_two_unit_range_triangle_zero_first_second
    (k n : ℕ) :
    dist (concreteL2MathlibFinTwoUnitZeroRangeVector k n)
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ≤
      dist (concreteL2MathlibFinTwoUnitZeroRangeVector k n)
        (concreteL2MathlibFinTwoUnitFirstRangeVector k n) +
      dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) := by
  exact dist_triangle
    (concreteL2MathlibFinTwoUnitZeroRangeVector k n)
    (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
    (concreteL2MathlibFinTwoUnitSecondRangeVector k n)

/-- The zero-to-second distance is bounded by the zero-to-first distance plus the
first-to-second distance.  With the two unit-distance identities, this becomes
`1 ≤ 1 + dist(e_k,e_n)`. -/
theorem concrete_l2_mathlib_fin_two_unit_range_triangle_unit_bound
    (k n : ℕ) :
    (1 : ℝ) ≤ 1 + dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
      (concreteL2MathlibFinTwoUnitSecondRangeVector k n) := by
  exact le_add_of_nonneg_right (dist_nonneg)

/-- The distance between the two distinguished unit range vectors is at most two.
This is the triangle inequality through the zero range vector, together with the
unit-distance identities from the three-point metric surface. -/
theorem concrete_l2_mathlib_fin_two_unit_first_second_range_dist_le_two
    (k n : ℕ) :
    dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ≤ 2 := by
  have htri := dist_triangle
    (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
    (concreteL2MathlibFinTwoUnitZeroRangeVector k n)
    (concreteL2MathlibFinTwoUnitSecondRangeVector k n)
  have hzero_first := concrete_l2_mathlib_fin_two_unit_zero_first_range_dist_eq_one k n
  have hzero_second := concrete_l2_mathlib_fin_two_unit_zero_second_range_dist_eq_one k n
  rw [dist_comm (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
      (concreteL2MathlibFinTwoUnitZeroRangeVector k n), hzero_first, hzero_second] at htri
  norm_num at htri
  exact htri

/-- If the selected indices are distinct, the distance between the two
nonzero distinguished range vectors lies in the interval `(0, 2]`. -/
theorem concrete_l2_mathlib_fin_two_unit_first_second_range_dist_pos_and_le_two
    {k n : ℕ} (hkn : k ≠ n) :
    0 < dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ∧
    dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ≤ 2 := by
  exact ⟨
    concrete_l2_mathlib_fin_two_unit_first_second_range_dist_pos hkn,
    concrete_l2_mathlib_fin_two_unit_first_second_range_dist_le_two k n⟩

/-- Adapter predicate for the triangle-inequality sanity surface on the three
range witnesses. -/
def concreteL2MathlibFinTwoUnitRangeTriangleAdapter : Prop :=
  (∀ k n : ℕ,
    dist (concreteL2MathlibFinTwoUnitZeroRangeVector k n)
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ≤
      dist (concreteL2MathlibFinTwoUnitZeroRangeVector k n)
        (concreteL2MathlibFinTwoUnitFirstRangeVector k n) +
      dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n)) ∧
  (∀ k n : ℕ,
    dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ≤ 2) ∧
  (∀ {k n : ℕ}, k ≠ n →
    0 < dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ∧
    dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ≤ 2)

/-- Adapter theorem for the triangle-inequality sanity surface on the three range
witnesses. -/
theorem concrete_l2_mathlib_fin_two_unit_range_triangle_adapter_ready :
    concreteL2MathlibFinTwoUnitRangeTriangleAdapter := by
  exact ⟨
    by intro k n; exact concrete_l2_mathlib_fin_two_unit_range_triangle_zero_first_second k n,
    by intro k n; exact concrete_l2_mathlib_fin_two_unit_first_second_range_dist_le_two k n,
    by intro k n hkn; exact concrete_l2_mathlib_fin_two_unit_first_second_range_dist_pos_and_le_two hkn⟩

/-- Surface for the triangle-inequality sanity check on the three range witnesses.

This layer only records metric consistency among the three explicit points
`0`, `e_k`, and `e_n`: the triangle inequality and the resulting upper bound
`dist(e_k,e_n) ≤ 2`.  It does not claim finite dimensionality of the ambient
space, a basis theorem, dense span, finite-support-domain equivalence, or any
operator-theoretic conclusion. -/
structure ConcreteL2MathlibFinTwoUnitRangeTriangleSurface where
  rangeThreePointMetricReady : concreteAnalyticSpineL2MathlibFinTwoUnitRangeThreePointMetricSurfaceReady
  rangeTriangleAdapter : concreteL2MathlibFinTwoUnitRangeTriangleAdapter
  boundaryNotFiniteDimensionalTheorem : Prop
  boundaryNotGeneralFiniteFamilyLinearIndependence : Prop
  boundaryNotBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop

/-- Concrete triangle-inequality sanity surface for the three range witnesses. -/
def concreteL2MathlibFinTwoUnitRangeTriangleSurface :
    ConcreteL2MathlibFinTwoUnitRangeTriangleSurface :=
  { rangeThreePointMetricReady :=
      concrete_analytic_spine_l2_mathlib_fin_two_unit_range_three_point_metric_surface_ready
    rangeTriangleAdapter := concrete_l2_mathlib_fin_two_unit_range_triangle_adapter_ready
    boundaryNotFiniteDimensionalTheorem := True
    boundaryNotGeneralFiniteFamilyLinearIndependence := True
    boundaryNotBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True }

/-- Readiness for the triangle-inequality sanity surface on the three range
witnesses. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitRangeTriangleSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitRangeThreePointMetricSurfaceReady ∧
  concreteL2MathlibFinTwoUnitRangeTriangleAdapter ∧
  concreteL2MathlibFinTwoUnitRangeTriangleSurface.boundaryNotFiniteDimensionalTheorem ∧
  concreteL2MathlibFinTwoUnitRangeTriangleSurface.boundaryNotGeneralFiniteFamilyLinearIndependence ∧
  concreteL2MathlibFinTwoUnitRangeTriangleSurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibFinTwoUnitRangeTriangleSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinTwoUnitRangeTriangleSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinTwoUnitRangeTriangleSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinTwoUnitRangeTriangleSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinTwoUnitRangeTriangleSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinTwoUnitRangeTriangleSurface.boundaryNotSpectralAtomTheorem

/-- Readiness theorem for the triangle-inequality sanity surface on the three
range witnesses. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_range_triangle_surface_ready :
    concreteAnalyticSpineL2MathlibFinTwoUnitRangeTriangleSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinTwoUnitRangeTriangleSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_two_unit_range_three_point_metric_surface_ready <|
      And.intro concrete_l2_mathlib_fin_two_unit_range_triangle_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the triangle-inequality sanity surface on the three range
witnesses. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitRangeTriangleHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitRangeTriangleSurfaceReady

/-- Boundary theorem for the triangle-inequality sanity surface on the three range
witnesses. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_range_triangle_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinTwoUnitRangeTriangleHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_two_unit_range_triangle_surface_ready

end

end MathlibAnalytic
end MGAP4D
