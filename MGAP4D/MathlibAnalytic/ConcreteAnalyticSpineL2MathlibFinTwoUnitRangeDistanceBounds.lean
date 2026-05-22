import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinTwoUnitRangeTriangle

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- The distance between the two distinguished range vectors is always
nonnegative. -/
theorem concrete_l2_mathlib_fin_two_unit_first_second_range_dist_nonneg
    (k n : ℕ) :
    0 ≤ dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) :=
  dist_nonneg

/-- The distance between the two distinguished range vectors lies in `[0, 2]`. -/
theorem concrete_l2_mathlib_fin_two_unit_first_second_range_dist_mem_Icc
    (k n : ℕ) :
    dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ∈ Set.Icc (0 : ℝ) 2 := by
  exact ⟨
    concrete_l2_mathlib_fin_two_unit_first_second_range_dist_nonneg k n,
    concrete_l2_mathlib_fin_two_unit_first_second_range_dist_le_two k n⟩

/-- For distinct selected indices, the distance between the two distinguished
range vectors lies in `(0, 2]`. -/
theorem concrete_l2_mathlib_fin_two_unit_first_second_range_dist_mem_Ioc
    {k n : ℕ} (hkn : k ≠ n) :
    dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ∈ Set.Ioc (0 : ℝ) 2 := by
  exact ⟨
    concrete_l2_mathlib_fin_two_unit_first_second_range_dist_pos hkn,
    concrete_l2_mathlib_fin_two_unit_first_second_range_dist_le_two k n⟩

/-- The range-level first/second distance is bounded by the sum of the two
zero-to-unit distances. -/
theorem concrete_l2_mathlib_fin_two_unit_first_second_range_dist_le_zero_spokes
    (k n : ℕ) :
    dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ≤
      dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
        (concreteL2MathlibFinTwoUnitZeroRangeVector k n) +
      dist (concreteL2MathlibFinTwoUnitZeroRangeVector k n)
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) := by
  exact dist_triangle
    (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
    (concreteL2MathlibFinTwoUnitZeroRangeVector k n)
    (concreteL2MathlibFinTwoUnitSecondRangeVector k n)

/-- Rewriting the zero-spoke bound gives the numerical bound `≤ 1 + 1`. -/
theorem concrete_l2_mathlib_fin_two_unit_first_second_range_dist_le_one_add_one
    (k n : ℕ) :
    dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ≤ (1 : ℝ) + 1 := by
  have h := concrete_l2_mathlib_fin_two_unit_first_second_range_dist_le_zero_spokes k n
  rw [dist_comm (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
      (concreteL2MathlibFinTwoUnitZeroRangeVector k n)] at h
  rw [concrete_l2_mathlib_fin_two_unit_zero_first_range_dist_eq_one,
    concrete_l2_mathlib_fin_two_unit_zero_second_range_dist_eq_one] at h
  exact h

/-- Adapter predicate for the range-level first/second distance bounds. -/
def concreteL2MathlibFinTwoUnitRangeDistanceBoundsAdapter : Prop :=
  (∀ k n : ℕ,
    dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
      (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ∈ Set.Icc (0 : ℝ) 2) ∧
  (∀ {k n : ℕ}, k ≠ n →
    dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
      (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ∈ Set.Ioc (0 : ℝ) 2) ∧
  (∀ k n : ℕ,
    dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
      (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ≤ (1 : ℝ) + 1)

/-- Adapter theorem for the range-level first/second distance bounds. -/
theorem concrete_l2_mathlib_fin_two_unit_range_distance_bounds_adapter_ready :
    concreteL2MathlibFinTwoUnitRangeDistanceBoundsAdapter := by
  exact ⟨
    by intro k n; exact concrete_l2_mathlib_fin_two_unit_first_second_range_dist_mem_Icc k n,
    by intro k n hkn; exact concrete_l2_mathlib_fin_two_unit_first_second_range_dist_mem_Ioc hkn,
    by intro k n; exact concrete_l2_mathlib_fin_two_unit_first_second_range_dist_le_one_add_one k n⟩

/-- Surface for range-level distance bounds between the two distinguished range
vectors.

This layer packages the first/second range distance as lying in `[0,2]`, and in
`(0,2]` when `k ≠ n`.  It is a metric-bound witness only; it does not claim an
exact first/second distance, finite dimensionality, a basis theorem, dense span,
finite-support-domain equivalence, or any operator-theoretic conclusion. -/
structure ConcreteL2MathlibFinTwoUnitRangeDistanceBoundsSurface where
  rangeTriangleReady : concreteAnalyticSpineL2MathlibFinTwoUnitRangeTriangleSurfaceReady
  rangeDistanceBoundsAdapter : concreteL2MathlibFinTwoUnitRangeDistanceBoundsAdapter
  boundaryNotExactFirstSecondDistance : Prop
  boundaryNotFiniteDimensionalTheorem : Prop
  boundaryNotGeneralFiniteFamilyLinearIndependence : Prop
  boundaryNotBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop

/-- Concrete range-level distance bounds surface. -/
def concreteL2MathlibFinTwoUnitRangeDistanceBoundsSurface :
    ConcreteL2MathlibFinTwoUnitRangeDistanceBoundsSurface :=
  { rangeTriangleReady :=
      concrete_analytic_spine_l2_mathlib_fin_two_unit_range_triangle_surface_ready
    rangeDistanceBoundsAdapter :=
      concrete_l2_mathlib_fin_two_unit_range_distance_bounds_adapter_ready
    boundaryNotExactFirstSecondDistance := True
    boundaryNotFiniteDimensionalTheorem := True
    boundaryNotGeneralFiniteFamilyLinearIndependence := True
    boundaryNotBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True }

/-- Readiness for the range-level distance bounds surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitRangeDistanceBoundsSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitRangeTriangleSurfaceReady ∧
  concreteL2MathlibFinTwoUnitRangeDistanceBoundsAdapter ∧
  concreteL2MathlibFinTwoUnitRangeDistanceBoundsSurface.boundaryNotExactFirstSecondDistance ∧
  concreteL2MathlibFinTwoUnitRangeDistanceBoundsSurface.boundaryNotFiniteDimensionalTheorem ∧
  concreteL2MathlibFinTwoUnitRangeDistanceBoundsSurface.boundaryNotGeneralFiniteFamilyLinearIndependence ∧
  concreteL2MathlibFinTwoUnitRangeDistanceBoundsSurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibFinTwoUnitRangeDistanceBoundsSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinTwoUnitRangeDistanceBoundsSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinTwoUnitRangeDistanceBoundsSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinTwoUnitRangeDistanceBoundsSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinTwoUnitRangeDistanceBoundsSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinTwoUnitRangeDistanceBoundsSurface.boundaryNotSpectralAtomTheorem

/-- Readiness theorem for the range-level distance bounds surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_range_distance_bounds_surface_ready :
    concreteAnalyticSpineL2MathlibFinTwoUnitRangeDistanceBoundsSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinTwoUnitRangeDistanceBoundsSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_two_unit_range_triangle_surface_ready <|
      And.intro concrete_l2_mathlib_fin_two_unit_range_distance_bounds_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the range-level distance bounds surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitRangeDistanceBoundsHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitRangeDistanceBoundsSurfaceReady

/-- Boundary theorem for the range-level distance bounds surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_range_distance_bounds_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinTwoUnitRangeDistanceBoundsHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_two_unit_range_distance_bounds_surface_ready

end

end MathlibAnalytic
end MGAP4D
