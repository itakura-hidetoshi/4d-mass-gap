import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinTwoUnitRangeDistanceBounds

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Exported lower bound for the first/second range distance. -/
theorem concrete_l2_mathlib_fin_two_unit_first_second_range_dist_lower_bound
    (k n : ℕ) :
    0 ≤ dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) :=
  (concrete_l2_mathlib_fin_two_unit_first_second_range_dist_mem_Icc k n).1

/-- Exported upper bound for the first/second range distance. -/
theorem concrete_l2_mathlib_fin_two_unit_first_second_range_dist_upper_bound
    (k n : ℕ) :
    dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ≤ 2 :=
  (concrete_l2_mathlib_fin_two_unit_first_second_range_dist_mem_Icc k n).2

/-- Exported strict lower bound for the first/second range distance when the
selected indices are distinct. -/
theorem concrete_l2_mathlib_fin_two_unit_first_second_range_dist_strict_lower_bound
    {k n : ℕ} (hkn : k ≠ n) :
    0 < dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) :=
  (concrete_l2_mathlib_fin_two_unit_first_second_range_dist_mem_Ioc hkn).1

/-- Exported upper bound for the first/second range distance when the selected
indices are distinct. -/
theorem concrete_l2_mathlib_fin_two_unit_first_second_range_dist_upper_bound_of_ne
    {k n : ℕ} (hkn : k ≠ n) :
    dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ≤ 2 :=
  (concrete_l2_mathlib_fin_two_unit_first_second_range_dist_mem_Ioc hkn).2

/-- Exported nonzero distance for the first/second range vectors when the selected
indices are distinct. -/
theorem concrete_l2_mathlib_fin_two_unit_first_second_range_dist_ne_zero_of_ne
    {k n : ℕ} (hkn : k ≠ n) :
    dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ≠ 0 := by
  exact ne_of_gt
    (concrete_l2_mathlib_fin_two_unit_first_second_range_dist_strict_lower_bound hkn)

/-- Exported closed interval bounds as a pair. -/
theorem concrete_l2_mathlib_fin_two_unit_first_second_range_dist_bounds_pair
    (k n : ℕ) :
    0 ≤ dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ∧
    dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ≤ 2 :=
  concrete_l2_mathlib_fin_two_unit_first_second_range_dist_mem_Icc k n

/-- Exported half-open interval bounds as a pair for distinct selected indices. -/
theorem concrete_l2_mathlib_fin_two_unit_first_second_range_dist_strict_bounds_pair
    {k n : ℕ} (hkn : k ≠ n) :
    0 < dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ∧
    dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ≤ 2 :=
  concrete_l2_mathlib_fin_two_unit_first_second_range_dist_mem_Ioc hkn

/-- Adapter predicate for exported first/second range-distance bounds. -/
def concreteL2MathlibFinTwoUnitRangeDistanceExportsAdapter : Prop :=
  (∀ k n : ℕ,
    0 ≤ dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
      (concreteL2MathlibFinTwoUnitSecondRangeVector k n)) ∧
  (∀ k n : ℕ,
    dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
      (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ≤ 2) ∧
  (∀ {k n : ℕ}, k ≠ n →
    dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
      (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ≠ 0)

/-- Adapter theorem for exported first/second range-distance bounds. -/
theorem concrete_l2_mathlib_fin_two_unit_range_distance_exports_adapter_ready :
    concreteL2MathlibFinTwoUnitRangeDistanceExportsAdapter := by
  exact ⟨
    by intro k n; exact concrete_l2_mathlib_fin_two_unit_first_second_range_dist_lower_bound k n,
    by intro k n; exact concrete_l2_mathlib_fin_two_unit_first_second_range_dist_upper_bound k n,
    by intro k n hkn; exact concrete_l2_mathlib_fin_two_unit_first_second_range_dist_ne_zero_of_ne hkn⟩

/-- Surface exporting reusable lower/upper/nonzero distance facts for the two
range unit witnesses.

This layer contains no new geometry; it only exposes the interval-bound surface
as small theorems suitable for downstream imports. -/
structure ConcreteL2MathlibFinTwoUnitRangeDistanceExportsSurface where
  rangeDistanceBoundsReady : concreteAnalyticSpineL2MathlibFinTwoUnitRangeDistanceBoundsSurfaceReady
  rangeDistanceExportsAdapter : concreteL2MathlibFinTwoUnitRangeDistanceExportsAdapter
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

/-- Concrete range-distance export surface. -/
def concreteL2MathlibFinTwoUnitRangeDistanceExportsSurface :
    ConcreteL2MathlibFinTwoUnitRangeDistanceExportsSurface :=
  { rangeDistanceBoundsReady :=
      concrete_analytic_spine_l2_mathlib_fin_two_unit_range_distance_bounds_surface_ready
    rangeDistanceExportsAdapter :=
      concrete_l2_mathlib_fin_two_unit_range_distance_exports_adapter_ready
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

/-- Readiness for the range-distance export surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitRangeDistanceExportsSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitRangeDistanceBoundsSurfaceReady ∧
  concreteL2MathlibFinTwoUnitRangeDistanceExportsAdapter ∧
  concreteL2MathlibFinTwoUnitRangeDistanceExportsSurface.boundaryNotExactFirstSecondDistance ∧
  concreteL2MathlibFinTwoUnitRangeDistanceExportsSurface.boundaryNotFiniteDimensionalTheorem ∧
  concreteL2MathlibFinTwoUnitRangeDistanceExportsSurface.boundaryNotGeneralFiniteFamilyLinearIndependence ∧
  concreteL2MathlibFinTwoUnitRangeDistanceExportsSurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibFinTwoUnitRangeDistanceExportsSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinTwoUnitRangeDistanceExportsSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinTwoUnitRangeDistanceExportsSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinTwoUnitRangeDistanceExportsSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinTwoUnitRangeDistanceExportsSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinTwoUnitRangeDistanceExportsSurface.boundaryNotSpectralAtomTheorem

/-- Readiness theorem for the range-distance export surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_range_distance_exports_surface_ready :
    concreteAnalyticSpineL2MathlibFinTwoUnitRangeDistanceExportsSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinTwoUnitRangeDistanceExportsSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_two_unit_range_distance_bounds_surface_ready <|
      And.intro concrete_l2_mathlib_fin_two_unit_range_distance_exports_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the range-distance export surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitRangeDistanceExportsHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitRangeDistanceExportsSurfaceReady

/-- Boundary theorem for the range-distance export surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_range_distance_exports_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinTwoUnitRangeDistanceExportsHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_two_unit_range_distance_exports_surface_ready

end

end MathlibAnalytic
end MGAP4D
