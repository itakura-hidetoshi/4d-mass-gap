import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinTwoUnitRangeDistanceExports

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Exported zero-distance criterion for the first/second range vectors. -/
theorem concrete_l2_mathlib_fin_two_unit_first_second_range_dist_eq_zero_iff_indices_eq
    {k n : ℕ} :
    dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) = 0 ↔ k = n :=
  concrete_l2_mathlib_fin_two_unit_range_vectors_dist_eq_zero_iff

/-- Exported nonzero-distance criterion for the first/second range vectors. -/
theorem concrete_l2_mathlib_fin_two_unit_first_second_range_dist_ne_zero_iff_indices_ne
    {k n : ℕ} :
    dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ≠ 0 ↔ k ≠ n := by
  constructor
  · intro hdist hkn
    exact hdist
      ((concrete_l2_mathlib_fin_two_unit_first_second_range_dist_eq_zero_iff_indices_eq).mpr hkn)
  · intro hkn
    exact concrete_l2_mathlib_fin_two_unit_first_second_range_dist_ne_zero_of_ne hkn

/-- Exported positive-distance criterion for the first/second range vectors. -/
theorem concrete_l2_mathlib_fin_two_unit_first_second_range_dist_pos_iff_indices_ne
    {k n : ℕ} :
    0 < dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ↔ k ≠ n :=
  concrete_l2_mathlib_fin_two_unit_range_vectors_dist_pos_iff

/-- Exported equality criterion for the first/second range vectors. -/
theorem concrete_l2_mathlib_fin_two_unit_first_second_range_vectors_eq_iff_indices_eq
    {k n : ℕ} :
    concreteL2MathlibFinTwoUnitFirstRangeVector k n =
        concreteL2MathlibFinTwoUnitSecondRangeVector k n ↔ k = n :=
  concrete_l2_mathlib_fin_two_unit_range_vectors_eq_iff

/-- Exported inequality criterion for the first/second range vectors. -/
theorem concrete_l2_mathlib_fin_two_unit_first_second_range_vectors_ne_iff_indices_ne
    {k n : ℕ} :
    concreteL2MathlibFinTwoUnitFirstRangeVector k n ≠
        concreteL2MathlibFinTwoUnitSecondRangeVector k n ↔ k ≠ n :=
  concrete_l2_mathlib_fin_two_unit_range_vectors_ne_iff

/-- Exported equivalence: zero distance iff equal range vectors. -/
theorem concrete_l2_mathlib_fin_two_unit_first_second_range_dist_eq_zero_iff_vectors_eq
    {k n : ℕ} :
    dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) = 0 ↔
      concreteL2MathlibFinTwoUnitFirstRangeVector k n =
        concreteL2MathlibFinTwoUnitSecondRangeVector k n := by
  exact dist_eq_zero

/-- Exported equivalence: nonzero distance iff unequal range vectors. -/
theorem concrete_l2_mathlib_fin_two_unit_first_second_range_dist_ne_zero_iff_vectors_ne
    {k n : ℕ} :
    dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ≠ 0 ↔
      concreteL2MathlibFinTwoUnitFirstRangeVector k n ≠
        concreteL2MathlibFinTwoUnitSecondRangeVector k n := by
  constructor
  · intro hdist hEq
    exact hdist (dist_eq_zero.mpr hEq)
  · intro hne hdist
    exact hne (dist_eq_zero.mp hdist)

/-- Adapter predicate for exported iff facts about first/second range-vector
distance. -/
def concreteL2MathlibFinTwoUnitRangeDistanceIffExportsAdapter : Prop :=
  (∀ {k n : ℕ},
    (dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
      (concreteL2MathlibFinTwoUnitSecondRangeVector k n) = 0 ↔ k = n)) ∧
  (∀ {k n : ℕ},
    (dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
      (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ≠ 0 ↔ k ≠ n)) ∧
  (∀ {k n : ℕ},
    (0 < dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
      (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ↔ k ≠ n))

/-- Adapter theorem for exported iff facts about first/second range-vector
distance. -/
theorem concrete_l2_mathlib_fin_two_unit_range_distance_iff_exports_adapter_ready :
    concreteL2MathlibFinTwoUnitRangeDistanceIffExportsAdapter := by
  exact ⟨
    by intro k n; exact concrete_l2_mathlib_fin_two_unit_first_second_range_dist_eq_zero_iff_indices_eq,
    by intro k n; exact concrete_l2_mathlib_fin_two_unit_first_second_range_dist_ne_zero_iff_indices_ne,
    by intro k n; exact concrete_l2_mathlib_fin_two_unit_first_second_range_dist_pos_iff_indices_ne⟩

/-- Surface exporting reusable iff facts about the first/second range distance.

This layer contains no new geometry; it only exposes zero/nonzero/positive
distance criteria in names convenient for downstream imports. -/
structure ConcreteL2MathlibFinTwoUnitRangeDistanceIffExportsSurface where
  rangeDistanceExportsReady : concreteAnalyticSpineL2MathlibFinTwoUnitRangeDistanceExportsSurfaceReady
  rangeDistanceIffExportsAdapter : concreteL2MathlibFinTwoUnitRangeDistanceIffExportsAdapter
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

/-- Concrete range-distance iff export surface. -/
def concreteL2MathlibFinTwoUnitRangeDistanceIffExportsSurface :
    ConcreteL2MathlibFinTwoUnitRangeDistanceIffExportsSurface :=
  { rangeDistanceExportsReady :=
      concrete_analytic_spine_l2_mathlib_fin_two_unit_range_distance_exports_surface_ready
    rangeDistanceIffExportsAdapter :=
      concrete_l2_mathlib_fin_two_unit_range_distance_iff_exports_adapter_ready
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

/-- Readiness for the range-distance iff export surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitRangeDistanceIffExportsSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitRangeDistanceExportsSurfaceReady ∧
  concreteL2MathlibFinTwoUnitRangeDistanceIffExportsAdapter ∧
  concreteL2MathlibFinTwoUnitRangeDistanceIffExportsSurface.boundaryNotExactFirstSecondDistance ∧
  concreteL2MathlibFinTwoUnitRangeDistanceIffExportsSurface.boundaryNotFiniteDimensionalTheorem ∧
  concreteL2MathlibFinTwoUnitRangeDistanceIffExportsSurface.boundaryNotGeneralFiniteFamilyLinearIndependence ∧
  concreteL2MathlibFinTwoUnitRangeDistanceIffExportsSurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibFinTwoUnitRangeDistanceIffExportsSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinTwoUnitRangeDistanceIffExportsSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinTwoUnitRangeDistanceIffExportsSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinTwoUnitRangeDistanceIffExportsSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinTwoUnitRangeDistanceIffExportsSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinTwoUnitRangeDistanceIffExportsSurface.boundaryNotSpectralAtomTheorem

/-- Readiness theorem for the range-distance iff export surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_range_distance_iff_exports_surface_ready :
    concreteAnalyticSpineL2MathlibFinTwoUnitRangeDistanceIffExportsSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinTwoUnitRangeDistanceIffExportsSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_two_unit_range_distance_exports_surface_ready <|
      And.intro concrete_l2_mathlib_fin_two_unit_range_distance_iff_exports_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the range-distance iff export surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitRangeDistanceIffExportsHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitRangeDistanceIffExportsSurfaceReady

/-- Boundary theorem for the range-distance iff export surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_range_distance_iff_exports_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinTwoUnitRangeDistanceIffExportsHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_two_unit_range_distance_iff_exports_surface_ready

end

end MathlibAnalytic
end MGAP4D
