import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinTwoUnitRangeNormExports

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Compact metric witness for the two unit vectors inside the two-unit synthesis
range.

It packages the norm-one facts and the first/second distance interval bound in a
single downstream-friendly theorem. -/
theorem concrete_l2_mathlib_fin_two_unit_range_metric_witness
    (k n : ℕ) :
    ‖concreteL2MathlibFinTwoUnitFirstRangeVector k n‖ = 1 ∧
    ‖concreteL2MathlibFinTwoUnitSecondRangeVector k n‖ = 1 ∧
    dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
      (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ∈ Set.Icc (0 : ℝ) 2 := by
  exact ⟨
    concrete_l2_mathlib_fin_two_unit_first_range_vector_norm_eq_one_export k n,
    concrete_l2_mathlib_fin_two_unit_second_range_vector_norm_eq_one_export k n,
    concrete_l2_mathlib_fin_two_unit_first_second_range_dist_mem_Icc k n⟩

/-- Compact strict metric witness for distinct selected indices. -/
theorem concrete_l2_mathlib_fin_two_unit_range_metric_witness_of_ne
    {k n : ℕ} (hkn : k ≠ n) :
    ‖concreteL2MathlibFinTwoUnitFirstRangeVector k n‖ = 1 ∧
    ‖concreteL2MathlibFinTwoUnitSecondRangeVector k n‖ = 1 ∧
    dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
      (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ∈ Set.Ioc (0 : ℝ) 2 := by
  exact ⟨
    concrete_l2_mathlib_fin_two_unit_first_range_vector_norm_eq_one_export k n,
    concrete_l2_mathlib_fin_two_unit_second_range_vector_norm_eq_one_export k n,
    concrete_l2_mathlib_fin_two_unit_first_second_range_dist_mem_Ioc hkn⟩

/-- Compact three-point metric witness for `0`, `e_k`, and `e_n` in the range. -/
theorem concrete_l2_mathlib_fin_two_unit_range_three_point_metric_witness
    (k n : ℕ) :
    ‖concreteL2MathlibFinTwoUnitZeroRangeVector k n‖ = 0 ∧
    dist (concreteL2MathlibFinTwoUnitZeroRangeVector k n)
      (concreteL2MathlibFinTwoUnitFirstRangeVector k n) = 1 ∧
    dist (concreteL2MathlibFinTwoUnitZeroRangeVector k n)
      (concreteL2MathlibFinTwoUnitSecondRangeVector k n) = 1 ∧
    dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
      (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ≤ 2 := by
  exact ⟨
    concrete_l2_mathlib_fin_two_unit_zero_range_vector_norm_eq_zero k n,
    concrete_l2_mathlib_fin_two_unit_zero_first_range_dist_eq_one k n,
    concrete_l2_mathlib_fin_two_unit_zero_second_range_dist_eq_one k n,
    concrete_l2_mathlib_fin_two_unit_first_second_range_dist_upper_bound k n⟩

/-- Compact strict three-point metric witness for distinct selected indices. -/
theorem concrete_l2_mathlib_fin_two_unit_range_three_point_metric_witness_of_ne
    {k n : ℕ} (hkn : k ≠ n) :
    ‖concreteL2MathlibFinTwoUnitZeroRangeVector k n‖ = 0 ∧
    dist (concreteL2MathlibFinTwoUnitZeroRangeVector k n)
      (concreteL2MathlibFinTwoUnitFirstRangeVector k n) = 1 ∧
    dist (concreteL2MathlibFinTwoUnitZeroRangeVector k n)
      (concreteL2MathlibFinTwoUnitSecondRangeVector k n) = 1 ∧
    0 < dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
      (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ∧
    dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
      (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ≤ 2 := by
  exact ⟨
    concrete_l2_mathlib_fin_two_unit_zero_range_vector_norm_eq_zero k n,
    concrete_l2_mathlib_fin_two_unit_zero_first_range_dist_eq_one k n,
    concrete_l2_mathlib_fin_two_unit_zero_second_range_dist_eq_one k n,
    concrete_l2_mathlib_fin_two_unit_first_second_range_dist_strict_lower_bound hkn,
    concrete_l2_mathlib_fin_two_unit_first_second_range_dist_upper_bound_of_ne hkn⟩

/-- Adapter predicate for compact range metric witnesses. -/
def concreteL2MathlibFinTwoUnitRangeMetricWitnessAdapter : Prop :=
  (∀ k n : ℕ,
    ‖concreteL2MathlibFinTwoUnitFirstRangeVector k n‖ = 1 ∧
    ‖concreteL2MathlibFinTwoUnitSecondRangeVector k n‖ = 1 ∧
    dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
      (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ∈ Set.Icc (0 : ℝ) 2) ∧
  (∀ {k n : ℕ}, k ≠ n →
    ‖concreteL2MathlibFinTwoUnitFirstRangeVector k n‖ = 1 ∧
    ‖concreteL2MathlibFinTwoUnitSecondRangeVector k n‖ = 1 ∧
    dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
      (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ∈ Set.Ioc (0 : ℝ) 2)

/-- Adapter theorem for compact range metric witnesses. -/
theorem concrete_l2_mathlib_fin_two_unit_range_metric_witness_adapter_ready :
    concreteL2MathlibFinTwoUnitRangeMetricWitnessAdapter := by
  exact ⟨
    by intro k n; exact concrete_l2_mathlib_fin_two_unit_range_metric_witness k n,
    by intro k n hkn; exact concrete_l2_mathlib_fin_two_unit_range_metric_witness_of_ne hkn⟩

/-- Surface packaging compact metric witnesses for the two distinguished range
unit vectors and the explicit three-point range configuration.

This layer contains no new geometry; it gathers already proved norm and distance
facts into compact downstream-friendly theorem bundles. -/
structure ConcreteL2MathlibFinTwoUnitRangeMetricWitnessSurface where
  rangeNormExportsReady : concreteAnalyticSpineL2MathlibFinTwoUnitRangeNormExportsSurfaceReady
  rangeMetricWitnessAdapter : concreteL2MathlibFinTwoUnitRangeMetricWitnessAdapter
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

/-- Concrete compact metric-witness surface. -/
def concreteL2MathlibFinTwoUnitRangeMetricWitnessSurface :
    ConcreteL2MathlibFinTwoUnitRangeMetricWitnessSurface :=
  { rangeNormExportsReady :=
      concrete_analytic_spine_l2_mathlib_fin_two_unit_range_norm_exports_surface_ready
    rangeMetricWitnessAdapter :=
      concrete_l2_mathlib_fin_two_unit_range_metric_witness_adapter_ready
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

/-- Readiness for the compact metric-witness surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitRangeMetricWitnessSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitRangeNormExportsSurfaceReady ∧
  concreteL2MathlibFinTwoUnitRangeMetricWitnessAdapter ∧
  concreteL2MathlibFinTwoUnitRangeMetricWitnessSurface.boundaryNotExactFirstSecondDistance ∧
  concreteL2MathlibFinTwoUnitRangeMetricWitnessSurface.boundaryNotFiniteDimensionalTheorem ∧
  concreteL2MathlibFinTwoUnitRangeMetricWitnessSurface.boundaryNotGeneralFiniteFamilyLinearIndependence ∧
  concreteL2MathlibFinTwoUnitRangeMetricWitnessSurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibFinTwoUnitRangeMetricWitnessSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinTwoUnitRangeMetricWitnessSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinTwoUnitRangeMetricWitnessSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinTwoUnitRangeMetricWitnessSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinTwoUnitRangeMetricWitnessSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinTwoUnitRangeMetricWitnessSurface.boundaryNotSpectralAtomTheorem

/-- Readiness theorem for the compact metric-witness surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_range_metric_witness_surface_ready :
    concreteAnalyticSpineL2MathlibFinTwoUnitRangeMetricWitnessSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinTwoUnitRangeMetricWitnessSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_two_unit_range_norm_exports_surface_ready <|
      And.intro concrete_l2_mathlib_fin_two_unit_range_metric_witness_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the compact metric-witness surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitRangeMetricWitnessHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitRangeMetricWitnessSurfaceReady

/-- Boundary theorem for the compact metric-witness surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_range_metric_witness_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinTwoUnitRangeMetricWitnessHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_two_unit_range_metric_witness_surface_ready

end

end MathlibAnalytic
end MGAP4D
