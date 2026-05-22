import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinTwoUnitRangeNontrivial

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- The first distinguished range vector has norm one. -/
theorem concrete_l2_mathlib_fin_two_unit_first_range_vector_norm_eq_one
    (k n : ℕ) :
    ‖concreteL2MathlibFinTwoUnitFirstRangeVector k n‖ = 1 := by
  change ‖(concreteL2MathlibFinTwoUnitFirstRangeVector k n :
      lp (fun _ : ℕ => ℝ) 2)‖ = 1
  rw [concrete_l2_mathlib_fin_two_unit_first_range_vector_val]
  exact concrete_l2_unit_transported_mathlib_norm_eq_one k

/-- The second distinguished range vector has norm one. -/
theorem concrete_l2_mathlib_fin_two_unit_second_range_vector_norm_eq_one
    (k n : ℕ) :
    ‖concreteL2MathlibFinTwoUnitSecondRangeVector k n‖ = 1 := by
  change ‖(concreteL2MathlibFinTwoUnitSecondRangeVector k n :
      lp (fun _ : ℕ => ℝ) 2)‖ = 1
  rw [concrete_l2_mathlib_fin_two_unit_second_range_vector_val]
  exact concrete_l2_unit_transported_mathlib_norm_eq_one n

/-- The range-subtype distance between the two distinguished range vectors is the
ambient `ℓ²` distance between the two selected coordinate units. -/
theorem concrete_l2_mathlib_fin_two_unit_range_vectors_dist_eq
    (k n : ℕ) :
    dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) =
      dist (concreteL2MathlibUnit k) (concreteL2MathlibUnit n) := by
  rfl

/-- The two distinguished range vectors are separated by positive metric distance
when the selected indices are distinct. -/
theorem concrete_l2_mathlib_fin_two_unit_range_vectors_dist_pos
    {k n : ℕ} (hkn : k ≠ n) :
    0 < dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) := by
  rw [concrete_l2_mathlib_fin_two_unit_range_vectors_dist_eq]
  exact concrete_l2_mathlib_unit_dist_pos hkn

/-- The range-subtype norm of the difference of the two distinguished range
vectors is positive when the selected indices are distinct. -/
theorem concrete_l2_mathlib_fin_two_unit_range_vectors_norm_sub_pos
    {k n : ℕ} (hkn : k ≠ n) :
    0 < ‖concreteL2MathlibFinTwoUnitFirstRangeVector k n -
        concreteL2MathlibFinTwoUnitSecondRangeVector k n‖ := by
  exact norm_pos_iff.mpr (sub_ne_zero.mpr
    (concrete_l2_mathlib_fin_two_unit_range_vectors_ne hkn))

/-- The norm of the difference of the two distinguished range vectors is nonzero
when the selected indices are distinct. -/
theorem concrete_l2_mathlib_fin_two_unit_range_vectors_norm_sub_ne_zero
    {k n : ℕ} (hkn : k ≠ n) :
    ‖concreteL2MathlibFinTwoUnitFirstRangeVector k n -
        concreteL2MathlibFinTwoUnitSecondRangeVector k n‖ ≠ 0 := by
  exact ne_of_gt (concrete_l2_mathlib_fin_two_unit_range_vectors_norm_sub_pos hkn)

/-- Adapter predicate for the metric data of the two distinguished vectors inside
the synthesis range. -/
def concreteL2MathlibFinTwoUnitRangeMetricAdapter : Prop :=
  (∀ k n : ℕ, ‖concreteL2MathlibFinTwoUnitFirstRangeVector k n‖ = 1) ∧
  (∀ k n : ℕ, ‖concreteL2MathlibFinTwoUnitSecondRangeVector k n‖ = 1) ∧
  (∀ {k n : ℕ}, k ≠ n →
    0 < dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
      (concreteL2MathlibFinTwoUnitSecondRangeVector k n)) ∧
  (∀ {k n : ℕ}, k ≠ n →
    0 < ‖concreteL2MathlibFinTwoUnitFirstRangeVector k n -
      concreteL2MathlibFinTwoUnitSecondRangeVector k n‖)

/-- Adapter theorem for the metric data of the two distinguished vectors inside
the synthesis range. -/
theorem concrete_l2_mathlib_fin_two_unit_range_metric_adapter_ready :
    concreteL2MathlibFinTwoUnitRangeMetricAdapter := by
  exact ⟨
    by intro k n; exact concrete_l2_mathlib_fin_two_unit_first_range_vector_norm_eq_one k n,
    by intro k n; exact concrete_l2_mathlib_fin_two_unit_second_range_vector_norm_eq_one k n,
    by intro k n hkn; exact concrete_l2_mathlib_fin_two_unit_range_vectors_dist_pos hkn,
    by intro k n hkn; exact concrete_l2_mathlib_fin_two_unit_range_vectors_norm_sub_pos hkn⟩

/-- Surface for metric data on the two distinguished vectors inside the two-unit
synthesis range.

This layer lifts the ambient unit norm and pairwise separation facts to the
range subtype: the two distinguished range vectors have norm one and, for
`k ≠ n`, positive distance and positive norm of their difference.  It remains a
two-coordinate range theorem and does not claim finite dimensionality of the
ambient space, a basis theorem, dense span, finite-support-domain equivalence, or
any operator-theoretic conclusion. -/
structure ConcreteL2MathlibFinTwoUnitRangeMetricSurface where
  rangeNontrivialReady : concreteAnalyticSpineL2MathlibFinTwoUnitRangeNontrivialSurfaceReady
  rangeMetricAdapter : concreteL2MathlibFinTwoUnitRangeMetricAdapter
  boundaryNotFiniteDimensionalTheorem : Prop
  boundaryNotGeneralFiniteFamilyLinearIndependence : Prop
  boundaryNotBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop

/-- Concrete metric surface for the two distinguished range vectors. -/
def concreteL2MathlibFinTwoUnitRangeMetricSurface :
    ConcreteL2MathlibFinTwoUnitRangeMetricSurface :=
  { rangeNontrivialReady :=
      concrete_analytic_spine_l2_mathlib_fin_two_unit_range_nontrivial_surface_ready
    rangeMetricAdapter := concrete_l2_mathlib_fin_two_unit_range_metric_adapter_ready
    boundaryNotFiniteDimensionalTheorem := True
    boundaryNotGeneralFiniteFamilyLinearIndependence := True
    boundaryNotBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True }

/-- Readiness for the two-unit range metric surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitRangeMetricSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitRangeNontrivialSurfaceReady ∧
  concreteL2MathlibFinTwoUnitRangeMetricAdapter ∧
  concreteL2MathlibFinTwoUnitRangeMetricSurface.boundaryNotFiniteDimensionalTheorem ∧
  concreteL2MathlibFinTwoUnitRangeMetricSurface.boundaryNotGeneralFiniteFamilyLinearIndependence ∧
  concreteL2MathlibFinTwoUnitRangeMetricSurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibFinTwoUnitRangeMetricSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinTwoUnitRangeMetricSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinTwoUnitRangeMetricSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinTwoUnitRangeMetricSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinTwoUnitRangeMetricSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinTwoUnitRangeMetricSurface.boundaryNotSpectralAtomTheorem

/-- Readiness theorem for the two-unit range metric surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_range_metric_surface_ready :
    concreteAnalyticSpineL2MathlibFinTwoUnitRangeMetricSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinTwoUnitRangeMetricSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_two_unit_range_nontrivial_surface_ready <|
      And.intro concrete_l2_mathlib_fin_two_unit_range_metric_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the two-unit range metric surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitRangeMetricHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitRangeMetricSurfaceReady

/-- Boundary theorem for the two-unit range metric surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_range_metric_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinTwoUnitRangeMetricHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_two_unit_range_metric_surface_ready

end

end MathlibAnalytic
end MGAP4D
