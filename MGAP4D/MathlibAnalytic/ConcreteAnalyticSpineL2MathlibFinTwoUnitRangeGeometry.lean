import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinTwoUnitRangeMetric

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- The distance between the two distinguished range vectors is nonzero when the
selected indices are distinct. -/
theorem concrete_l2_mathlib_fin_two_unit_range_vectors_dist_ne_zero
    {k n : ℕ} (hkn : k ≠ n) :
    dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ≠ 0 := by
  exact ne_of_gt (concrete_l2_mathlib_fin_two_unit_range_vectors_dist_pos hkn)

/-- The two distinguished range vectors are equal iff the two selected indices
are equal. -/
theorem concrete_l2_mathlib_fin_two_unit_range_vectors_eq_iff
    {k n : ℕ} :
    concreteL2MathlibFinTwoUnitFirstRangeVector k n =
        concreteL2MathlibFinTwoUnitSecondRangeVector k n ↔ k = n := by
  constructor
  · intro hEq
    have hval := congrArg
      (fun v : concreteL2MathlibFinTwoUnitSynthesisRange k n =>
        (v : lp (fun _ : ℕ => ℝ) 2)) hEq
    exact concrete_l2_mathlib_unit_injective hval
  · intro hEq
    subst hEq
    rfl

/-- The two distinguished range vectors are unequal iff the selected indices are
unequal. -/
theorem concrete_l2_mathlib_fin_two_unit_range_vectors_ne_iff
    {k n : ℕ} :
    concreteL2MathlibFinTwoUnitFirstRangeVector k n ≠
        concreteL2MathlibFinTwoUnitSecondRangeVector k n ↔ k ≠ n := by
  constructor
  · intro hne hkn
    exact hne ((concrete_l2_mathlib_fin_two_unit_range_vectors_eq_iff).mpr hkn)
  · intro hkn
    exact concrete_l2_mathlib_fin_two_unit_range_vectors_ne hkn

/-- Positive distance of distinguished range vectors is equivalent to distinct
selected indices. -/
theorem concrete_l2_mathlib_fin_two_unit_range_vectors_dist_pos_iff
    {k n : ℕ} :
    0 < dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ↔ k ≠ n := by
  constructor
  · intro hdist hkn
    have hdist_zero :
        dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
            (concreteL2MathlibFinTwoUnitSecondRangeVector k n) = 0 := by
      rw [(concrete_l2_mathlib_fin_two_unit_range_vectors_eq_iff).mpr hkn]
      simp
    rw [hdist_zero] at hdist
    exact (lt_irrefl (0 : ℝ)) hdist
  · intro hkn
    exact concrete_l2_mathlib_fin_two_unit_range_vectors_dist_pos hkn

/-- Zero distance of distinguished range vectors is equivalent to equal selected
indices. -/
theorem concrete_l2_mathlib_fin_two_unit_range_vectors_dist_eq_zero_iff
    {k n : ℕ} :
    dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) = 0 ↔ k = n := by
  constructor
  · intro hdist
    have hEq : concreteL2MathlibFinTwoUnitFirstRangeVector k n =
        concreteL2MathlibFinTwoUnitSecondRangeVector k n := by
      exact dist_eq_zero.mp hdist
    exact (concrete_l2_mathlib_fin_two_unit_range_vectors_eq_iff).mp hEq
  · intro hkn
    rw [(concrete_l2_mathlib_fin_two_unit_range_vectors_eq_iff).mpr hkn]
    simp

/-- The norm of the difference of the distinguished range vectors is zero iff
the selected indices are equal. -/
theorem concrete_l2_mathlib_fin_two_unit_range_vectors_norm_sub_eq_zero_iff
    {k n : ℕ} :
    ‖concreteL2MathlibFinTwoUnitFirstRangeVector k n -
        concreteL2MathlibFinTwoUnitSecondRangeVector k n‖ = 0 ↔ k = n := by
  constructor
  · intro hnorm
    have hsub : concreteL2MathlibFinTwoUnitFirstRangeVector k n -
        concreteL2MathlibFinTwoUnitSecondRangeVector k n = 0 := by
      exact norm_eq_zero.mp hnorm
    have hEq : concreteL2MathlibFinTwoUnitFirstRangeVector k n =
        concreteL2MathlibFinTwoUnitSecondRangeVector k n := by
      exact sub_eq_zero.mp hsub
    exact (concrete_l2_mathlib_fin_two_unit_range_vectors_eq_iff).mp hEq
  · intro hkn
    rw [(concrete_l2_mathlib_fin_two_unit_range_vectors_eq_iff).mpr hkn]
    simp

/-- Adapter predicate for the two-point geometry of the distinguished vectors
inside the synthesis range. -/
def concreteL2MathlibFinTwoUnitRangeGeometryAdapter : Prop :=
  (∀ {k n : ℕ}, k ≠ n →
    dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
      (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ≠ 0) ∧
  (∀ {k n : ℕ},
    (concreteL2MathlibFinTwoUnitFirstRangeVector k n =
      concreteL2MathlibFinTwoUnitSecondRangeVector k n ↔ k = n)) ∧
  (∀ {k n : ℕ},
    (0 < dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
      (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ↔ k ≠ n))

/-- Adapter theorem for the two-point geometry of the distinguished vectors
inside the synthesis range. -/
theorem concrete_l2_mathlib_fin_two_unit_range_geometry_adapter_ready :
    concreteL2MathlibFinTwoUnitRangeGeometryAdapter := by
  exact ⟨
    by intro k n hkn; exact concrete_l2_mathlib_fin_two_unit_range_vectors_dist_ne_zero hkn,
    by intro k n; exact concrete_l2_mathlib_fin_two_unit_range_vectors_eq_iff,
    by intro k n; exact concrete_l2_mathlib_fin_two_unit_range_vectors_dist_pos_iff⟩

/-- Surface for the two-point geometry of the distinguished vectors inside the
two-unit synthesis range.

This layer packages equality, inequality, zero-distance, and positive-distance
criteria for the two distinguished range vectors.  It remains a two-coordinate
range theorem and does not claim finite dimensionality of the ambient space, a
basis theorem, dense span, finite-support-domain equivalence, or any
operator-theoretic conclusion. -/
structure ConcreteL2MathlibFinTwoUnitRangeGeometrySurface where
  rangeMetricReady : concreteAnalyticSpineL2MathlibFinTwoUnitRangeMetricSurfaceReady
  rangeGeometryAdapter : concreteL2MathlibFinTwoUnitRangeGeometryAdapter
  boundaryNotFiniteDimensionalTheorem : Prop
  boundaryNotGeneralFiniteFamilyLinearIndependence : Prop
  boundaryNotBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop

/-- Concrete two-point range geometry surface. -/
def concreteL2MathlibFinTwoUnitRangeGeometrySurface :
    ConcreteL2MathlibFinTwoUnitRangeGeometrySurface :=
  { rangeMetricReady :=
      concrete_analytic_spine_l2_mathlib_fin_two_unit_range_metric_surface_ready
    rangeGeometryAdapter :=
      concrete_l2_mathlib_fin_two_unit_range_geometry_adapter_ready
    boundaryNotFiniteDimensionalTheorem := True
    boundaryNotGeneralFiniteFamilyLinearIndependence := True
    boundaryNotBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True }

/-- Readiness for the two-unit range geometry surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitRangeGeometrySurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitRangeMetricSurfaceReady ∧
  concreteL2MathlibFinTwoUnitRangeGeometryAdapter ∧
  concreteL2MathlibFinTwoUnitRangeGeometrySurface.boundaryNotFiniteDimensionalTheorem ∧
  concreteL2MathlibFinTwoUnitRangeGeometrySurface.boundaryNotGeneralFiniteFamilyLinearIndependence ∧
  concreteL2MathlibFinTwoUnitRangeGeometrySurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibFinTwoUnitRangeGeometrySurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinTwoUnitRangeGeometrySurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinTwoUnitRangeGeometrySurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinTwoUnitRangeGeometrySurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinTwoUnitRangeGeometrySurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinTwoUnitRangeGeometrySurface.boundaryNotSpectralAtomTheorem

/-- Readiness theorem for the two-unit range geometry surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_range_geometry_surface_ready :
    concreteAnalyticSpineL2MathlibFinTwoUnitRangeGeometrySurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinTwoUnitRangeGeometrySurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_two_unit_range_metric_surface_ready <|
      And.intro concrete_l2_mathlib_fin_two_unit_range_geometry_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the two-unit range geometry surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitRangeGeometryHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitRangeGeometrySurfaceReady

/-- Boundary theorem for the two-unit range geometry surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_range_geometry_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinTwoUnitRangeGeometryHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_two_unit_range_geometry_surface_ready

end

end MathlibAnalytic
end MGAP4D
