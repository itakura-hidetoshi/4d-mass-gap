import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinTwoUnitRangeNontrivialInstance

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- The zero vector in the two-unit synthesis range. -/
def concreteL2MathlibFinTwoUnitZeroRangeVector (k n : ℕ) :
    concreteL2MathlibFinTwoUnitSynthesisRange k n :=
  0

/-- The zero range vector has zero underlying value. -/
theorem concrete_l2_mathlib_fin_two_unit_zero_range_vector_val
    (k n : ℕ) :
    (concreteL2MathlibFinTwoUnitZeroRangeVector k n :
        lp (fun _ : ℕ => ℝ) 2) = 0 := by
  rfl

/-- The zero range vector is distinct from the first distinguished range vector. -/
theorem concrete_l2_mathlib_fin_two_unit_zero_range_vector_ne_first
    (k n : ℕ) :
    concreteL2MathlibFinTwoUnitZeroRangeVector k n ≠
      concreteL2MathlibFinTwoUnitFirstRangeVector k n := by
  intro hEq
  exact concrete_l2_mathlib_fin_two_unit_first_range_vector_ne_zero k n hEq.symm

/-- The zero range vector is distinct from the second distinguished range vector. -/
theorem concrete_l2_mathlib_fin_two_unit_zero_range_vector_ne_second
    (k n : ℕ) :
    concreteL2MathlibFinTwoUnitZeroRangeVector k n ≠
      concreteL2MathlibFinTwoUnitSecondRangeVector k n := by
  intro hEq
  exact concrete_l2_mathlib_fin_two_unit_second_range_vector_ne_zero k n hEq.symm

/-- The first distinguished range vector is distinct from zero. -/
theorem concrete_l2_mathlib_fin_two_unit_first_range_vector_ne_zero_range
    (k n : ℕ) :
    concreteL2MathlibFinTwoUnitFirstRangeVector k n ≠
      concreteL2MathlibFinTwoUnitZeroRangeVector k n := by
  intro hEq
  exact concrete_l2_mathlib_fin_two_unit_zero_range_vector_ne_first k n hEq.symm

/-- The second distinguished range vector is distinct from zero. -/
theorem concrete_l2_mathlib_fin_two_unit_second_range_vector_ne_zero_range
    (k n : ℕ) :
    concreteL2MathlibFinTwoUnitSecondRangeVector k n ≠
      concreteL2MathlibFinTwoUnitZeroRangeVector k n := by
  intro hEq
  exact concrete_l2_mathlib_fin_two_unit_zero_range_vector_ne_second k n hEq.symm

/-- For distinct selected indices, the three range vectors `0`, `e_k`, and `e_n`
are pairwise distinct. -/
theorem concrete_l2_mathlib_fin_two_unit_range_three_points_pairwise
    {k n : ℕ} (hkn : k ≠ n) :
    concreteL2MathlibFinTwoUnitZeroRangeVector k n ≠
      concreteL2MathlibFinTwoUnitFirstRangeVector k n ∧
    concreteL2MathlibFinTwoUnitZeroRangeVector k n ≠
      concreteL2MathlibFinTwoUnitSecondRangeVector k n ∧
    concreteL2MathlibFinTwoUnitFirstRangeVector k n ≠
      concreteL2MathlibFinTwoUnitSecondRangeVector k n := by
  exact ⟨
    concrete_l2_mathlib_fin_two_unit_zero_range_vector_ne_first k n,
    concrete_l2_mathlib_fin_two_unit_zero_range_vector_ne_second k n,
    concrete_l2_mathlib_fin_two_unit_range_vectors_ne hkn⟩

/-- For distinct selected indices, the two-unit synthesis range has three
explicit pairwise distinct witnesses. -/
theorem concrete_l2_mathlib_fin_two_unit_range_has_three_distinct_vectors
    {k n : ℕ} (hkn : k ≠ n) :
    ∃ z v w : concreteL2MathlibFinTwoUnitSynthesisRange k n,
      z ≠ v ∧ z ≠ w ∧ v ≠ w := by
  exact ⟨
    concreteL2MathlibFinTwoUnitZeroRangeVector k n,
    concreteL2MathlibFinTwoUnitFirstRangeVector k n,
    concreteL2MathlibFinTwoUnitSecondRangeVector k n,
    concrete_l2_mathlib_fin_two_unit_range_three_points_pairwise hkn⟩

/-- Adapter predicate for the three-point witness surface of the two-unit
synthesis range. -/
def concreteL2MathlibFinTwoUnitRangeThreePointAdapter : Prop :=
  (∀ k n : ℕ,
    concreteL2MathlibFinTwoUnitZeroRangeVector k n ≠
      concreteL2MathlibFinTwoUnitFirstRangeVector k n) ∧
  (∀ k n : ℕ,
    concreteL2MathlibFinTwoUnitZeroRangeVector k n ≠
      concreteL2MathlibFinTwoUnitSecondRangeVector k n) ∧
  (∀ {k n : ℕ}, k ≠ n →
    ∃ z v w : concreteL2MathlibFinTwoUnitSynthesisRange k n,
      z ≠ v ∧ z ≠ w ∧ v ≠ w)

/-- Adapter theorem for the three-point witness surface of the two-unit synthesis
range. -/
theorem concrete_l2_mathlib_fin_two_unit_range_three_point_adapter_ready :
    concreteL2MathlibFinTwoUnitRangeThreePointAdapter := by
  exact ⟨
    by intro k n; exact concrete_l2_mathlib_fin_two_unit_zero_range_vector_ne_first k n,
    by intro k n; exact concrete_l2_mathlib_fin_two_unit_zero_range_vector_ne_second k n,
    by intro k n hkn; exact concrete_l2_mathlib_fin_two_unit_range_has_three_distinct_vectors hkn⟩

/-- Surface for three explicit witnesses in the two-unit synthesis range.

This layer records the concrete range-level points `0`, `e_k`, and `e_n`; for
`k ≠ n` they are pairwise distinct.  It remains a small finite-witness theorem
and does not claim finite dimensionality of the ambient space, a basis theorem,
dense span, finite-support-domain equivalence, or any operator-theoretic
conclusion. -/
structure ConcreteL2MathlibFinTwoUnitRangeThreePointSurface where
  rangeNontrivialInstanceReady : concreteAnalyticSpineL2MathlibFinTwoUnitRangeNontrivialInstanceSurfaceReady
  rangeThreePointAdapter : concreteL2MathlibFinTwoUnitRangeThreePointAdapter
  boundaryNotFiniteDimensionalTheorem : Prop
  boundaryNotGeneralFiniteFamilyLinearIndependence : Prop
  boundaryNotBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop

/-- Concrete three-point witness surface for the two-unit synthesis range. -/
def concreteL2MathlibFinTwoUnitRangeThreePointSurface :
    ConcreteL2MathlibFinTwoUnitRangeThreePointSurface :=
  { rangeNontrivialInstanceReady :=
      concrete_analytic_spine_l2_mathlib_fin_two_unit_range_nontrivial_instance_surface_ready
    rangeThreePointAdapter := concrete_l2_mathlib_fin_two_unit_range_three_point_adapter_ready
    boundaryNotFiniteDimensionalTheorem := True
    boundaryNotGeneralFiniteFamilyLinearIndependence := True
    boundaryNotBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True }

/-- Readiness for the three-point witness surface of the two-unit synthesis range. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitRangeThreePointSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitRangeNontrivialInstanceSurfaceReady ∧
  concreteL2MathlibFinTwoUnitRangeThreePointAdapter ∧
  concreteL2MathlibFinTwoUnitRangeThreePointSurface.boundaryNotFiniteDimensionalTheorem ∧
  concreteL2MathlibFinTwoUnitRangeThreePointSurface.boundaryNotGeneralFiniteFamilyLinearIndependence ∧
  concreteL2MathlibFinTwoUnitRangeThreePointSurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibFinTwoUnitRangeThreePointSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinTwoUnitRangeThreePointSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinTwoUnitRangeThreePointSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinTwoUnitRangeThreePointSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinTwoUnitRangeThreePointSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinTwoUnitRangeThreePointSurface.boundaryNotSpectralAtomTheorem

/-- Readiness theorem for the three-point witness surface of the two-unit synthesis
range. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_range_three_point_surface_ready :
    concreteAnalyticSpineL2MathlibFinTwoUnitRangeThreePointSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinTwoUnitRangeThreePointSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_two_unit_range_nontrivial_instance_surface_ready <|
      And.intro concrete_l2_mathlib_fin_two_unit_range_three_point_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the three-point witness surface of the two-unit synthesis
range. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitRangeThreePointHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitRangeThreePointSurfaceReady

/-- Boundary theorem for the three-point witness surface of the two-unit synthesis
range. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_range_three_point_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinTwoUnitRangeThreePointHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_two_unit_range_three_point_surface_ready

end

end MathlibAnalytic
end MGAP4D
