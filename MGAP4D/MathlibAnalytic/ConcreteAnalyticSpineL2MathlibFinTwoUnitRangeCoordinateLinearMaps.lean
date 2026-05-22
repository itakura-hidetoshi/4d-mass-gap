import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinTwoUnitRangeFacade

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- The first reconstructed coordinate on the two-unit synthesis range, promoted
to a genuine `LinearMap`. -/
def concreteL2MathlibFinTwoUnitRangeFirstCoordinateLinearMap
    {k n : ℕ} (hkn : k ≠ n) :
    concreteL2MathlibFinTwoUnitSynthesisRange k n →ₗ[ℝ] ℝ where
  toFun := concreteL2MathlibFinTwoUnitRangeFirstCoordinate hkn
  map_add' := by
    intro v w
    unfold concreteL2MathlibFinTwoUnitRangeFirstCoordinate
    unfold concreteL2MathlibFinTwoUnitRangeCoordinates
    rw [map_add]
    rfl
  map_smul' := by
    intro a v
    unfold concreteL2MathlibFinTwoUnitRangeFirstCoordinate
    unfold concreteL2MathlibFinTwoUnitRangeCoordinates
    rw [map_smul]
    rfl

/-- The second reconstructed coordinate on the two-unit synthesis range, promoted
to a genuine `LinearMap`. -/
def concreteL2MathlibFinTwoUnitRangeSecondCoordinateLinearMap
    {k n : ℕ} (hkn : k ≠ n) :
    concreteL2MathlibFinTwoUnitSynthesisRange k n →ₗ[ℝ] ℝ where
  toFun := concreteL2MathlibFinTwoUnitRangeSecondCoordinate hkn
  map_add' := by
    intro v w
    unfold concreteL2MathlibFinTwoUnitRangeSecondCoordinate
    unfold concreteL2MathlibFinTwoUnitRangeCoordinates
    rw [map_add]
    rfl
  map_smul' := by
    intro a v
    unfold concreteL2MathlibFinTwoUnitRangeSecondCoordinate
    unfold concreteL2MathlibFinTwoUnitRangeCoordinates
    rw [map_smul]
    rfl

/-- The first coordinate linear map agrees with the previously defined first
coordinate function. -/
theorem concrete_l2_mathlib_fin_two_unit_range_first_coordinate_linear_map_apply
    {k n : ℕ} (hkn : k ≠ n)
    (v : concreteL2MathlibFinTwoUnitSynthesisRange k n) :
    concreteL2MathlibFinTwoUnitRangeFirstCoordinateLinearMap hkn v =
      concreteL2MathlibFinTwoUnitRangeFirstCoordinate hkn v := by
  rfl

/-- The second coordinate linear map agrees with the previously defined second
coordinate function. -/
theorem concrete_l2_mathlib_fin_two_unit_range_second_coordinate_linear_map_apply
    {k n : ℕ} (hkn : k ≠ n)
    (v : concreteL2MathlibFinTwoUnitSynthesisRange k n) :
    concreteL2MathlibFinTwoUnitRangeSecondCoordinateLinearMap hkn v =
      concreteL2MathlibFinTwoUnitRangeSecondCoordinate hkn v := by
  rfl

/-- The first coordinate linear map sends the first distinguished range vector to
`1`. -/
theorem concrete_l2_mathlib_fin_two_unit_range_first_coordinate_linear_map_first
    {k n : ℕ} (hkn : k ≠ n) :
    concreteL2MathlibFinTwoUnitRangeFirstCoordinateLinearMap hkn
        (concreteL2MathlibFinTwoUnitFirstRangeVector k n) = 1 := by
  rw [concrete_l2_mathlib_fin_two_unit_range_first_coordinate_linear_map_apply]
  exact concrete_l2_mathlib_fin_two_unit_first_range_first_coordinate_eq_one hkn

/-- The first coordinate linear map sends the second distinguished range vector to
`0`. -/
theorem concrete_l2_mathlib_fin_two_unit_range_first_coordinate_linear_map_second
    {k n : ℕ} (hkn : k ≠ n) :
    concreteL2MathlibFinTwoUnitRangeFirstCoordinateLinearMap hkn
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) = 0 := by
  rw [concrete_l2_mathlib_fin_two_unit_range_first_coordinate_linear_map_apply]
  exact concrete_l2_mathlib_fin_two_unit_second_range_first_coordinate_eq_zero hkn

/-- The second coordinate linear map sends the first distinguished range vector to
`0`. -/
theorem concrete_l2_mathlib_fin_two_unit_range_second_coordinate_linear_map_first
    {k n : ℕ} (hkn : k ≠ n) :
    concreteL2MathlibFinTwoUnitRangeSecondCoordinateLinearMap hkn
        (concreteL2MathlibFinTwoUnitFirstRangeVector k n) = 0 := by
  rw [concrete_l2_mathlib_fin_two_unit_range_second_coordinate_linear_map_apply]
  exact concrete_l2_mathlib_fin_two_unit_first_range_second_coordinate_eq_zero hkn

/-- The second coordinate linear map sends the second distinguished range vector
to `1`. -/
theorem concrete_l2_mathlib_fin_two_unit_range_second_coordinate_linear_map_second
    {k n : ℕ} (hkn : k ≠ n) :
    concreteL2MathlibFinTwoUnitRangeSecondCoordinateLinearMap hkn
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) = 1 := by
  rw [concrete_l2_mathlib_fin_two_unit_range_second_coordinate_linear_map_apply]
  exact concrete_l2_mathlib_fin_two_unit_second_range_second_coordinate_eq_one hkn

/-- The two coordinate linear maps separate the two distinguished range vectors. -/
theorem concrete_l2_mathlib_fin_two_unit_range_coordinate_linear_maps_separate
    {k n : ℕ} (hkn : k ≠ n) :
    concreteL2MathlibFinTwoUnitRangeFirstCoordinateLinearMap hkn
        (concreteL2MathlibFinTwoUnitFirstRangeVector k n) = 1 ∧
    concreteL2MathlibFinTwoUnitRangeFirstCoordinateLinearMap hkn
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) = 0 ∧
    concreteL2MathlibFinTwoUnitRangeSecondCoordinateLinearMap hkn
        (concreteL2MathlibFinTwoUnitFirstRangeVector k n) = 0 ∧
    concreteL2MathlibFinTwoUnitRangeSecondCoordinateLinearMap hkn
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) = 1 := by
  exact ⟨
    concrete_l2_mathlib_fin_two_unit_range_first_coordinate_linear_map_first hkn,
    concrete_l2_mathlib_fin_two_unit_range_first_coordinate_linear_map_second hkn,
    concrete_l2_mathlib_fin_two_unit_range_second_coordinate_linear_map_first hkn,
    concrete_l2_mathlib_fin_two_unit_range_second_coordinate_linear_map_second hkn⟩

/-- Adapter predicate for the coordinate `LinearMap` surface. -/
def concreteL2MathlibFinTwoUnitRangeCoordinateLinearMapsAdapter : Prop :=
  ∀ {k n : ℕ} (hkn : k ≠ n),
    concreteL2MathlibFinTwoUnitRangeFirstCoordinateLinearMap hkn
        (concreteL2MathlibFinTwoUnitFirstRangeVector k n) = 1 ∧
    concreteL2MathlibFinTwoUnitRangeFirstCoordinateLinearMap hkn
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) = 0 ∧
    concreteL2MathlibFinTwoUnitRangeSecondCoordinateLinearMap hkn
        (concreteL2MathlibFinTwoUnitFirstRangeVector k n) = 0 ∧
    concreteL2MathlibFinTwoUnitRangeSecondCoordinateLinearMap hkn
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) = 1

/-- Adapter theorem for the coordinate `LinearMap` surface. -/
theorem concrete_l2_mathlib_fin_two_unit_range_coordinate_linear_maps_adapter_ready :
    concreteL2MathlibFinTwoUnitRangeCoordinateLinearMapsAdapter := by
  intro k n hkn
  exact concrete_l2_mathlib_fin_two_unit_range_coordinate_linear_maps_separate hkn

/-- Surface promoting reconstructed range coordinates to genuine Mathlib
`LinearMap`s.

This leaf exposes the coordinate functionals as linear maps on the synthesis
range.  It is still a two-coordinate range theorem and does not assert a basis
for the ambient `ℓ²`, dense span, finite-support-domain equivalence, or any
operator-theoretic conclusion. -/
structure ConcreteL2MathlibFinTwoUnitRangeCoordinateLinearMapsSurface where
  rangeFacadeReady : concreteAnalyticSpineL2MathlibFinTwoUnitRangeFacadeSurfaceReady
  coordinateLinearMapsAdapter : concreteL2MathlibFinTwoUnitRangeCoordinateLinearMapsAdapter
  boundaryNoAggregateRootTouched : Prop
  boundaryNoNewAmbientBasisClaim : Prop
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

/-- Concrete coordinate `LinearMap` surface. -/
def concreteL2MathlibFinTwoUnitRangeCoordinateLinearMapsSurface :
    ConcreteL2MathlibFinTwoUnitRangeCoordinateLinearMapsSurface :=
  { rangeFacadeReady :=
      concrete_analytic_spine_l2_mathlib_fin_two_unit_range_facade_surface_ready
    coordinateLinearMapsAdapter :=
      concrete_l2_mathlib_fin_two_unit_range_coordinate_linear_maps_adapter_ready
    boundaryNoAggregateRootTouched := True
    boundaryNoNewAmbientBasisClaim := True
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

/-- Readiness for the coordinate `LinearMap` surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinateLinearMapsSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitRangeFacadeSurfaceReady ∧
  concreteL2MathlibFinTwoUnitRangeCoordinateLinearMapsAdapter ∧
  concreteL2MathlibFinTwoUnitRangeCoordinateLinearMapsSurface.boundaryNoAggregateRootTouched ∧
  concreteL2MathlibFinTwoUnitRangeCoordinateLinearMapsSurface.boundaryNoNewAmbientBasisClaim ∧
  concreteL2MathlibFinTwoUnitRangeCoordinateLinearMapsSurface.boundaryNotExactFirstSecondDistance ∧
  concreteL2MathlibFinTwoUnitRangeCoordinateLinearMapsSurface.boundaryNotFiniteDimensionalTheorem ∧
  concreteL2MathlibFinTwoUnitRangeCoordinateLinearMapsSurface.boundaryNotGeneralFiniteFamilyLinearIndependence ∧
  concreteL2MathlibFinTwoUnitRangeCoordinateLinearMapsSurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibFinTwoUnitRangeCoordinateLinearMapsSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinTwoUnitRangeCoordinateLinearMapsSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinTwoUnitRangeCoordinateLinearMapsSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinTwoUnitRangeCoordinateLinearMapsSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinTwoUnitRangeCoordinateLinearMapsSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinTwoUnitRangeCoordinateLinearMapsSurface.boundaryNotSpectralAtomTheorem

/-- Readiness theorem for the coordinate `LinearMap` surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_range_coordinate_linear_maps_surface_ready :
    concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinateLinearMapsSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinateLinearMapsSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_two_unit_range_facade_surface_ready <|
      And.intro concrete_l2_mathlib_fin_two_unit_range_coordinate_linear_maps_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial <| And.intro trivial <|
              And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the coordinate `LinearMap` surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinateLinearMapsHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinateLinearMapsSurfaceReady

/-- Boundary theorem for the coordinate `LinearMap` surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_range_coordinate_linear_maps_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinateLinearMapsHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_two_unit_range_coordinate_linear_maps_surface_ready

end

end MathlibAnalytic
end MGAP4D
