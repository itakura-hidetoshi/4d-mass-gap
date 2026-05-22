import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinateLinearMaps

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- The reconstructed coordinate-pair map on the two-unit synthesis range,
promoted to a genuine `LinearMap` into `Fin 2 → ℝ`.

This packages the two scalar coordinate linear maps into one vector-valued
coordinate map. -/
def concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap
    {k n : ℕ} (hkn : k ≠ n) :
    concreteL2MathlibFinTwoUnitSynthesisRange k n →ₗ[ℝ] (Fin 2 → ℝ) where
  toFun := fun v => fun i =>
    if i = 0 then
      concreteL2MathlibFinTwoUnitRangeFirstCoordinateLinearMap hkn v
    else
      concreteL2MathlibFinTwoUnitRangeSecondCoordinateLinearMap hkn v
  map_add' := by
    intro v w
    ext i
    by_cases hi : i = 0
    · simp [hi]
    · simp [hi]
  map_smul' := by
    intro a v
    ext i
    by_cases hi : i = 0
    · simp [hi]
    · simp [hi]

/-- The coordinate-pair linear map agrees with the reconstructed coordinate
function. -/
theorem concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_linear_map_apply
    {k n : ℕ} (hkn : k ≠ n)
    (v : concreteL2MathlibFinTwoUnitSynthesisRange k n) :
    concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn v =
      concreteL2MathlibFinTwoUnitRangeCoordinates hkn v := by
  ext i
  by_cases hi : i = 0
  · subst hi
    simp [concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap,
      concreteL2MathlibFinTwoUnitRangeFirstCoordinate,
      concrete_l2_mathlib_fin_two_unit_range_first_coordinate_linear_map_apply]
  · have hi1 : i = 1 := by
      fin_cases i
      · contradiction
      · rfl
    subst hi1
    simp [concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap,
      concreteL2MathlibFinTwoUnitRangeSecondCoordinate,
      concrete_l2_mathlib_fin_two_unit_range_second_coordinate_linear_map_apply]

/-- The coordinate-pair linear map sends the first distinguished range vector to
`(1,0)`. -/
theorem concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_linear_map_first
    {k n : ℕ} (hkn : k ≠ n) :
    concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn
        (concreteL2MathlibFinTwoUnitFirstRangeVector k n) =
      (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) := by
  rw [concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_linear_map_apply]
  exact concrete_l2_mathlib_fin_two_unit_first_range_coordinates_eq hkn

/-- The coordinate-pair linear map sends the second distinguished range vector to
`(0,1)`. -/
theorem concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_linear_map_second
    {k n : ℕ} (hkn : k ≠ n) :
    concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) =
      (fun i : Fin 2 => if i = 1 then (1 : ℝ) else 0) := by
  rw [concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_linear_map_apply]
  exact concrete_l2_mathlib_fin_two_unit_second_range_coordinates_eq hkn

/-- The coordinate-pair linear map re-synthesizes to the original range vector. -/
theorem concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_linear_map_synthesize
    {k n : ℕ} (hkn : k ≠ n)
    (v : concreteL2MathlibFinTwoUnitSynthesisRange k n) :
    concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn
        (concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn v) = v := by
  rw [concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_linear_map_apply]
  exact concrete_l2_mathlib_fin_two_unit_range_coordinates_synthesize hkn v

/-- Adapter predicate for the coordinate-pair `LinearMap` surface. -/
def concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMapAdapter : Prop :=
  ∀ {k n : ℕ} (hkn : k ≠ n),
    (∀ v : concreteL2MathlibFinTwoUnitSynthesisRange k n,
      concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn v =
        concreteL2MathlibFinTwoUnitRangeCoordinates hkn v) ∧
    concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn
        (concreteL2MathlibFinTwoUnitFirstRangeVector k n) =
      (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) ∧
    concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) =
      (fun i : Fin 2 => if i = 1 then (1 : ℝ) else 0)

/-- Adapter theorem for the coordinate-pair `LinearMap` surface. -/
theorem concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_linear_map_adapter_ready :
    concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMapAdapter := by
  intro k n hkn
  exact ⟨
    by intro v; exact concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_linear_map_apply hkn v,
    concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_linear_map_first hkn,
    concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_linear_map_second hkn⟩

/-- Surface promoting the full reconstructed range coordinate map to a genuine
Mathlib `LinearMap` into `Fin 2 → ℝ`.

This is range-local.  It does not assert a basis theorem for the ambient `ℓ²`,
dense span, finite-support-domain equivalence, unbounded operator domain facts,
self-adjointness, PVM construction, or spectral atoms. -/
structure ConcreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMapSurface where
  coordinateLinearMapsReady : concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinateLinearMapsSurfaceReady
  coordinatePairLinearMapAdapter : concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMapAdapter
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

/-- Concrete coordinate-pair `LinearMap` surface. -/
def concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMapSurface :
    ConcreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMapSurface :=
  { coordinateLinearMapsReady :=
      concrete_analytic_spine_l2_mathlib_fin_two_unit_range_coordinate_linear_maps_surface_ready
    coordinatePairLinearMapAdapter :=
      concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_linear_map_adapter_ready
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

/-- Readiness for the coordinate-pair `LinearMap` surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatePairLinearMapSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinateLinearMapsSurfaceReady ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMapAdapter ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMapSurface.boundaryNoAggregateRootTouched ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMapSurface.boundaryNoNewAmbientBasisClaim ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMapSurface.boundaryNotExactFirstSecondDistance ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMapSurface.boundaryNotFiniteDimensionalTheorem ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMapSurface.boundaryNotGeneralFiniteFamilyLinearIndependence ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMapSurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMapSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMapSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMapSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMapSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMapSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMapSurface.boundaryNotSpectralAtomTheorem

/-- Readiness theorem for the coordinate-pair `LinearMap` surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_range_coordinate_pair_linear_map_surface_ready :
    concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatePairLinearMapSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatePairLinearMapSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_two_unit_range_coordinate_linear_maps_surface_ready <|
      And.intro concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_linear_map_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial <| And.intro trivial <|
              And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the coordinate-pair `LinearMap` surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatePairLinearMapHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatePairLinearMapSurfaceReady

/-- Boundary theorem for the coordinate-pair `LinearMap` surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_range_coordinate_pair_linear_map_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatePairLinearMapHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_two_unit_range_coordinate_pair_linear_map_surface_ready

end

end MathlibAnalytic
end MGAP4D
