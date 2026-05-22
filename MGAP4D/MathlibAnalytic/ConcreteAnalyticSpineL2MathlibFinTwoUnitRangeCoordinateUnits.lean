import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinates

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- The first selected coordinate unit, viewed as a vector in the two-unit
synthesis range. -/
def concreteL2MathlibFinTwoUnitFirstRangeVector (k n : ℕ) :
    concreteL2MathlibFinTwoUnitSynthesisRange k n :=
  ⟨concreteL2MathlibUnit k,
    concrete_l2_mathlib_fin_two_unit_first_mem_range k n⟩

/-- The second selected coordinate unit, viewed as a vector in the two-unit
synthesis range. -/
def concreteL2MathlibFinTwoUnitSecondRangeVector (k n : ℕ) :
    concreteL2MathlibFinTwoUnitSynthesisRange k n :=
  ⟨concreteL2MathlibUnit n,
    concrete_l2_mathlib_fin_two_unit_second_mem_range k n⟩

/-- The underlying value of the first range vector is the first selected
coordinate unit. -/
theorem concrete_l2_mathlib_fin_two_unit_first_range_vector_val
    (k n : ℕ) :
    (concreteL2MathlibFinTwoUnitFirstRangeVector k n :
        lp (fun _ : ℕ => ℝ) 2) = concreteL2MathlibUnit k := by
  rfl

/-- The underlying value of the second range vector is the second selected
coordinate unit. -/
theorem concrete_l2_mathlib_fin_two_unit_second_range_vector_val
    (k n : ℕ) :
    (concreteL2MathlibFinTwoUnitSecondRangeVector k n :
        lp (fun _ : ℕ => ℝ) 2) = concreteL2MathlibUnit n := by
  rfl

/-- The reconstructed range coordinates of the first selected coordinate unit are
`(1, 0)`. -/
theorem concrete_l2_mathlib_fin_two_unit_first_range_coordinates_eq
    {k n : ℕ} (hkn : k ≠ n) :
    concreteL2MathlibFinTwoUnitRangeCoordinates hkn
        (concreteL2MathlibFinTwoUnitFirstRangeVector k n) =
      (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) := by
  symm
  apply concrete_l2_mathlib_fin_two_unit_range_coordinates_unique hkn
  apply Subtype.ext
  rw [concrete_l2_mathlib_fin_two_unit_synthesis_range_linear_equiv_apply_val]
  rw [concrete_l2_mathlib_fin_two_unit_synthesis_linear_map_apply_eq_sum]
  rw [Fin.sum_univ_two]
  simp [concreteL2MathlibFinTwoUnitFamily, concreteL2MathlibFinTwoUnitFirstRangeVector]

/-- The reconstructed range coordinates of the second selected coordinate unit
are `(0, 1)`. -/
theorem concrete_l2_mathlib_fin_two_unit_second_range_coordinates_eq
    {k n : ℕ} (hkn : k ≠ n) :
    concreteL2MathlibFinTwoUnitRangeCoordinates hkn
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) =
      (fun i : Fin 2 => if i = 1 then (1 : ℝ) else 0) := by
  symm
  apply concrete_l2_mathlib_fin_two_unit_range_coordinates_unique hkn
  apply Subtype.ext
  rw [concrete_l2_mathlib_fin_two_unit_synthesis_range_linear_equiv_apply_val]
  rw [concrete_l2_mathlib_fin_two_unit_synthesis_linear_map_apply_eq_sum]
  rw [Fin.sum_univ_two]
  simp [concreteL2MathlibFinTwoUnitFamily, concreteL2MathlibFinTwoUnitSecondRangeVector]

/-- The first coordinate of the first selected range vector is `1`. -/
theorem concrete_l2_mathlib_fin_two_unit_first_range_first_coordinate_eq_one
    {k n : ℕ} (hkn : k ≠ n) :
    concreteL2MathlibFinTwoUnitRangeFirstCoordinate hkn
        (concreteL2MathlibFinTwoUnitFirstRangeVector k n) = 1 := by
  unfold concreteL2MathlibFinTwoUnitRangeFirstCoordinate
  rw [concrete_l2_mathlib_fin_two_unit_first_range_coordinates_eq hkn]
  simp

/-- The second coordinate of the first selected range vector is `0`. -/
theorem concrete_l2_mathlib_fin_two_unit_first_range_second_coordinate_eq_zero
    {k n : ℕ} (hkn : k ≠ n) :
    concreteL2MathlibFinTwoUnitRangeSecondCoordinate hkn
        (concreteL2MathlibFinTwoUnitFirstRangeVector k n) = 0 := by
  unfold concreteL2MathlibFinTwoUnitRangeSecondCoordinate
  rw [concrete_l2_mathlib_fin_two_unit_first_range_coordinates_eq hkn]
  simp

/-- The first coordinate of the second selected range vector is `0`. -/
theorem concrete_l2_mathlib_fin_two_unit_second_range_first_coordinate_eq_zero
    {k n : ℕ} (hkn : k ≠ n) :
    concreteL2MathlibFinTwoUnitRangeFirstCoordinate hkn
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) = 0 := by
  unfold concreteL2MathlibFinTwoUnitRangeFirstCoordinate
  rw [concrete_l2_mathlib_fin_two_unit_second_range_coordinates_eq hkn]
  simp

/-- The second coordinate of the second selected range vector is `1`. -/
theorem concrete_l2_mathlib_fin_two_unit_second_range_second_coordinate_eq_one
    {k n : ℕ} (hkn : k ≠ n) :
    concreteL2MathlibFinTwoUnitRangeSecondCoordinate hkn
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) = 1 := by
  unfold concreteL2MathlibFinTwoUnitRangeSecondCoordinate
  rw [concrete_l2_mathlib_fin_two_unit_second_range_coordinates_eq hkn]
  simp

/-- Adapter predicate for the two selected coordinate units inside the synthesis
range. -/
def concreteL2MathlibFinTwoUnitRangeCoordinateUnitsAdapter : Prop :=
  ∀ {k n : ℕ} (hkn : k ≠ n),
    concreteL2MathlibFinTwoUnitRangeCoordinates hkn
        (concreteL2MathlibFinTwoUnitFirstRangeVector k n) =
      (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) ∧
    concreteL2MathlibFinTwoUnitRangeCoordinates hkn
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) =
      (fun i : Fin 2 => if i = 1 then (1 : ℝ) else 0)

/-- Adapter theorem for the two selected coordinate units inside the synthesis
range. -/
theorem concrete_l2_mathlib_fin_two_unit_range_coordinate_units_adapter_ready :
    concreteL2MathlibFinTwoUnitRangeCoordinateUnitsAdapter := by
  intro k n hkn
  exact ⟨
    concrete_l2_mathlib_fin_two_unit_first_range_coordinates_eq hkn,
    concrete_l2_mathlib_fin_two_unit_second_range_coordinates_eq hkn⟩

/-- Surface for the coordinate-unit reconstruction theorem inside the two-unit
synthesis range.

This layer proves that the two selected coordinate units have reconstructed
range coordinates `(1,0)` and `(0,1)`, respectively.  It is still a two-coordinate
range-coordinate theorem and does not claim finite dimensionality of the ambient
space, a basis theorem, dense span, finite-support-domain equivalence, or any
operator-theoretic conclusion. -/
structure ConcreteL2MathlibFinTwoUnitRangeCoordinateUnitsSurface where
  rangeCoordinatesReady : concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatesSurfaceReady
  coordinateUnitsAdapter : concreteL2MathlibFinTwoUnitRangeCoordinateUnitsAdapter
  boundaryNotFiniteDimensionalTheorem : Prop
  boundaryNotGeneralFiniteFamilyLinearIndependence : Prop
  boundaryNotBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop

/-- Concrete coordinate-unit reconstruction surface for the two-unit synthesis
range. -/
def concreteL2MathlibFinTwoUnitRangeCoordinateUnitsSurface :
    ConcreteL2MathlibFinTwoUnitRangeCoordinateUnitsSurface :=
  { rangeCoordinatesReady :=
      concrete_analytic_spine_l2_mathlib_fin_two_unit_range_coordinates_surface_ready
    coordinateUnitsAdapter :=
      concrete_l2_mathlib_fin_two_unit_range_coordinate_units_adapter_ready
    boundaryNotFiniteDimensionalTheorem := True
    boundaryNotGeneralFiniteFamilyLinearIndependence := True
    boundaryNotBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True }

/-- Readiness for the two-unit range coordinate-unit reconstruction surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinateUnitsSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatesSurfaceReady ∧
  concreteL2MathlibFinTwoUnitRangeCoordinateUnitsAdapter ∧
  concreteL2MathlibFinTwoUnitRangeCoordinateUnitsSurface.boundaryNotFiniteDimensionalTheorem ∧
  concreteL2MathlibFinTwoUnitRangeCoordinateUnitsSurface.boundaryNotGeneralFiniteFamilyLinearIndependence ∧
  concreteL2MathlibFinTwoUnitRangeCoordinateUnitsSurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibFinTwoUnitRangeCoordinateUnitsSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinTwoUnitRangeCoordinateUnitsSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinTwoUnitRangeCoordinateUnitsSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinTwoUnitRangeCoordinateUnitsSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinTwoUnitRangeCoordinateUnitsSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinTwoUnitRangeCoordinateUnitsSurface.boundaryNotSpectralAtomTheorem

/-- Readiness theorem for the two-unit range coordinate-unit reconstruction
surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_range_coordinate_units_surface_ready :
    concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinateUnitsSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinateUnitsSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_two_unit_range_coordinates_surface_ready <|
      And.intro concrete_l2_mathlib_fin_two_unit_range_coordinate_units_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the two-unit range coordinate-unit reconstruction surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinateUnitsHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinateUnitsSurfaceReady

/-- Boundary theorem for the two-unit range coordinate-unit reconstruction surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_range_coordinate_units_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinateUnitsHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_two_unit_range_coordinate_units_surface_ready

end

end MathlibAnalytic
end MGAP4D
