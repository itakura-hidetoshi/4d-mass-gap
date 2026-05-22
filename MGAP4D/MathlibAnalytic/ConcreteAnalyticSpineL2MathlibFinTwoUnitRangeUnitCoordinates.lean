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

/-- The underlying value of the first range vector is the first selected unit. -/
theorem concrete_l2_mathlib_fin_two_unit_first_range_vector_val
    (k n : ℕ) :
    (concreteL2MathlibFinTwoUnitFirstRangeVector k n :
        lp (fun _ : ℕ => ℝ) 2) = concreteL2MathlibUnit k := by
  rfl

/-- The underlying value of the second range vector is the second selected unit. -/
theorem concrete_l2_mathlib_fin_two_unit_second_range_vector_val
    (k n : ℕ) :
    (concreteL2MathlibFinTwoUnitSecondRangeVector k n :
        lp (fun _ : ℕ => ℝ) 2) = concreteL2MathlibUnit n := by
  rfl

/-- The reconstructed coordinates of the first selected range unit are `(1, 0)`. -/
theorem concrete_l2_mathlib_fin_two_unit_first_range_coordinates
    {k n : ℕ} (hkn : k ≠ n) :
    concreteL2MathlibFinTwoUnitRangeCoordinates hkn
        (concreteL2MathlibFinTwoUnitFirstRangeVector k n) =
      (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) := by
  let c : Fin 2 → ℝ := fun i => if i = 0 then (1 : ℝ) else 0
  have hc :
      concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn c =
        concreteL2MathlibFinTwoUnitFirstRangeVector k n := by
    apply Subtype.ext
    rw [concrete_l2_mathlib_fin_two_unit_synthesis_range_linear_equiv_apply_val]
    rw [concrete_l2_mathlib_fin_two_unit_synthesis_linear_map_apply_eq_sum]
    rw [Fin.sum_univ_two]
    simp [c, concreteL2MathlibFinTwoUnitFamily]
  have huniq :
      c = concreteL2MathlibFinTwoUnitRangeCoordinates hkn
        (concreteL2MathlibFinTwoUnitFirstRangeVector k n) :=
    concrete_l2_mathlib_fin_two_unit_range_coordinates_unique hkn hc
  exact huniq.symm

/-- The reconstructed coordinates of the second selected range unit are `(0, 1)`. -/
theorem concrete_l2_mathlib_fin_two_unit_second_range_coordinates
    {k n : ℕ} (hkn : k ≠ n) :
    concreteL2MathlibFinTwoUnitRangeCoordinates hkn
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) =
      (fun i : Fin 2 => if i = 1 then (1 : ℝ) else 0) := by
  let c : Fin 2 → ℝ := fun i => if i = 1 then (1 : ℝ) else 0
  have hc :
      concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn c =
        concreteL2MathlibFinTwoUnitSecondRangeVector k n := by
    apply Subtype.ext
    rw [concrete_l2_mathlib_fin_two_unit_synthesis_range_linear_equiv_apply_val]
    rw [concrete_l2_mathlib_fin_two_unit_synthesis_linear_map_apply_eq_sum]
    rw [Fin.sum_univ_two]
    simp [c, concreteL2MathlibFinTwoUnitFamily]
  have huniq :
      c = concreteL2MathlibFinTwoUnitRangeCoordinates hkn
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) :=
    concrete_l2_mathlib_fin_two_unit_range_coordinates_unique hkn hc
  exact huniq.symm

/-- The first coordinate of the first selected range unit is `1`. -/
theorem concrete_l2_mathlib_fin_two_unit_first_range_first_coordinate
    {k n : ℕ} (hkn : k ≠ n) :
    concreteL2MathlibFinTwoUnitRangeFirstCoordinate hkn
      (concreteL2MathlibFinTwoUnitFirstRangeVector k n) = 1 := by
  have hcoords := concrete_l2_mathlib_fin_two_unit_first_range_coordinates hkn
  have h0 := congrArg (fun f : Fin 2 → ℝ => f 0) hcoords
  simpa [concreteL2MathlibFinTwoUnitRangeFirstCoordinate] using h0

/-- The second coordinate of the first selected range unit is `0`. -/
theorem concrete_l2_mathlib_fin_two_unit_first_range_second_coordinate
    {k n : ℕ} (hkn : k ≠ n) :
    concreteL2MathlibFinTwoUnitRangeSecondCoordinate hkn
      (concreteL2MathlibFinTwoUnitFirstRangeVector k n) = 0 := by
  have hcoords := concrete_l2_mathlib_fin_two_unit_first_range_coordinates hkn
  have h1 := congrArg (fun f : Fin 2 → ℝ => f 1) hcoords
  simpa [concreteL2MathlibFinTwoUnitRangeSecondCoordinate] using h1

/-- The first coordinate of the second selected range unit is `0`. -/
theorem concrete_l2_mathlib_fin_two_unit_second_range_first_coordinate
    {k n : ℕ} (hkn : k ≠ n) :
    concreteL2MathlibFinTwoUnitRangeFirstCoordinate hkn
      (concreteL2MathlibFinTwoUnitSecondRangeVector k n) = 0 := by
  have hcoords := concrete_l2_mathlib_fin_two_unit_second_range_coordinates hkn
  have h0 := congrArg (fun f : Fin 2 → ℝ => f 0) hcoords
  simpa [concreteL2MathlibFinTwoUnitRangeFirstCoordinate] using h0

/-- The second coordinate of the second selected range unit is `1`. -/
theorem concrete_l2_mathlib_fin_two_unit_second_range_second_coordinate
    {k n : ℕ} (hkn : k ≠ n) :
    concreteL2MathlibFinTwoUnitRangeSecondCoordinate hkn
      (concreteL2MathlibFinTwoUnitSecondRangeVector k n) = 1 := by
  have hcoords := concrete_l2_mathlib_fin_two_unit_second_range_coordinates hkn
  have h1 := congrArg (fun f : Fin 2 → ℝ => f 1) hcoords
  simpa [concreteL2MathlibFinTwoUnitRangeSecondCoordinate] using h1

/-- Adapter predicate for unit-coordinate reconstruction in the two-unit range. -/
def concreteL2MathlibFinTwoUnitRangeUnitCoordinatesAdapter : Prop :=
  ∀ {k n : ℕ} (hkn : k ≠ n),
    concreteL2MathlibFinTwoUnitRangeFirstCoordinate hkn
      (concreteL2MathlibFinTwoUnitFirstRangeVector k n) = 1 ∧
    concreteL2MathlibFinTwoUnitRangeSecondCoordinate hkn
      (concreteL2MathlibFinTwoUnitFirstRangeVector k n) = 0 ∧
    concreteL2MathlibFinTwoUnitRangeFirstCoordinate hkn
      (concreteL2MathlibFinTwoUnitSecondRangeVector k n) = 0 ∧
    concreteL2MathlibFinTwoUnitRangeSecondCoordinate hkn
      (concreteL2MathlibFinTwoUnitSecondRangeVector k n) = 1

/-- Adapter theorem for unit-coordinate reconstruction in the two-unit range. -/
theorem concrete_l2_mathlib_fin_two_unit_range_unit_coordinates_adapter_ready :
    concreteL2MathlibFinTwoUnitRangeUnitCoordinatesAdapter := by
  intro k n hkn
  exact ⟨
    concrete_l2_mathlib_fin_two_unit_first_range_first_coordinate hkn,
    concrete_l2_mathlib_fin_two_unit_first_range_second_coordinate hkn,
    concrete_l2_mathlib_fin_two_unit_second_range_first_coordinate hkn,
    concrete_l2_mathlib_fin_two_unit_second_range_second_coordinate hkn⟩

/-- Surface for unit-coordinate reconstruction on the two-unit synthesis range.

This layer proves that the two selected coordinate units have reconstructed range
coordinates `(1,0)` and `(0,1)`.  It remains a concrete two-unit range-coordinate
surface and does not claim a general basis theorem, finite-dimensionality of the
ambient space, dense span, or any operator-theoretic conclusion. -/
structure ConcreteL2MathlibFinTwoUnitRangeUnitCoordinatesSurface where
  rangeCoordinatesReady : concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatesSurfaceReady
  unitCoordinatesAdapter : concreteL2MathlibFinTwoUnitRangeUnitCoordinatesAdapter
  boundaryNotFiniteDimensionalTheorem : Prop
  boundaryNotGeneralFiniteFamilyLinearIndependence : Prop
  boundaryNotBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop

/-- Concrete unit-coordinate-reconstruction surface for the two-unit synthesis range. -/
def concreteL2MathlibFinTwoUnitRangeUnitCoordinatesSurface :
    ConcreteL2MathlibFinTwoUnitRangeUnitCoordinatesSurface :=
  { rangeCoordinatesReady :=
      concrete_analytic_spine_l2_mathlib_fin_two_unit_range_coordinates_surface_ready
    unitCoordinatesAdapter :=
      concrete_l2_mathlib_fin_two_unit_range_unit_coordinates_adapter_ready
    boundaryNotFiniteDimensionalTheorem := True
    boundaryNotGeneralFiniteFamilyLinearIndependence := True
    boundaryNotBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True }

/-- Readiness for the two-unit range unit-coordinate-reconstruction surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitRangeUnitCoordinatesSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatesSurfaceReady ∧
  concreteL2MathlibFinTwoUnitRangeUnitCoordinatesAdapter ∧
  concreteL2MathlibFinTwoUnitRangeUnitCoordinatesSurface.boundaryNotFiniteDimensionalTheorem ∧
  concreteL2MathlibFinTwoUnitRangeUnitCoordinatesSurface.boundaryNotGeneralFiniteFamilyLinearIndependence ∧
  concreteL2MathlibFinTwoUnitRangeUnitCoordinatesSurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibFinTwoUnitRangeUnitCoordinatesSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinTwoUnitRangeUnitCoordinatesSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinTwoUnitRangeUnitCoordinatesSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinTwoUnitRangeUnitCoordinatesSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinTwoUnitRangeUnitCoordinatesSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinTwoUnitRangeUnitCoordinatesSurface.boundaryNotSpectralAtomTheorem

/-- Readiness theorem for the two-unit range unit-coordinate-reconstruction surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_range_unit_coordinates_surface_ready :
    concreteAnalyticSpineL2MathlibFinTwoUnitRangeUnitCoordinatesSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinTwoUnitRangeUnitCoordinatesSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_two_unit_range_coordinates_surface_ready <|
      And.intro concrete_l2_mathlib_fin_two_unit_range_unit_coordinates_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the two-unit range unit-coordinate-reconstruction surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitRangeUnitCoordinatesHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitRangeUnitCoordinatesSurfaceReady

/-- Boundary theorem for the two-unit range unit-coordinate-reconstruction surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_range_unit_coordinates_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinTwoUnitRangeUnitCoordinatesHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_two_unit_range_unit_coordinates_surface_ready

end

end MathlibAnalytic
end MGAP4D
