import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinThreeUnitSynthesisRangeEquiv

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Coordinate reconstruction on the three-unit synthesis range.

For a vector in the range of the three-unit synthesis map, its coordinates are
the inverse image under the range `LinearEquiv`. -/
def concreteL2MathlibFinThreeUnitRangeCoordinates
    {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (v : concreteL2MathlibFinThreeUnitSynthesisRange a b c) : Fin 3 → ℝ :=
  (concreteL2MathlibFinThreeUnitSynthesisRangeLinearEquiv hab hac hbc).symm v

/-- The first reconstructed coefficient of a vector in the three-unit synthesis range. -/
def concreteL2MathlibFinThreeUnitRangeFirstCoordinate
    {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (v : concreteL2MathlibFinThreeUnitSynthesisRange a b c) : ℝ :=
  concreteL2MathlibFinThreeUnitRangeCoordinates hab hac hbc v 0

/-- The second reconstructed coefficient of a vector in the three-unit synthesis range. -/
def concreteL2MathlibFinThreeUnitRangeSecondCoordinate
    {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (v : concreteL2MathlibFinThreeUnitSynthesisRange a b c) : ℝ :=
  concreteL2MathlibFinThreeUnitRangeCoordinates hab hac hbc v 1

/-- The third reconstructed coefficient of a vector in the three-unit synthesis range. -/
def concreteL2MathlibFinThreeUnitRangeThirdCoordinate
    {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (v : concreteL2MathlibFinThreeUnitSynthesisRange a b c) : ℝ :=
  concreteL2MathlibFinThreeUnitRangeCoordinates hab hac hbc v 2

/-- Re-synthesizing the reconstructed coordinates gives back the range vector. -/
theorem concrete_l2_mathlib_fin_three_unit_range_coordinates_synthesize
    {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (v : concreteL2MathlibFinThreeUnitSynthesisRange a b c) :
    concreteL2MathlibFinThreeUnitSynthesisRangeLinearEquiv hab hac hbc
        (concreteL2MathlibFinThreeUnitRangeCoordinates hab hac hbc v) = v := by
  unfold concreteL2MathlibFinThreeUnitRangeCoordinates
  exact (concreteL2MathlibFinThreeUnitSynthesisRangeLinearEquiv hab hac hbc).apply_symm_apply v

/-- Underlying-value form of coordinate reconstruction. -/
theorem concrete_l2_mathlib_fin_three_unit_range_coordinates_synthesize_val
    {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (v : concreteL2MathlibFinThreeUnitSynthesisRange a b c) :
    ((concreteL2MathlibFinThreeUnitSynthesisRangeLinearEquiv hab hac hbc
        (concreteL2MathlibFinThreeUnitRangeCoordinates hab hac hbc v)) :
        lp (fun _ : ℕ => ℝ) 2) = (v : lp (fun _ : ℕ => ℝ) 2) := by
  exact congrArg
    (fun w : concreteL2MathlibFinThreeUnitSynthesisRange a b c =>
      (w : lp (fun _ : ℕ => ℝ) 2))
    (concrete_l2_mathlib_fin_three_unit_range_coordinates_synthesize hab hac hbc v)

/-- Any coefficient vector synthesizing to a range vector equals the reconstructed
coordinate vector. -/
theorem concrete_l2_mathlib_fin_three_unit_range_coordinates_unique
    {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {v : concreteL2MathlibFinThreeUnitSynthesisRange a b c} {r : Fin 3 → ℝ}
    (hr : concreteL2MathlibFinThreeUnitSynthesisRangeLinearEquiv hab hac hbc r = v) :
    r = concreteL2MathlibFinThreeUnitRangeCoordinates hab hac hbc v := by
  exact concrete_l2_mathlib_fin_three_unit_synthesis_range_linear_equiv_inverse_unique hab hac hbc hr

/-- Equality with the reconstructed coordinates is equivalent to synthesizing to
the target range vector. -/
theorem concrete_l2_mathlib_fin_three_unit_range_coordinates_eq_iff
    {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {v : concreteL2MathlibFinThreeUnitSynthesisRange a b c} {r : Fin 3 → ℝ} :
    r = concreteL2MathlibFinThreeUnitRangeCoordinates hab hac hbc v ↔
      concreteL2MathlibFinThreeUnitSynthesisRangeLinearEquiv hab hac hbc r = v := by
  constructor
  · intro hr
    rw [hr]
    exact concrete_l2_mathlib_fin_three_unit_range_coordinates_synthesize hab hac hbc v
  · intro hr
    exact concrete_l2_mathlib_fin_three_unit_range_coordinates_unique hab hac hbc hr

/-- The first coefficient of any synthesis witness is the reconstructed first
coordinate. -/
theorem concrete_l2_mathlib_fin_three_unit_range_first_coordinate_unique
    {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {v : concreteL2MathlibFinThreeUnitSynthesisRange a b c} {r : Fin 3 → ℝ}
    (hr : concreteL2MathlibFinThreeUnitSynthesisRangeLinearEquiv hab hac hbc r = v) :
    r 0 = concreteL2MathlibFinThreeUnitRangeFirstCoordinate hab hac hbc v := by
  have hcoord : r = concreteL2MathlibFinThreeUnitRangeCoordinates hab hac hbc v :=
    concrete_l2_mathlib_fin_three_unit_range_coordinates_unique hab hac hbc hr
  exact congrArg (fun f : Fin 3 → ℝ => f 0) hcoord

/-- The second coefficient of any synthesis witness is the reconstructed second
coordinate. -/
theorem concrete_l2_mathlib_fin_three_unit_range_second_coordinate_unique
    {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {v : concreteL2MathlibFinThreeUnitSynthesisRange a b c} {r : Fin 3 → ℝ}
    (hr : concreteL2MathlibFinThreeUnitSynthesisRangeLinearEquiv hab hac hbc r = v) :
    r 1 = concreteL2MathlibFinThreeUnitRangeSecondCoordinate hab hac hbc v := by
  have hcoord : r = concreteL2MathlibFinThreeUnitRangeCoordinates hab hac hbc v :=
    concrete_l2_mathlib_fin_three_unit_range_coordinates_unique hab hac hbc hr
  exact congrArg (fun f : Fin 3 → ℝ => f 1) hcoord

/-- The third coefficient of any synthesis witness is the reconstructed third
coordinate. -/
theorem concrete_l2_mathlib_fin_three_unit_range_third_coordinate_unique
    {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    {v : concreteL2MathlibFinThreeUnitSynthesisRange a b c} {r : Fin 3 → ℝ}
    (hr : concreteL2MathlibFinThreeUnitSynthesisRangeLinearEquiv hab hac hbc r = v) :
    r 2 = concreteL2MathlibFinThreeUnitRangeThirdCoordinate hab hac hbc v := by
  have hcoord : r = concreteL2MathlibFinThreeUnitRangeCoordinates hab hac hbc v :=
    concrete_l2_mathlib_fin_three_unit_range_coordinates_unique hab hac hbc hr
  exact congrArg (fun f : Fin 3 → ℝ => f 2) hcoord

/-- Adapter predicate for the three-unit range coordinate-reconstruction layer. -/
def concreteL2MathlibFinThreeUnitRangeCoordinatesAdapter : Prop :=
  ∀ {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c),
    (∀ v : concreteL2MathlibFinThreeUnitSynthesisRange a b c,
      concreteL2MathlibFinThreeUnitSynthesisRangeLinearEquiv hab hac hbc
        (concreteL2MathlibFinThreeUnitRangeCoordinates hab hac hbc v) = v) ∧
    (∀ {v : concreteL2MathlibFinThreeUnitSynthesisRange a b c} {r : Fin 3 → ℝ},
      concreteL2MathlibFinThreeUnitSynthesisRangeLinearEquiv hab hac hbc r = v →
        r = concreteL2MathlibFinThreeUnitRangeCoordinates hab hac hbc v)

/-- Adapter theorem for the three-unit range coordinate-reconstruction layer. -/
theorem concrete_l2_mathlib_fin_three_unit_range_coordinates_adapter_ready :
    concreteL2MathlibFinThreeUnitRangeCoordinatesAdapter := by
  intro a b c hab hac hbc
  exact ⟨
    by intro v; exact concrete_l2_mathlib_fin_three_unit_range_coordinates_synthesize hab hac hbc v,
    by intro v r hr; exact concrete_l2_mathlib_fin_three_unit_range_coordinates_unique hab hac hbc hr⟩

/-- Surface for coordinate reconstruction on the three-unit synthesis range.

This layer turns the range `LinearEquiv` into explicit first/second/third
coefficient reconstruction for vectors in the range. -/
structure ConcreteL2MathlibFinThreeUnitRangeCoordinatesSurface where
  rangeLinearEquivReady : concreteAnalyticSpineL2MathlibFinThreeUnitSynthesisRangeLinearEquivSurfaceReady
  rangeCoordinatesAdapter : concreteL2MathlibFinThreeUnitRangeCoordinatesAdapter
  boundaryNotFiniteDimensionalTheorem : Prop
  boundaryNotGeneralFiniteFamilyLinearIndependence : Prop
  boundaryNotBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop

/-- Concrete coordinate-reconstruction surface for the three-unit synthesis range. -/
def concreteL2MathlibFinThreeUnitRangeCoordinatesSurface :
    ConcreteL2MathlibFinThreeUnitRangeCoordinatesSurface :=
  { rangeLinearEquivReady :=
      concrete_analytic_spine_l2_mathlib_fin_three_unit_synthesis_range_linear_equiv_surface_ready
    rangeCoordinatesAdapter := concrete_l2_mathlib_fin_three_unit_range_coordinates_adapter_ready
    boundaryNotFiniteDimensionalTheorem := True
    boundaryNotGeneralFiniteFamilyLinearIndependence := True
    boundaryNotBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True }

/-- Readiness for the three-unit range coordinate-reconstruction surface. -/
def concreteAnalyticSpineL2MathlibFinThreeUnitRangeCoordinatesSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinThreeUnitSynthesisRangeLinearEquivSurfaceReady ∧
  concreteL2MathlibFinThreeUnitRangeCoordinatesAdapter ∧
  concreteL2MathlibFinThreeUnitRangeCoordinatesSurface.boundaryNotFiniteDimensionalTheorem ∧
  concreteL2MathlibFinThreeUnitRangeCoordinatesSurface.boundaryNotGeneralFiniteFamilyLinearIndependence ∧
  concreteL2MathlibFinThreeUnitRangeCoordinatesSurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibFinThreeUnitRangeCoordinatesSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinThreeUnitRangeCoordinatesSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinThreeUnitRangeCoordinatesSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinThreeUnitRangeCoordinatesSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinThreeUnitRangeCoordinatesSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinThreeUnitRangeCoordinatesSurface.boundaryNotSpectralAtomTheorem

/-- Readiness theorem for the three-unit range coordinate-reconstruction surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_three_unit_range_coordinates_surface_ready :
    concreteAnalyticSpineL2MathlibFinThreeUnitRangeCoordinatesSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinThreeUnitRangeCoordinatesSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_three_unit_synthesis_range_linear_equiv_surface_ready <|
      And.intro concrete_l2_mathlib_fin_three_unit_range_coordinates_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the three-unit range coordinate-reconstruction surface. -/
def concreteAnalyticSpineL2MathlibFinThreeUnitRangeCoordinatesHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinThreeUnitRangeCoordinatesSurfaceReady

/-- Boundary theorem for the three-unit range coordinate-reconstruction surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_three_unit_range_coordinates_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinThreeUnitRangeCoordinatesHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_three_unit_range_coordinates_surface_ready

end

end MathlibAnalytic
end MGAP4D
