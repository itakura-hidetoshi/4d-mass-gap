import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinTwoUnitSynthesisRangeEquiv

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Coordinate reconstruction on the two-unit synthesis range.

For a vector in the range of the two-unit synthesis map, its coordinates are the
inverse image under the range `LinearEquiv`.  This is the coefficient-recovery
surface after the range equivalence leaf. -/
def concreteL2MathlibFinTwoUnitRangeCoordinates
    {k n : ℕ} (hkn : k ≠ n)
    (v : concreteL2MathlibFinTwoUnitSynthesisRange k n) : Fin 2 → ℝ :=
  (concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn).symm v

/-- The first reconstructed coefficient of a vector in the two-unit synthesis range. -/
def concreteL2MathlibFinTwoUnitRangeFirstCoordinate
    {k n : ℕ} (hkn : k ≠ n)
    (v : concreteL2MathlibFinTwoUnitSynthesisRange k n) : ℝ :=
  concreteL2MathlibFinTwoUnitRangeCoordinates hkn v 0

/-- The second reconstructed coefficient of a vector in the two-unit synthesis range. -/
def concreteL2MathlibFinTwoUnitRangeSecondCoordinate
    {k n : ℕ} (hkn : k ≠ n)
    (v : concreteL2MathlibFinTwoUnitSynthesisRange k n) : ℝ :=
  concreteL2MathlibFinTwoUnitRangeCoordinates hkn v 1

/-- Re-synthesizing the reconstructed coordinates gives back the range vector. -/
theorem concrete_l2_mathlib_fin_two_unit_range_coordinates_synthesize
    {k n : ℕ} (hkn : k ≠ n)
    (v : concreteL2MathlibFinTwoUnitSynthesisRange k n) :
    concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn
        (concreteL2MathlibFinTwoUnitRangeCoordinates hkn v) = v := by
  unfold concreteL2MathlibFinTwoUnitRangeCoordinates
  exact (concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn).apply_symm_apply v

/-- Underlying-value form of coordinate reconstruction. -/
theorem concrete_l2_mathlib_fin_two_unit_range_coordinates_synthesize_val
    {k n : ℕ} (hkn : k ≠ n)
    (v : concreteL2MathlibFinTwoUnitSynthesisRange k n) :
    ((concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn
        (concreteL2MathlibFinTwoUnitRangeCoordinates hkn v)) :
        lp (fun _ : ℕ => ℝ) 2) = (v : lp (fun _ : ℕ => ℝ) 2) := by
  exact congrArg
    (fun w : concreteL2MathlibFinTwoUnitSynthesisRange k n =>
      (w : lp (fun _ : ℕ => ℝ) 2))
    (concrete_l2_mathlib_fin_two_unit_range_coordinates_synthesize hkn v)

/-- Any coefficient vector synthesizing to a range vector equals the reconstructed
coordinate vector. -/
theorem concrete_l2_mathlib_fin_two_unit_range_coordinates_unique
    {k n : ℕ} (hkn : k ≠ n)
    {v : concreteL2MathlibFinTwoUnitSynthesisRange k n} {c : Fin 2 → ℝ}
    (hc : concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn c = v) :
    c = concreteL2MathlibFinTwoUnitRangeCoordinates hkn v := by
  exact concrete_l2_mathlib_fin_two_unit_synthesis_range_linear_equiv_inverse_unique hkn hc

/-- Equality with the reconstructed coordinates is equivalent to synthesizing to
the target range vector. -/
theorem concrete_l2_mathlib_fin_two_unit_range_coordinates_eq_iff
    {k n : ℕ} (hkn : k ≠ n)
    {v : concreteL2MathlibFinTwoUnitSynthesisRange k n} {c : Fin 2 → ℝ} :
    c = concreteL2MathlibFinTwoUnitRangeCoordinates hkn v ↔
      concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn c = v := by
  constructor
  · intro hc
    rw [hc]
    exact concrete_l2_mathlib_fin_two_unit_range_coordinates_synthesize hkn v
  · intro hc
    exact concrete_l2_mathlib_fin_two_unit_range_coordinates_unique hkn hc

/-- The first coefficient of any synthesis witness is the reconstructed first
coordinate. -/
theorem concrete_l2_mathlib_fin_two_unit_range_first_coordinate_unique
    {k n : ℕ} (hkn : k ≠ n)
    {v : concreteL2MathlibFinTwoUnitSynthesisRange k n} {c : Fin 2 → ℝ}
    (hc : concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn c = v) :
    c 0 = concreteL2MathlibFinTwoUnitRangeFirstCoordinate hkn v := by
  have hcoord : c = concreteL2MathlibFinTwoUnitRangeCoordinates hkn v :=
    concrete_l2_mathlib_fin_two_unit_range_coordinates_unique hkn hc
  exact congrArg (fun f : Fin 2 → ℝ => f 0) hcoord

/-- The second coefficient of any synthesis witness is the reconstructed second
coordinate. -/
theorem concrete_l2_mathlib_fin_two_unit_range_second_coordinate_unique
    {k n : ℕ} (hkn : k ≠ n)
    {v : concreteL2MathlibFinTwoUnitSynthesisRange k n} {c : Fin 2 → ℝ}
    (hc : concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn c = v) :
    c 1 = concreteL2MathlibFinTwoUnitRangeSecondCoordinate hkn v := by
  have hcoord : c = concreteL2MathlibFinTwoUnitRangeCoordinates hkn v :=
    concrete_l2_mathlib_fin_two_unit_range_coordinates_unique hkn hc
  exact congrArg (fun f : Fin 2 → ℝ => f 1) hcoord

/-- Adapter predicate for the two-unit range coordinate-reconstruction layer. -/
def concreteL2MathlibFinTwoUnitRangeCoordinatesAdapter : Prop :=
  ∀ {k n : ℕ} (hkn : k ≠ n),
    (∀ v : concreteL2MathlibFinTwoUnitSynthesisRange k n,
      concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn
        (concreteL2MathlibFinTwoUnitRangeCoordinates hkn v) = v) ∧
    (∀ {v : concreteL2MathlibFinTwoUnitSynthesisRange k n} {c : Fin 2 → ℝ},
      concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn c = v →
        c = concreteL2MathlibFinTwoUnitRangeCoordinates hkn v)

/-- Adapter theorem for the two-unit range coordinate-reconstruction layer. -/
theorem concrete_l2_mathlib_fin_two_unit_range_coordinates_adapter_ready :
    concreteL2MathlibFinTwoUnitRangeCoordinatesAdapter := by
  intro k n hkn
  exact ⟨
    by intro v; exact concrete_l2_mathlib_fin_two_unit_range_coordinates_synthesize hkn v,
    by intro v c hc; exact concrete_l2_mathlib_fin_two_unit_range_coordinates_unique hkn hc⟩

/-- Surface for coordinate reconstruction on the two-unit synthesis range.

This layer turns the range `LinearEquiv` into explicit first/second coefficient
reconstruction for vectors in the range.  It remains strictly a two-coordinate
range-coordinate theorem and does not claim finite dimensionality of the ambient
space, a basis theorem, dense span, finite-support-domain equivalence, or any
operator-theoretic conclusion. -/
structure ConcreteL2MathlibFinTwoUnitRangeCoordinatesSurface where
  rangeLinearEquivReady : concreteAnalyticSpineL2MathlibFinTwoUnitSynthesisRangeLinearEquivSurfaceReady
  rangeCoordinatesAdapter : concreteL2MathlibFinTwoUnitRangeCoordinatesAdapter
  boundaryNotFiniteDimensionalTheorem : Prop
  boundaryNotGeneralFiniteFamilyLinearIndependence : Prop
  boundaryNotBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop

/-- Concrete coordinate-reconstruction surface for the two-unit synthesis range. -/
def concreteL2MathlibFinTwoUnitRangeCoordinatesSurface :
    ConcreteL2MathlibFinTwoUnitRangeCoordinatesSurface :=
  { rangeLinearEquivReady :=
      concrete_analytic_spine_l2_mathlib_fin_two_unit_synthesis_range_linear_equiv_surface_ready
    rangeCoordinatesAdapter :=
      concrete_l2_mathlib_fin_two_unit_range_coordinates_adapter_ready
    boundaryNotFiniteDimensionalTheorem := True
    boundaryNotGeneralFiniteFamilyLinearIndependence := True
    boundaryNotBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True }

/-- Readiness for the two-unit range coordinate-reconstruction surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatesSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitSynthesisRangeLinearEquivSurfaceReady ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatesAdapter ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatesSurface.boundaryNotFiniteDimensionalTheorem ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatesSurface.boundaryNotGeneralFiniteFamilyLinearIndependence ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatesSurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatesSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatesSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatesSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatesSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatesSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatesSurface.boundaryNotSpectralAtomTheorem

/-- Readiness theorem for the two-unit range coordinate-reconstruction surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_range_coordinates_surface_ready :
    concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatesSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatesSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_two_unit_synthesis_range_linear_equiv_surface_ready <|
      And.intro concrete_l2_mathlib_fin_two_unit_range_coordinates_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the two-unit range coordinate-reconstruction surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatesHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatesSurfaceReady

/-- Boundary theorem for the two-unit range coordinate-reconstruction surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_range_coordinates_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatesHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_two_unit_range_coordinates_surface_ready

end

end MathlibAnalytic
end MGAP4D
