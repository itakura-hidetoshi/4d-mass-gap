import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatePairLinearMap

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- The coordinate-pair linear map is a left inverse to the range synthesis
`LinearEquiv` on coefficient space. -/
theorem concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_left_inverse
    {k n : ℕ} (hkn : k ≠ n)
    (c : Fin 2 → ℝ) :
    concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn
        (concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn c) = c := by
  rw [concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_linear_map_apply]
  unfold concreteL2MathlibFinTwoUnitRangeCoordinates
  exact (concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn).symm_apply_apply c

/-- The coordinate-pair linear map is a right inverse to the range synthesis
`LinearEquiv` on the synthesis range. -/
theorem concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_right_inverse
    {k n : ℕ} (hkn : k ≠ n)
    (v : concreteL2MathlibFinTwoUnitSynthesisRange k n) :
    concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn
        (concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn v) = v :=
  concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_linear_map_synthesize hkn v

/-- The coordinate-pair linear map is injective. -/
theorem concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_linear_map_injective
    {k n : ℕ} (hkn : k ≠ n) :
    Function.Injective (concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn) := by
  intro v w hvw
  calc
    v = concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn
        (concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn v) := by
      exact (concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_right_inverse hkn v).symm
    _ = concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn
        (concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn w) := by
      rw [hvw]
    _ = w := by
      exact concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_right_inverse hkn w

/-- The coordinate-pair linear map is surjective onto the two-coordinate
coefficient space. -/
theorem concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_linear_map_surjective
    {k n : ℕ} (hkn : k ≠ n) :
    Function.Surjective (concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn) := by
  intro c
  exact ⟨
    concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn c,
    concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_left_inverse hkn c⟩

/-- The coordinate-pair linear map is bijective. -/
theorem concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_linear_map_bijective
    {k n : ℕ} (hkn : k ≠ n) :
    Function.Bijective (concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn) :=
  ⟨
    concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_linear_map_injective hkn,
    concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_linear_map_surjective hkn⟩

/-- The range synthesis `LinearEquiv` and coordinate-pair `LinearMap` form a
section/retraction pair. -/
theorem concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_inverse_pair
    {k n : ℕ} (hkn : k ≠ n) :
    (∀ c : Fin 2 → ℝ,
      concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn
        (concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn c) = c) ∧
    (∀ v : concreteL2MathlibFinTwoUnitSynthesisRange k n,
      concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn
        (concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn v) = v) := by
  exact ⟨
    concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_left_inverse hkn,
    concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_right_inverse hkn⟩

/-- Adapter predicate for the coordinate-pair inverse surface. -/
def concreteL2MathlibFinTwoUnitRangeCoordinatePairInverseAdapter : Prop :=
  ∀ {k n : ℕ} (hkn : k ≠ n),
    Function.Bijective (concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn) ∧
    (∀ c : Fin 2 → ℝ,
      concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn
        (concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn c) = c) ∧
    (∀ v : concreteL2MathlibFinTwoUnitSynthesisRange k n,
      concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn
        (concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn v) = v)

/-- Adapter theorem for the coordinate-pair inverse surface. -/
theorem concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_inverse_adapter_ready :
    concreteL2MathlibFinTwoUnitRangeCoordinatePairInverseAdapter := by
  intro k n hkn
  exact ⟨
    concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_linear_map_bijective hkn,
    concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_left_inverse hkn,
    concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_right_inverse hkn⟩

/-- Surface proving that the coordinate-pair `LinearMap` is inverse to the range
synthesis equivalence.

This is still range-local.  It does not assert a basis theorem for the ambient
`ℓ²`, dense span, finite-support-domain equivalence, unbounded operator domain
facts, self-adjointness, PVM construction, or spectral atoms. -/
structure ConcreteL2MathlibFinTwoUnitRangeCoordinatePairInverseSurface where
  coordinatePairLinearMapReady : concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatePairLinearMapSurfaceReady
  coordinatePairInverseAdapter : concreteL2MathlibFinTwoUnitRangeCoordinatePairInverseAdapter
  boundaryNoAggregateRootTouched : Prop
  boundaryNoNewAmbientBasisClaim : Prop
  boundaryRangeLocalOnly : Prop
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

/-- Concrete coordinate-pair inverse surface. -/
def concreteL2MathlibFinTwoUnitRangeCoordinatePairInverseSurface :
    ConcreteL2MathlibFinTwoUnitRangeCoordinatePairInverseSurface :=
  { coordinatePairLinearMapReady :=
      concrete_analytic_spine_l2_mathlib_fin_two_unit_range_coordinate_pair_linear_map_surface_ready
    coordinatePairInverseAdapter :=
      concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_inverse_adapter_ready
    boundaryNoAggregateRootTouched := True
    boundaryNoNewAmbientBasisClaim := True
    boundaryRangeLocalOnly := True
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

/-- Readiness for the coordinate-pair inverse surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatePairInverseSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatePairLinearMapSurfaceReady ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePairInverseAdapter ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePairInverseSurface.boundaryNoAggregateRootTouched ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePairInverseSurface.boundaryNoNewAmbientBasisClaim ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePairInverseSurface.boundaryRangeLocalOnly ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePairInverseSurface.boundaryNotExactFirstSecondDistance ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePairInverseSurface.boundaryNotFiniteDimensionalTheorem ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePairInverseSurface.boundaryNotGeneralFiniteFamilyLinearIndependence ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePairInverseSurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePairInverseSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePairInverseSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePairInverseSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePairInverseSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePairInverseSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePairInverseSurface.boundaryNotSpectralAtomTheorem

/-- Readiness theorem for the coordinate-pair inverse surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_range_coordinate_pair_inverse_surface_ready :
    concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatePairInverseSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatePairInverseSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_two_unit_range_coordinate_pair_linear_map_surface_ready <|
      And.intro concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_inverse_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial <| And.intro trivial <|
              And.intro trivial <| And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the coordinate-pair inverse surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatePairInverseHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatePairInverseSurfaceReady

/-- Boundary theorem for the coordinate-pair inverse surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_range_coordinate_pair_inverse_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatePairInverseHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_two_unit_range_coordinate_pair_inverse_surface_ready

end

end MathlibAnalytic
end MGAP4D
