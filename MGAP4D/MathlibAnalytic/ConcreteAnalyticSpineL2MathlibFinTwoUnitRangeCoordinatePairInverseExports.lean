import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatePairInverse

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Exported left-inverse law for the range coordinate-pair map. -/
theorem concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_export_left_inverse
    {k n : ℕ} (hkn : k ≠ n)
    (c : Fin 2 → ℝ) :
    concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn
        (concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn c) = c :=
  concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_left_inverse hkn c

/-- Exported right-inverse law for the range coordinate-pair map. -/
theorem concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_export_right_inverse
    {k n : ℕ} (hkn : k ≠ n)
    (v : concreteL2MathlibFinTwoUnitSynthesisRange k n) :
    concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn
        (concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn v) = v :=
  concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_right_inverse hkn v

/-- Exported injectivity of the range coordinate-pair map. -/
theorem concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_export_injective
    {k n : ℕ} (hkn : k ≠ n) :
    Function.Injective (concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn) :=
  concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_linear_map_injective hkn

/-- Exported surjectivity of the range coordinate-pair map. -/
theorem concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_export_surjective
    {k n : ℕ} (hkn : k ≠ n) :
    Function.Surjective (concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn) :=
  concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_linear_map_surjective hkn

/-- Exported bijectivity of the range coordinate-pair map. -/
theorem concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_export_bijective
    {k n : ℕ} (hkn : k ≠ n) :
    Function.Bijective (concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn) :=
  concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_linear_map_bijective hkn

/-- Exported section/retraction pair for the range coordinate-pair map. -/
theorem concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_export_inverse_pair
    {k n : ℕ} (hkn : k ≠ n) :
    (∀ c : Fin 2 → ℝ,
      concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn
        (concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn c) = c) ∧
    (∀ v : concreteL2MathlibFinTwoUnitSynthesisRange k n,
      concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn
        (concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn v) = v) :=
  concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_inverse_pair hkn

/-- Exported coordinate-pair equivalence-style certificate. -/
theorem concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_export_certificate
    {k n : ℕ} (hkn : k ≠ n) :
    Function.Bijective (concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn) ∧
    (∀ c : Fin 2 → ℝ,
      concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn
        (concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn c) = c) ∧
    (∀ v : concreteL2MathlibFinTwoUnitSynthesisRange k n,
      concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn
        (concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn v) = v) := by
  exact ⟨
    concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_export_bijective hkn,
    (concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_export_inverse_pair hkn).1,
    (concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_export_inverse_pair hkn).2⟩

/-- Adapter predicate for coordinate-pair inverse exports. -/
def concreteL2MathlibFinTwoUnitRangeCoordinatePairInverseExportsAdapter : Prop :=
  ∀ {k n : ℕ} (hkn : k ≠ n),
    Function.Bijective (concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn) ∧
    (∀ c : Fin 2 → ℝ,
      concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn
        (concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn c) = c) ∧
    (∀ v : concreteL2MathlibFinTwoUnitSynthesisRange k n,
      concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn
        (concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn v) = v)

/-- Adapter theorem for coordinate-pair inverse exports. -/
theorem concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_inverse_exports_adapter_ready :
    concreteL2MathlibFinTwoUnitRangeCoordinatePairInverseExportsAdapter := by
  intro k n hkn
  exact concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_export_certificate hkn

/-- Surface exporting the range coordinate-pair inverse facts under downstream-friendly names.

This is an export-only leaf over the range-local inverse surface.  It does not
assert an ambient basis theorem, dense span, finite-support-domain equivalence,
unbounded operator domain facts, self-adjointness, PVM construction, or spectral
atoms. -/
structure ConcreteL2MathlibFinTwoUnitRangeCoordinatePairInverseExportsSurface where
  coordinatePairInverseReady : concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatePairInverseSurfaceReady
  coordinatePairInverseExportsAdapter : concreteL2MathlibFinTwoUnitRangeCoordinatePairInverseExportsAdapter
  boundaryNoAggregateRootTouched : Prop
  boundaryNoNewMathematicalClaim : Prop
  boundaryRangeLocalOnly : Prop
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

/-- Concrete coordinate-pair inverse export surface. -/
def concreteL2MathlibFinTwoUnitRangeCoordinatePairInverseExportsSurface :
    ConcreteL2MathlibFinTwoUnitRangeCoordinatePairInverseExportsSurface :=
  { coordinatePairInverseReady :=
      concrete_analytic_spine_l2_mathlib_fin_two_unit_range_coordinate_pair_inverse_surface_ready
    coordinatePairInverseExportsAdapter :=
      concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_inverse_exports_adapter_ready
    boundaryNoAggregateRootTouched := True
    boundaryNoNewMathematicalClaim := True
    boundaryRangeLocalOnly := True
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

/-- Readiness for the coordinate-pair inverse export surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatePairInverseExportsSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatePairInverseSurfaceReady ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePairInverseExportsAdapter ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePairInverseExportsSurface.boundaryNoAggregateRootTouched ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePairInverseExportsSurface.boundaryNoNewMathematicalClaim ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePairInverseExportsSurface.boundaryRangeLocalOnly ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePairInverseExportsSurface.boundaryNoNewAmbientBasisClaim ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePairInverseExportsSurface.boundaryNotExactFirstSecondDistance ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePairInverseExportsSurface.boundaryNotFiniteDimensionalTheorem ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePairInverseExportsSurface.boundaryNotGeneralFiniteFamilyLinearIndependence ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePairInverseExportsSurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePairInverseExportsSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePairInverseExportsSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePairInverseExportsSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePairInverseExportsSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePairInverseExportsSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePairInverseExportsSurface.boundaryNotSpectralAtomTheorem

/-- Readiness theorem for the coordinate-pair inverse export surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_range_coordinate_pair_inverse_exports_surface_ready :
    concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatePairInverseExportsSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatePairInverseExportsSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_two_unit_range_coordinate_pair_inverse_surface_ready <|
      And.intro concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_inverse_exports_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial <| And.intro trivial <|
              And.intro trivial <| And.intro trivial <| And.intro trivial <|
                And.intro trivial trivial

/-- Boundary marker for the coordinate-pair inverse export surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatePairInverseExportsHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatePairInverseExportsSurfaceReady

/-- Boundary theorem for the coordinate-pair inverse export surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_range_coordinate_pair_inverse_exports_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatePairInverseExportsHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_two_unit_range_coordinate_pair_inverse_exports_surface_ready

end

end MathlibAnalytic
end MGAP4D
