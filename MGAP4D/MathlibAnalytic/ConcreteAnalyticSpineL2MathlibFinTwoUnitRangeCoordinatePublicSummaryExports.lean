import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatePublicSummary

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Exported public summary for the completed range-local coordinate chain. -/
theorem concrete_l2_mathlib_fin_two_unit_range_coordinate_public_summary_export
    {k n : ℕ} (hkn : k ≠ n) :
    Function.Bijective (concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn) ∧
    Function.Bijective (concreteL2MathlibFinTwoUnitSynthesisRangeMap k n) ∧
    (∀ v : concreteL2MathlibFinTwoUnitSynthesisRange k n,
      concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn v =
        concreteL2MathlibFinTwoUnitRangeCoordinates hkn v) ∧
    concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn
        (concreteL2MathlibFinTwoUnitFirstRangeVector k n) =
      (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) ∧
    concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) =
      (fun i : Fin 2 => if i = 1 then (1 : ℝ) else 0) ∧
    (∀ c : Fin 2 → ℝ,
      concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn
        (concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn c) = c) ∧
    (∀ v : concreteL2MathlibFinTwoUnitSynthesisRange k n,
      concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn
        (concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn v) = v) ∧
    ‖concreteL2MathlibFinTwoUnitFirstRangeVector k n‖ = 1 ∧
    ‖concreteL2MathlibFinTwoUnitSecondRangeVector k n‖ = 1 ∧
    dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
      (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ∈ Set.Ioc (0 : ℝ) 2 :=
  concrete_l2_mathlib_fin_two_unit_range_coordinate_public_summary hkn

/-- Exported coordinate-pair bijectivity from the public summary. -/
theorem concrete_l2_mathlib_fin_two_unit_range_coordinate_public_summary_export_coordinate_bijective
    {k n : ℕ} (hkn : k ≠ n) :
    Function.Bijective (concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn) :=
  (concrete_l2_mathlib_fin_two_unit_range_coordinate_public_summary_export hkn).1

/-- Exported synthesis-range bijectivity from the public summary. -/
theorem concrete_l2_mathlib_fin_two_unit_range_coordinate_public_summary_export_synthesis_bijective
    {k n : ℕ} (hkn : k ≠ n) :
    Function.Bijective (concreteL2MathlibFinTwoUnitSynthesisRangeMap k n) :=
  (concrete_l2_mathlib_fin_two_unit_range_coordinate_public_summary_export hkn).2.1

/-- Exported agreement of the coordinate-pair map with reconstructed coordinates. -/
theorem concrete_l2_mathlib_fin_two_unit_range_coordinate_public_summary_export_apply
    {k n : ℕ} (hkn : k ≠ n)
    (v : concreteL2MathlibFinTwoUnitSynthesisRange k n) :
    concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn v =
      concreteL2MathlibFinTwoUnitRangeCoordinates hkn v :=
  (concrete_l2_mathlib_fin_two_unit_range_coordinate_public_summary_export hkn).2.2.1 v

/-- Exported first distinguished coordinate image from the public summary. -/
theorem concrete_l2_mathlib_fin_two_unit_range_coordinate_public_summary_export_first
    {k n : ℕ} (hkn : k ≠ n) :
    concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn
        (concreteL2MathlibFinTwoUnitFirstRangeVector k n) =
      (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) :=
  (concrete_l2_mathlib_fin_two_unit_range_coordinate_public_summary_export hkn).2.2.2.1

/-- Exported second distinguished coordinate image from the public summary. -/
theorem concrete_l2_mathlib_fin_two_unit_range_coordinate_public_summary_export_second
    {k n : ℕ} (hkn : k ≠ n) :
    concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) =
      (fun i : Fin 2 => if i = 1 then (1 : ℝ) else 0) :=
  (concrete_l2_mathlib_fin_two_unit_range_coordinate_public_summary_export hkn).2.2.2.2.1

/-- Exported left inverse law from the public summary. -/
theorem concrete_l2_mathlib_fin_two_unit_range_coordinate_public_summary_export_left_inverse
    {k n : ℕ} (hkn : k ≠ n)
    (c : Fin 2 → ℝ) :
    concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn
        (concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn c) = c :=
  (concrete_l2_mathlib_fin_two_unit_range_coordinate_public_summary_export hkn).2.2.2.2.2.1 c

/-- Exported right inverse law from the public summary. -/
theorem concrete_l2_mathlib_fin_two_unit_range_coordinate_public_summary_export_right_inverse
    {k n : ℕ} (hkn : k ≠ n)
    (v : concreteL2MathlibFinTwoUnitSynthesisRange k n) :
    concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn
        (concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn v) = v :=
  (concrete_l2_mathlib_fin_two_unit_range_coordinate_public_summary_export hkn).2.2.2.2.2.2.1 v

/-- Exported metric package from the public summary. -/
theorem concrete_l2_mathlib_fin_two_unit_range_coordinate_public_summary_export_metric
    {k n : ℕ} (hkn : k ≠ n) :
    ‖concreteL2MathlibFinTwoUnitFirstRangeVector k n‖ = 1 ∧
    ‖concreteL2MathlibFinTwoUnitSecondRangeVector k n‖ = 1 ∧
    dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
      (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ∈ Set.Ioc (0 : ℝ) 2 := by
  rcases concrete_l2_mathlib_fin_two_unit_range_coordinate_public_summary_export hkn with
    ⟨_hcoordBij, _hsynthBij, _happly, _hfirst, _hsecond, _hleft, _hright,
      hnormFirst, hnormSecond, hdist⟩
  exact ⟨hnormFirst, hnormSecond, hdist⟩

/-- Adapter predicate for public coordinate summary exports. -/
def concreteL2MathlibFinTwoUnitRangeCoordinatePublicSummaryExportsAdapter : Prop :=
  ∀ {k n : ℕ} (hkn : k ≠ n),
    Function.Bijective (concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn) ∧
    Function.Bijective (concreteL2MathlibFinTwoUnitSynthesisRangeMap k n) ∧
    (∀ v : concreteL2MathlibFinTwoUnitSynthesisRange k n,
      concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn v =
        concreteL2MathlibFinTwoUnitRangeCoordinates hkn v) ∧
    ‖concreteL2MathlibFinTwoUnitFirstRangeVector k n‖ = 1 ∧
    ‖concreteL2MathlibFinTwoUnitSecondRangeVector k n‖ = 1 ∧
    dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
      (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ∈ Set.Ioc (0 : ℝ) 2

/-- Adapter theorem for public coordinate summary exports. -/
theorem concrete_l2_mathlib_fin_two_unit_range_coordinate_public_summary_exports_adapter_ready :
    concreteL2MathlibFinTwoUnitRangeCoordinatePublicSummaryExportsAdapter := by
  intro k n hkn
  exact ⟨
    concrete_l2_mathlib_fin_two_unit_range_coordinate_public_summary_export_coordinate_bijective hkn,
    concrete_l2_mathlib_fin_two_unit_range_coordinate_public_summary_export_synthesis_bijective hkn,
    concrete_l2_mathlib_fin_two_unit_range_coordinate_public_summary_export_apply hkn,
    (concrete_l2_mathlib_fin_two_unit_range_coordinate_public_summary_export_metric hkn).1,
    (concrete_l2_mathlib_fin_two_unit_range_coordinate_public_summary_export_metric hkn).2.1,
    (concrete_l2_mathlib_fin_two_unit_range_coordinate_public_summary_export_metric hkn).2.2⟩

/-- Export-only surface for the public coordinate summary. -/
structure ConcreteL2MathlibFinTwoUnitRangeCoordinatePublicSummaryExportsSurface where
  coordinatePublicSummaryReady : concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatePublicSummarySurfaceReady
  coordinatePublicSummaryExportsAdapter : concreteL2MathlibFinTwoUnitRangeCoordinatePublicSummaryExportsAdapter
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

/-- Concrete public coordinate summary export surface. -/
def concreteL2MathlibFinTwoUnitRangeCoordinatePublicSummaryExportsSurface :
    ConcreteL2MathlibFinTwoUnitRangeCoordinatePublicSummaryExportsSurface :=
  { coordinatePublicSummaryReady :=
      concrete_analytic_spine_l2_mathlib_fin_two_unit_range_coordinate_public_summary_surface_ready
    coordinatePublicSummaryExportsAdapter :=
      concrete_l2_mathlib_fin_two_unit_range_coordinate_public_summary_exports_adapter_ready
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

/-- Readiness for the public coordinate summary export surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatePublicSummaryExportsSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatePublicSummarySurfaceReady ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePublicSummaryExportsAdapter ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePublicSummaryExportsSurface.boundaryNoAggregateRootTouched ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePublicSummaryExportsSurface.boundaryNoNewMathematicalClaim ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePublicSummaryExportsSurface.boundaryRangeLocalOnly ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePublicSummaryExportsSurface.boundaryNoNewAmbientBasisClaim ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePublicSummaryExportsSurface.boundaryNotExactFirstSecondDistance ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePublicSummaryExportsSurface.boundaryNotFiniteDimensionalTheorem ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePublicSummaryExportsSurface.boundaryNotGeneralFiniteFamilyLinearIndependence ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePublicSummaryExportsSurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePublicSummaryExportsSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePublicSummaryExportsSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePublicSummaryExportsSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePublicSummaryExportsSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePublicSummaryExportsSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePublicSummaryExportsSurface.boundaryNotSpectralAtomTheorem

/-- Readiness theorem for the public coordinate summary export surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_range_coordinate_public_summary_exports_surface_ready :
    concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatePublicSummaryExportsSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatePublicSummaryExportsSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_two_unit_range_coordinate_public_summary_surface_ready <|
      And.intro concrete_l2_mathlib_fin_two_unit_range_coordinate_public_summary_exports_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial <| And.intro trivial <|
              And.intro trivial <| And.intro trivial <| And.intro trivial <|
                And.intro trivial trivial

/-- Boundary marker for the public coordinate summary export surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatePublicSummaryExportsHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatePublicSummaryExportsSurfaceReady

/-- Boundary theorem for the public coordinate summary export surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_range_coordinate_public_summary_exports_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatePublicSummaryExportsHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_two_unit_range_coordinate_public_summary_exports_surface_ready

end

end MathlibAnalytic
end MGAP4D
