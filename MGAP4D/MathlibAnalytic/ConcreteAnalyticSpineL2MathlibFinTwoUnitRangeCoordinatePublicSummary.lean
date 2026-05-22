import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinateTerminalExports

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Public summary for the completed range-local coordinate chain.

For distinct indices, this theorem bundles the coordinate-pair bijection, the
range synthesis bijection, agreement with the reconstructed coordinate function,
distinguished coordinate images, inverse laws, and the unit/metric witnesses. -/
theorem concrete_l2_mathlib_fin_two_unit_range_coordinate_public_summary
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
      (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ∈ Set.Ioc (0 : ℝ) 2 := by
  rcases concrete_l2_mathlib_fin_two_unit_range_coordinate_terminal_export_certificate hkn with
    ⟨hcoordBij, happly, hfirst, hsecond, hleft, hright⟩
  rcases concrete_l2_mathlib_fin_two_unit_range_coordinate_terminal_export_metric hkn with
    ⟨_hcoordBijMetric, hsynthBij, hnormFirst, hnormSecond, hdist⟩
  exact ⟨
    hcoordBij, hsynthBij, happly, hfirst, hsecond, hleft, hright,
    hnormFirst, hnormSecond, hdist⟩

/-- Public summary restricted to the two distinguished range witnesses. -/
theorem concrete_l2_mathlib_fin_two_unit_range_coordinate_public_distinguished_summary
    {k n : ℕ} (hkn : k ≠ n) :
    concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn
        (concreteL2MathlibFinTwoUnitFirstRangeVector k n) =
      (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) ∧
    concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) =
      (fun i : Fin 2 => if i = 1 then (1 : ℝ) else 0) ∧
    ‖concreteL2MathlibFinTwoUnitFirstRangeVector k n‖ = 1 ∧
    ‖concreteL2MathlibFinTwoUnitSecondRangeVector k n‖ = 1 ∧
    dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
      (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ∈ Set.Ioc (0 : ℝ) 2 := by
  rcases concrete_l2_mathlib_fin_two_unit_range_coordinate_terminal_export_distinguished hkn with
    ⟨hfirst, hsecond⟩
  rcases concrete_l2_mathlib_fin_two_unit_range_coordinate_terminal_export_metric hkn with
    ⟨_hcoordBij, _hsynthBij, hnormFirst, hnormSecond, hdist⟩
  exact ⟨hfirst, hsecond, hnormFirst, hnormSecond, hdist⟩

/-- Public summary of the coordinate/synthesis inverse laws. -/
theorem concrete_l2_mathlib_fin_two_unit_range_coordinate_public_inverse_summary
    {k n : ℕ} (hkn : k ≠ n) :
    Function.Bijective (concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn) ∧
    (∀ c : Fin 2 → ℝ,
      concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn
        (concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn c) = c) ∧
    (∀ v : concreteL2MathlibFinTwoUnitSynthesisRange k n,
      concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn
        (concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn v) = v) := by
  rcases concrete_l2_mathlib_fin_two_unit_range_coordinate_terminal_export_certificate hkn with
    ⟨hcoordBij, _happly, _hfirst, _hsecond, hleft, hright⟩
  exact ⟨hcoordBij, hleft, hright⟩

/-- Adapter predicate for the public coordinate summary surface. -/
def concreteL2MathlibFinTwoUnitRangeCoordinatePublicSummaryAdapter : Prop :=
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

/-- Adapter theorem for the public coordinate summary surface. -/
theorem concrete_l2_mathlib_fin_two_unit_range_coordinate_public_summary_adapter_ready :
    concreteL2MathlibFinTwoUnitRangeCoordinatePublicSummaryAdapter := by
  intro k n hkn
  rcases concrete_l2_mathlib_fin_two_unit_range_coordinate_public_summary hkn with
    ⟨hcoordBij, hsynthBij, happly, _hfirst, _hsecond, _hleft, _hright,
      hnormFirst, hnormSecond, hdist⟩
  exact ⟨hcoordBij, hsynthBij, happly, hnormFirst, hnormSecond, hdist⟩

/-- Public summary surface for the range-local coordinate chain.

This leaf is still range-local and contains no new mathematical claim.  It is a
single public summary over the coordinate terminal export layer. -/
structure ConcreteL2MathlibFinTwoUnitRangeCoordinatePublicSummarySurface where
  coordinateTerminalExportsReady : concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinateTerminalExportsSurfaceReady
  coordinatePublicSummaryAdapter : concreteL2MathlibFinTwoUnitRangeCoordinatePublicSummaryAdapter
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

/-- Concrete public coordinate summary surface. -/
def concreteL2MathlibFinTwoUnitRangeCoordinatePublicSummarySurface :
    ConcreteL2MathlibFinTwoUnitRangeCoordinatePublicSummarySurface :=
  { coordinateTerminalExportsReady :=
      concrete_analytic_spine_l2_mathlib_fin_two_unit_range_coordinate_terminal_exports_surface_ready
    coordinatePublicSummaryAdapter :=
      concrete_l2_mathlib_fin_two_unit_range_coordinate_public_summary_adapter_ready
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

/-- Readiness for the public coordinate summary surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatePublicSummarySurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinateTerminalExportsSurfaceReady ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePublicSummaryAdapter ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePublicSummarySurface.boundaryNoAggregateRootTouched ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePublicSummarySurface.boundaryNoNewMathematicalClaim ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePublicSummarySurface.boundaryRangeLocalOnly ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePublicSummarySurface.boundaryNoNewAmbientBasisClaim ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePublicSummarySurface.boundaryNotExactFirstSecondDistance ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePublicSummarySurface.boundaryNotFiniteDimensionalTheorem ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePublicSummarySurface.boundaryNotGeneralFiniteFamilyLinearIndependence ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePublicSummarySurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePublicSummarySurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePublicSummarySurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePublicSummarySurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePublicSummarySurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePublicSummarySurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinTwoUnitRangeCoordinatePublicSummarySurface.boundaryNotSpectralAtomTheorem

/-- Readiness theorem for the public coordinate summary surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_range_coordinate_public_summary_surface_ready :
    concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatePublicSummarySurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatePublicSummarySurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_two_unit_range_coordinate_terminal_exports_surface_ready <|
      And.intro concrete_l2_mathlib_fin_two_unit_range_coordinate_public_summary_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial <| And.intro trivial <|
              And.intro trivial <| And.intro trivial <| And.intro trivial <|
                And.intro trivial trivial

/-- Boundary marker for the public coordinate summary surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatePublicSummaryHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatePublicSummarySurfaceReady

/-- Boundary theorem for the public coordinate summary surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_range_coordinate_public_summary_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatePublicSummaryHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_two_unit_range_coordinate_public_summary_surface_ready

end

end MathlibAnalytic
end MGAP4D
