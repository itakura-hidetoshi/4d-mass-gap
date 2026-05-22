import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinTwoUnitRangeCertificate

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Exported bijectivity certificate for the range-restricted two-unit synthesis
map. -/
theorem concrete_l2_mathlib_fin_two_unit_range_certificate_bijective
    {k n : ℕ} (hkn : k ≠ n) :
    Function.Bijective (concreteL2MathlibFinTwoUnitSynthesisRangeMap k n) :=
  (concrete_l2_mathlib_fin_two_unit_range_equiv_certificate hkn).1

/-- Exported injectivity certificate for the range `LinearEquiv`. -/
theorem concrete_l2_mathlib_fin_two_unit_range_certificate_linear_equiv_injective
    {k n : ℕ} (hkn : k ≠ n) :
    Function.Injective (concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn) :=
  (concrete_l2_mathlib_fin_two_unit_range_equiv_certificate hkn).2.1

/-- Exported surjectivity certificate for the range `LinearEquiv`. -/
theorem concrete_l2_mathlib_fin_two_unit_range_certificate_linear_equiv_surjective
    {k n : ℕ} (hkn : k ≠ n) :
    Function.Surjective (concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn) :=
  (concrete_l2_mathlib_fin_two_unit_range_equiv_certificate hkn).2.2.1

/-- Exported first-coordinate certificate for the first distinguished range
vector. -/
theorem concrete_l2_mathlib_fin_two_unit_range_certificate_first_coordinates
    {k n : ℕ} (hkn : k ≠ n) :
    concreteL2MathlibFinTwoUnitRangeCoordinates hkn
        (concreteL2MathlibFinTwoUnitFirstRangeVector k n) =
      (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) :=
  (concrete_l2_mathlib_fin_two_unit_range_equiv_certificate hkn).2.2.2.1

/-- Exported second-coordinate certificate for the second distinguished range
vector. -/
theorem concrete_l2_mathlib_fin_two_unit_range_certificate_second_coordinates
    {k n : ℕ} (hkn : k ≠ n) :
    concreteL2MathlibFinTwoUnitRangeCoordinates hkn
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) =
      (fun i : Fin 2 => if i = 1 then (1 : ℝ) else 0) :=
  (concrete_l2_mathlib_fin_two_unit_range_equiv_certificate hkn).2.2.2.2

/-- Exported metric certificate for the two distinguished range vectors. -/
theorem concrete_l2_mathlib_fin_two_unit_range_certificate_metric_pair
    {k n : ℕ} (hkn : k ≠ n) :
    ‖concreteL2MathlibFinTwoUnitFirstRangeVector k n‖ = 1 ∧
    ‖concreteL2MathlibFinTwoUnitSecondRangeVector k n‖ = 1 ∧
    dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
      (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ∈ Set.Ioc (0 : ℝ) 2 := by
  rcases concrete_l2_mathlib_fin_two_unit_range_two_vector_certificate hkn with
    ⟨_hcoord₀, _hcoord₁, hnorm₀, hnorm₁, hdist⟩
  exact ⟨hnorm₀, hnorm₁, hdist⟩

/-- Exported coordinate certificate pair for the two distinguished range vectors. -/
theorem concrete_l2_mathlib_fin_two_unit_range_certificate_coordinate_pair
    {k n : ℕ} (hkn : k ≠ n) :
    concreteL2MathlibFinTwoUnitRangeCoordinates hkn
        (concreteL2MathlibFinTwoUnitFirstRangeVector k n) =
      (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) ∧
    concreteL2MathlibFinTwoUnitRangeCoordinates hkn
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) =
      (fun i : Fin 2 => if i = 1 then (1 : ℝ) else 0) := by
  exact ⟨
    concrete_l2_mathlib_fin_two_unit_range_certificate_first_coordinates hkn,
    concrete_l2_mathlib_fin_two_unit_range_certificate_second_coordinates hkn⟩

/-- Exported full compact certificate for the two distinguished range vectors. -/
theorem concrete_l2_mathlib_fin_two_unit_range_certificate_two_vector_export
    {k n : ℕ} (hkn : k ≠ n) :
    concreteL2MathlibFinTwoUnitRangeCoordinates hkn
        (concreteL2MathlibFinTwoUnitFirstRangeVector k n) =
      (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) ∧
    concreteL2MathlibFinTwoUnitRangeCoordinates hkn
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) =
      (fun i : Fin 2 => if i = 1 then (1 : ℝ) else 0) ∧
    ‖concreteL2MathlibFinTwoUnitFirstRangeVector k n‖ = 1 ∧
    ‖concreteL2MathlibFinTwoUnitSecondRangeVector k n‖ = 1 ∧
    dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
      (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ∈ Set.Ioc (0 : ℝ) 2 :=
  concrete_l2_mathlib_fin_two_unit_range_two_vector_certificate hkn

/-- Adapter predicate for range-certificate exports. -/
def concreteL2MathlibFinTwoUnitRangeCertificateExportsAdapter : Prop :=
  (∀ {k n : ℕ} (hkn : k ≠ n),
    Function.Bijective (concreteL2MathlibFinTwoUnitSynthesisRangeMap k n)) ∧
  (∀ {k n : ℕ} (hkn : k ≠ n),
    concreteL2MathlibFinTwoUnitRangeCoordinates hkn
        (concreteL2MathlibFinTwoUnitFirstRangeVector k n) =
      (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0)) ∧
  (∀ {k n : ℕ} (hkn : k ≠ n),
    ‖concreteL2MathlibFinTwoUnitFirstRangeVector k n‖ = 1 ∧
    ‖concreteL2MathlibFinTwoUnitSecondRangeVector k n‖ = 1 ∧
    dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
      (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ∈ Set.Ioc (0 : ℝ) 2)

/-- Adapter theorem for range-certificate exports. -/
theorem concrete_l2_mathlib_fin_two_unit_range_certificate_exports_adapter_ready :
    concreteL2MathlibFinTwoUnitRangeCertificateExportsAdapter := by
  exact ⟨
    by intro k n hkn; exact concrete_l2_mathlib_fin_two_unit_range_certificate_bijective hkn,
    by intro k n hkn; exact concrete_l2_mathlib_fin_two_unit_range_certificate_first_coordinates hkn,
    by intro k n hkn; exact concrete_l2_mathlib_fin_two_unit_range_certificate_metric_pair hkn⟩

/-- Surface exporting the compact range certificate as smaller downstream-friendly
theorems.

This layer contains no new mathematical claim; it decomposes the compact
certificate into named bijection, coordinate, and metric exports. -/
structure ConcreteL2MathlibFinTwoUnitRangeCertificateExportsSurface where
  rangeCertificateReady : concreteAnalyticSpineL2MathlibFinTwoUnitRangeCertificateSurfaceReady
  rangeCertificateExportsAdapter : concreteL2MathlibFinTwoUnitRangeCertificateExportsAdapter
  boundaryNoNewMathematicalClaim : Prop
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

/-- Concrete range-certificate export surface. -/
def concreteL2MathlibFinTwoUnitRangeCertificateExportsSurface :
    ConcreteL2MathlibFinTwoUnitRangeCertificateExportsSurface :=
  { rangeCertificateReady :=
      concrete_analytic_spine_l2_mathlib_fin_two_unit_range_certificate_surface_ready
    rangeCertificateExportsAdapter :=
      concrete_l2_mathlib_fin_two_unit_range_certificate_exports_adapter_ready
    boundaryNoNewMathematicalClaim := True
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

/-- Readiness for the range-certificate export surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitRangeCertificateExportsSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitRangeCertificateSurfaceReady ∧
  concreteL2MathlibFinTwoUnitRangeCertificateExportsAdapter ∧
  concreteL2MathlibFinTwoUnitRangeCertificateExportsSurface.boundaryNoNewMathematicalClaim ∧
  concreteL2MathlibFinTwoUnitRangeCertificateExportsSurface.boundaryNotExactFirstSecondDistance ∧
  concreteL2MathlibFinTwoUnitRangeCertificateExportsSurface.boundaryNotFiniteDimensionalTheorem ∧
  concreteL2MathlibFinTwoUnitRangeCertificateExportsSurface.boundaryNotGeneralFiniteFamilyLinearIndependence ∧
  concreteL2MathlibFinTwoUnitRangeCertificateExportsSurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibFinTwoUnitRangeCertificateExportsSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinTwoUnitRangeCertificateExportsSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinTwoUnitRangeCertificateExportsSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinTwoUnitRangeCertificateExportsSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinTwoUnitRangeCertificateExportsSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinTwoUnitRangeCertificateExportsSurface.boundaryNotSpectralAtomTheorem

/-- Readiness theorem for the range-certificate export surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_range_certificate_exports_surface_ready :
    concreteAnalyticSpineL2MathlibFinTwoUnitRangeCertificateExportsSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinTwoUnitRangeCertificateExportsSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_two_unit_range_certificate_surface_ready <|
      And.intro concrete_l2_mathlib_fin_two_unit_range_certificate_exports_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial <| And.intro trivial <|
              And.intro trivial trivial

/-- Boundary marker for the range-certificate export surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitRangeCertificateExportsHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitRangeCertificateExportsSurfaceReady

/-- Boundary theorem for the range-certificate export surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_range_certificate_exports_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinTwoUnitRangeCertificateExportsHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_two_unit_range_certificate_exports_surface_ready

end

end MathlibAnalytic
end MGAP4D
