import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinTwoUnitRangeMetricWitness

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Compact certificate that the first distinguished range vector has coordinates
`(1,0)` and norm one. -/
theorem concrete_l2_mathlib_fin_two_unit_first_range_certificate
    {k n : ℕ} (hkn : k ≠ n) :
    concreteL2MathlibFinTwoUnitRangeCoordinates hkn
        (concreteL2MathlibFinTwoUnitFirstRangeVector k n) =
      (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) ∧
    ‖concreteL2MathlibFinTwoUnitFirstRangeVector k n‖ = 1 := by
  exact ⟨
    concrete_l2_mathlib_fin_two_unit_first_range_coordinates_eq hkn,
    concrete_l2_mathlib_fin_two_unit_first_range_vector_norm_eq_one_export k n⟩

/-- Compact certificate that the second distinguished range vector has coordinates
`(0,1)` and norm one. -/
theorem concrete_l2_mathlib_fin_two_unit_second_range_certificate
    {k n : ℕ} (hkn : k ≠ n) :
    concreteL2MathlibFinTwoUnitRangeCoordinates hkn
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) =
      (fun i : Fin 2 => if i = 1 then (1 : ℝ) else 0) ∧
    ‖concreteL2MathlibFinTwoUnitSecondRangeVector k n‖ = 1 := by
  exact ⟨
    concrete_l2_mathlib_fin_two_unit_second_range_coordinates_eq hkn,
    concrete_l2_mathlib_fin_two_unit_second_range_vector_norm_eq_one_export k n⟩

/-- Compact certificate for the two distinguished range vectors: coordinates,
norms, and metric separation. -/
theorem concrete_l2_mathlib_fin_two_unit_range_two_vector_certificate
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
      (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ∈ Set.Ioc (0 : ℝ) 2 := by
  exact ⟨
    concrete_l2_mathlib_fin_two_unit_first_range_coordinates_eq hkn,
    concrete_l2_mathlib_fin_two_unit_second_range_coordinates_eq hkn,
    concrete_l2_mathlib_fin_two_unit_first_range_vector_norm_eq_one_export k n,
    concrete_l2_mathlib_fin_two_unit_second_range_vector_norm_eq_one_export k n,
    concrete_l2_mathlib_fin_two_unit_first_second_range_dist_mem_Ioc hkn⟩

/-- Compact certificate for the explicit three-point range configuration
`0`, `e_k`, `e_n`. -/
theorem concrete_l2_mathlib_fin_two_unit_range_three_point_certificate
    {k n : ℕ} (hkn : k ≠ n) :
    ‖concreteL2MathlibFinTwoUnitZeroRangeVector k n‖ = 0 ∧
    ‖concreteL2MathlibFinTwoUnitFirstRangeVector k n‖ = 1 ∧
    ‖concreteL2MathlibFinTwoUnitSecondRangeVector k n‖ = 1 ∧
    dist (concreteL2MathlibFinTwoUnitZeroRangeVector k n)
      (concreteL2MathlibFinTwoUnitFirstRangeVector k n) = 1 ∧
    dist (concreteL2MathlibFinTwoUnitZeroRangeVector k n)
      (concreteL2MathlibFinTwoUnitSecondRangeVector k n) = 1 ∧
    0 < dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
      (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ∧
    dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
      (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ≤ 2 := by
  exact ⟨
    concrete_l2_mathlib_fin_two_unit_zero_range_vector_norm_eq_zero k n,
    concrete_l2_mathlib_fin_two_unit_first_range_vector_norm_eq_one_export k n,
    concrete_l2_mathlib_fin_two_unit_second_range_vector_norm_eq_one_export k n,
    concrete_l2_mathlib_fin_two_unit_zero_first_range_dist_eq_one k n,
    concrete_l2_mathlib_fin_two_unit_zero_second_range_dist_eq_one k n,
    concrete_l2_mathlib_fin_two_unit_first_second_range_dist_strict_lower_bound hkn,
    concrete_l2_mathlib_fin_two_unit_first_second_range_dist_upper_bound_of_ne hkn⟩

/-- Compact certificate for the range equivalence and its two distinguished
coordinate witnesses. -/
theorem concrete_l2_mathlib_fin_two_unit_range_equiv_certificate
    {k n : ℕ} (hkn : k ≠ n) :
    Function.Bijective (concreteL2MathlibFinTwoUnitSynthesisRangeMap k n) ∧
    Function.Injective (concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn) ∧
    Function.Surjective (concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn) ∧
    concreteL2MathlibFinTwoUnitRangeCoordinates hkn
        (concreteL2MathlibFinTwoUnitFirstRangeVector k n) =
      (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) ∧
    concreteL2MathlibFinTwoUnitRangeCoordinates hkn
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) =
      (fun i : Fin 2 => if i = 1 then (1 : ℝ) else 0) := by
  exact ⟨
    concrete_l2_mathlib_fin_two_unit_synthesis_range_map_bijective hkn,
    concrete_l2_mathlib_fin_two_unit_synthesis_range_linear_equiv_injective hkn,
    concrete_l2_mathlib_fin_two_unit_synthesis_range_linear_equiv_surjective hkn,
    concrete_l2_mathlib_fin_two_unit_first_range_coordinates_eq hkn,
    concrete_l2_mathlib_fin_two_unit_second_range_coordinates_eq hkn⟩

/-- Adapter predicate for compact range certificates. -/
def concreteL2MathlibFinTwoUnitRangeCertificateAdapter : Prop :=
  (∀ {k n : ℕ}, k ≠ n →
    Function.Bijective (concreteL2MathlibFinTwoUnitSynthesisRangeMap k n)) ∧
  (∀ {k n : ℕ}, k ≠ n →
    ‖concreteL2MathlibFinTwoUnitFirstRangeVector k n‖ = 1 ∧
    ‖concreteL2MathlibFinTwoUnitSecondRangeVector k n‖ = 1 ∧
    dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
      (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ∈ Set.Ioc (0 : ℝ) 2)

/-- Adapter theorem for compact range certificates. -/
theorem concrete_l2_mathlib_fin_two_unit_range_certificate_adapter_ready :
    concreteL2MathlibFinTwoUnitRangeCertificateAdapter := by
  exact ⟨
    by intro k n hkn; exact concrete_l2_mathlib_fin_two_unit_synthesis_range_map_bijective hkn,
    by
      intro k n hkn
      exact concrete_l2_mathlib_fin_two_unit_range_metric_witness_of_ne hkn⟩

/-- Surface packaging the range equivalence, coordinate reconstruction witnesses,
and metric witnesses for the two distinguished range vectors.

This layer contains no new analytic or operator-theoretic claim.  It is a compact
certificate assembled from prior leaves for downstream import. -/
structure ConcreteL2MathlibFinTwoUnitRangeCertificateSurface where
  rangeMetricWitnessReady : concreteAnalyticSpineL2MathlibFinTwoUnitRangeMetricWitnessSurfaceReady
  rangeCertificateAdapter : concreteL2MathlibFinTwoUnitRangeCertificateAdapter
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

/-- Concrete compact range-certificate surface. -/
def concreteL2MathlibFinTwoUnitRangeCertificateSurface :
    ConcreteL2MathlibFinTwoUnitRangeCertificateSurface :=
  { rangeMetricWitnessReady :=
      concrete_analytic_spine_l2_mathlib_fin_two_unit_range_metric_witness_surface_ready
    rangeCertificateAdapter :=
      concrete_l2_mathlib_fin_two_unit_range_certificate_adapter_ready
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

/-- Readiness for the compact range-certificate surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitRangeCertificateSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitRangeMetricWitnessSurfaceReady ∧
  concreteL2MathlibFinTwoUnitRangeCertificateAdapter ∧
  concreteL2MathlibFinTwoUnitRangeCertificateSurface.boundaryNotExactFirstSecondDistance ∧
  concreteL2MathlibFinTwoUnitRangeCertificateSurface.boundaryNotFiniteDimensionalTheorem ∧
  concreteL2MathlibFinTwoUnitRangeCertificateSurface.boundaryNotGeneralFiniteFamilyLinearIndependence ∧
  concreteL2MathlibFinTwoUnitRangeCertificateSurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibFinTwoUnitRangeCertificateSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinTwoUnitRangeCertificateSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinTwoUnitRangeCertificateSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinTwoUnitRangeCertificateSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinTwoUnitRangeCertificateSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinTwoUnitRangeCertificateSurface.boundaryNotSpectralAtomTheorem

/-- Readiness theorem for the compact range-certificate surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_range_certificate_surface_ready :
    concreteAnalyticSpineL2MathlibFinTwoUnitRangeCertificateSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinTwoUnitRangeCertificateSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_two_unit_range_metric_witness_surface_ready <|
      And.intro concrete_l2_mathlib_fin_two_unit_range_certificate_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the compact range-certificate surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitRangeCertificateHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitRangeCertificateSurfaceReady

/-- Boundary theorem for the compact range-certificate surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_range_certificate_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinTwoUnitRangeCertificateHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_two_unit_range_certificate_surface_ready

end

end MathlibAnalytic
end MGAP4D
