import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatePairFacade

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Coordinate equivalence certificate for the two-unit synthesis range.

For distinct selected indices, the coordinate-pair map from the synthesis range to
`Fin 2 → ℝ` is bijective, agrees with the reconstructed coordinate function, and
is inverse to range synthesis on both sides. -/
theorem concrete_l2_mathlib_fin_two_unit_range_coordinate_equivalence_certificate
    {k n : ℕ} (hkn : k ≠ n) :
    Function.Bijective (concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn) ∧
    (∀ v : concreteL2MathlibFinTwoUnitSynthesisRange k n,
      concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn v =
        concreteL2MathlibFinTwoUnitRangeCoordinates hkn v) ∧
    (∀ c : Fin 2 → ℝ,
      concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn
        (concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn c) = c) ∧
    (∀ v : concreteL2MathlibFinTwoUnitSynthesisRange k n,
      concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn
        (concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn v) = v) := by
  rcases concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_facade_summary hkn with
    ⟨hbij, happly, _hfirst, _hsecond, hleft, hright⟩
  exact ⟨hbij, happly, hleft, hright⟩

/-- Distinguished-coordinate certificate for the two range unit witnesses. -/
theorem concrete_l2_mathlib_fin_two_unit_range_coordinate_equivalence_distinguished
    {k n : ℕ} (hkn : k ≠ n) :
    concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn
        (concreteL2MathlibFinTwoUnitFirstRangeVector k n) =
      (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) ∧
    concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) =
      (fun i : Fin 2 => if i = 1 then (1 : ℝ) else 0) := by
  exact ⟨
    concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_facade_first hkn,
    concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_facade_second hkn⟩

/-- Full coordinate equivalence certificate including distinguished vector images. -/
theorem concrete_l2_mathlib_fin_two_unit_range_coordinate_equivalence_full_certificate
    {k n : ℕ} (hkn : k ≠ n) :
    Function.Bijective (concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn) ∧
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
        (concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn v) = v) := by
  rcases concrete_l2_mathlib_fin_two_unit_range_coordinate_pair_facade_summary hkn with
    ⟨hbij, happly, hfirst, hsecond, hleft, hright⟩
  exact ⟨hbij, happly, hfirst, hsecond, hleft, hright⟩

/-- Adapter predicate for the coordinate equivalence certificate surface. -/
def concreteL2MathlibFinTwoUnitRangeCoordinateEquivalenceCertificateAdapter : Prop :=
  ∀ {k n : ℕ} (hkn : k ≠ n),
    Function.Bijective (concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn) ∧
    (∀ v : concreteL2MathlibFinTwoUnitSynthesisRange k n,
      concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn v =
        concreteL2MathlibFinTwoUnitRangeCoordinates hkn v) ∧
    (∀ c : Fin 2 → ℝ,
      concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn
        (concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn c) = c) ∧
    (∀ v : concreteL2MathlibFinTwoUnitSynthesisRange k n,
      concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn
        (concreteL2MathlibFinTwoUnitRangeCoordinatePairLinearMap hkn v) = v)

/-- Adapter theorem for the coordinate equivalence certificate surface. -/
theorem concrete_l2_mathlib_fin_two_unit_range_coordinate_equivalence_certificate_adapter_ready :
    concreteL2MathlibFinTwoUnitRangeCoordinateEquivalenceCertificateAdapter := by
  intro k n hkn
  exact concrete_l2_mathlib_fin_two_unit_range_coordinate_equivalence_certificate hkn

/-- Surface bundling the range-local coordinate equivalence between the synthesis
range and `Fin 2 → ℝ`.

This leaf is still range-local and does not assert an ambient basis theorem,
dense span, finite-support-domain equivalence, unbounded operator domain facts,
self-adjointness, PVM construction, or spectral atoms. -/
structure ConcreteL2MathlibFinTwoUnitRangeCoordinateEquivalenceCertificateSurface where
  coordinatePairFacadeReady : concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatePairFacadeSurfaceReady
  coordinateEquivalenceCertificateAdapter : concreteL2MathlibFinTwoUnitRangeCoordinateEquivalenceCertificateAdapter
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

/-- Concrete coordinate equivalence certificate surface. -/
def concreteL2MathlibFinTwoUnitRangeCoordinateEquivalenceCertificateSurface :
    ConcreteL2MathlibFinTwoUnitRangeCoordinateEquivalenceCertificateSurface :=
  { coordinatePairFacadeReady :=
      concrete_analytic_spine_l2_mathlib_fin_two_unit_range_coordinate_pair_facade_surface_ready
    coordinateEquivalenceCertificateAdapter :=
      concrete_l2_mathlib_fin_two_unit_range_coordinate_equivalence_certificate_adapter_ready
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

/-- Readiness for the coordinate equivalence certificate surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinateEquivalenceCertificateSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinatePairFacadeSurfaceReady ∧
  concreteL2MathlibFinTwoUnitRangeCoordinateEquivalenceCertificateAdapter ∧
  concreteL2MathlibFinTwoUnitRangeCoordinateEquivalenceCertificateSurface.boundaryNoAggregateRootTouched ∧
  concreteL2MathlibFinTwoUnitRangeCoordinateEquivalenceCertificateSurface.boundaryNoNewMathematicalClaim ∧
  concreteL2MathlibFinTwoUnitRangeCoordinateEquivalenceCertificateSurface.boundaryRangeLocalOnly ∧
  concreteL2MathlibFinTwoUnitRangeCoordinateEquivalenceCertificateSurface.boundaryNoNewAmbientBasisClaim ∧
  concreteL2MathlibFinTwoUnitRangeCoordinateEquivalenceCertificateSurface.boundaryNotExactFirstSecondDistance ∧
  concreteL2MathlibFinTwoUnitRangeCoordinateEquivalenceCertificateSurface.boundaryNotFiniteDimensionalTheorem ∧
  concreteL2MathlibFinTwoUnitRangeCoordinateEquivalenceCertificateSurface.boundaryNotGeneralFiniteFamilyLinearIndependence ∧
  concreteL2MathlibFinTwoUnitRangeCoordinateEquivalenceCertificateSurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibFinTwoUnitRangeCoordinateEquivalenceCertificateSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinTwoUnitRangeCoordinateEquivalenceCertificateSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinTwoUnitRangeCoordinateEquivalenceCertificateSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinTwoUnitRangeCoordinateEquivalenceCertificateSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinTwoUnitRangeCoordinateEquivalenceCertificateSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinTwoUnitRangeCoordinateEquivalenceCertificateSurface.boundaryNotSpectralAtomTheorem

/-- Readiness theorem for the coordinate equivalence certificate surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_range_coordinate_equivalence_certificate_surface_ready :
    concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinateEquivalenceCertificateSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinateEquivalenceCertificateSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_two_unit_range_coordinate_pair_facade_surface_ready <|
      And.intro concrete_l2_mathlib_fin_two_unit_range_coordinate_equivalence_certificate_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial <| And.intro trivial <|
              And.intro trivial <| And.intro trivial <| And.intro trivial <|
                And.intro trivial trivial

/-- Boundary marker for the coordinate equivalence certificate surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinateEquivalenceCertificateHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinateEquivalenceCertificateSurfaceReady

/-- Boundary theorem for the coordinate equivalence certificate surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_range_coordinate_equivalence_certificate_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinTwoUnitRangeCoordinateEquivalenceCertificateHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_two_unit_range_coordinate_equivalence_certificate_surface_ready

end

end MathlibAnalytic
end MGAP4D
