import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinTwoUnitRangeTerminal

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Public façade: the two selected coordinate units have reconstructed range
coordinates `(1,0)` and `(0,1)` when `k ≠ n`. -/
theorem concrete_l2_mathlib_fin_two_unit_range_facade_coordinates
    {k n : ℕ} (hkn : k ≠ n) :
    concreteL2MathlibFinTwoUnitRangeCoordinates hkn
        (concreteL2MathlibFinTwoUnitFirstRangeVector k n) =
      (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) ∧
    concreteL2MathlibFinTwoUnitRangeCoordinates hkn
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) =
      (fun i : Fin 2 => if i = 1 then (1 : ℝ) else 0) :=
  concrete_l2_mathlib_fin_two_unit_range_terminal_coordinates hkn

/-- Public façade: the two selected range vectors are unit vectors and are
strictly metrically separated with distance at most `2` when `k ≠ n`. -/
theorem concrete_l2_mathlib_fin_two_unit_range_facade_metric
    {k n : ℕ} (hkn : k ≠ n) :
    ‖concreteL2MathlibFinTwoUnitFirstRangeVector k n‖ = 1 ∧
    ‖concreteL2MathlibFinTwoUnitSecondRangeVector k n‖ = 1 ∧
    0 < dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
      (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ∧
    dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
      (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ≤ 2 := by
  rcases concrete_l2_mathlib_fin_two_unit_range_terminal_metric hkn with
    ⟨hnorm₀, hnorm₁, hdist⟩
  exact ⟨hnorm₀, hnorm₁, hdist.1, hdist.2⟩

/-- Public façade: the range-restricted synthesis map is bijective and the range
`LinearEquiv` is injective and surjective when `k ≠ n`. -/
theorem concrete_l2_mathlib_fin_two_unit_range_facade_equiv
    {k n : ℕ} (hkn : k ≠ n) :
    Function.Bijective (concreteL2MathlibFinTwoUnitSynthesisRangeMap k n) ∧
    Function.Injective (concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn) ∧
    Function.Surjective (concreteL2MathlibFinTwoUnitSynthesisRangeLinearEquiv hkn) :=
  concrete_l2_mathlib_fin_two_unit_range_terminal_equiv hkn

/-- Public façade: terminal summary, exposed under the shorter façade name. -/
theorem concrete_l2_mathlib_fin_two_unit_range_facade_summary
    {k n : ℕ} (hkn : k ≠ n) :
    Function.Bijective (concreteL2MathlibFinTwoUnitSynthesisRangeMap k n) ∧
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
  concrete_l2_mathlib_fin_two_unit_range_terminal_summary hkn

/-- Public façade: the distinguished range vectors are unequal exactly when the
indices are unequal. -/
theorem concrete_l2_mathlib_fin_two_unit_range_facade_ne_iff
    {k n : ℕ} :
    concreteL2MathlibFinTwoUnitFirstRangeVector k n ≠
        concreteL2MathlibFinTwoUnitSecondRangeVector k n ↔ k ≠ n :=
  concrete_l2_mathlib_fin_two_unit_first_second_range_vectors_ne_iff_indices_ne

/-- Public façade: the distance between the distinguished range vectors is
positive exactly when the indices are unequal. -/
theorem concrete_l2_mathlib_fin_two_unit_range_facade_dist_pos_iff
    {k n : ℕ} :
    0 < dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ↔ k ≠ n :=
  concrete_l2_mathlib_fin_two_unit_first_second_range_dist_pos_iff_indices_ne

/-- Adapter predicate for the public façade surface. -/
def concreteL2MathlibFinTwoUnitRangeFacadeAdapter : Prop :=
  (∀ {k n : ℕ} (hkn : k ≠ n),
    Function.Bijective (concreteL2MathlibFinTwoUnitSynthesisRangeMap k n) ∧
    concreteL2MathlibFinTwoUnitRangeCoordinates hkn
        (concreteL2MathlibFinTwoUnitFirstRangeVector k n) =
      (fun i : Fin 2 => if i = 0 then (1 : ℝ) else 0) ∧
    concreteL2MathlibFinTwoUnitRangeCoordinates hkn
        (concreteL2MathlibFinTwoUnitSecondRangeVector k n) =
      (fun i : Fin 2 => if i = 1 then (1 : ℝ) else 0) ∧
    ‖concreteL2MathlibFinTwoUnitFirstRangeVector k n‖ = 1 ∧
    ‖concreteL2MathlibFinTwoUnitSecondRangeVector k n‖ = 1 ∧
    dist (concreteL2MathlibFinTwoUnitFirstRangeVector k n)
      (concreteL2MathlibFinTwoUnitSecondRangeVector k n) ∈ Set.Ioc (0 : ℝ) 2)

/-- Adapter theorem for the public façade surface. -/
theorem concrete_l2_mathlib_fin_two_unit_range_facade_adapter_ready :
    concreteL2MathlibFinTwoUnitRangeFacadeAdapter := by
  intro k n hkn
  exact concrete_l2_mathlib_fin_two_unit_range_facade_summary hkn

/-- Public façade surface for the complete two-unit range proof chain.

This is a downstream-friendly leaf façade over the terminal summary.  It contains
no new mathematical claim and still does not touch the aggregate root. -/
structure ConcreteL2MathlibFinTwoUnitRangeFacadeSurface where
  rangeTerminalReady : concreteAnalyticSpineL2MathlibFinTwoUnitRangeTerminalSurfaceReady
  rangeFacadeAdapter : concreteL2MathlibFinTwoUnitRangeFacadeAdapter
  boundaryNoAggregateRootTouched : Prop
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

/-- Concrete public façade surface. -/
def concreteL2MathlibFinTwoUnitRangeFacadeSurface :
    ConcreteL2MathlibFinTwoUnitRangeFacadeSurface :=
  { rangeTerminalReady :=
      concrete_analytic_spine_l2_mathlib_fin_two_unit_range_terminal_surface_ready
    rangeFacadeAdapter :=
      concrete_l2_mathlib_fin_two_unit_range_facade_adapter_ready
    boundaryNoAggregateRootTouched := True
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

/-- Readiness for the public façade surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitRangeFacadeSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitRangeTerminalSurfaceReady ∧
  concreteL2MathlibFinTwoUnitRangeFacadeAdapter ∧
  concreteL2MathlibFinTwoUnitRangeFacadeSurface.boundaryNoAggregateRootTouched ∧
  concreteL2MathlibFinTwoUnitRangeFacadeSurface.boundaryNoNewMathematicalClaim ∧
  concreteL2MathlibFinTwoUnitRangeFacadeSurface.boundaryNotExactFirstSecondDistance ∧
  concreteL2MathlibFinTwoUnitRangeFacadeSurface.boundaryNotFiniteDimensionalTheorem ∧
  concreteL2MathlibFinTwoUnitRangeFacadeSurface.boundaryNotGeneralFiniteFamilyLinearIndependence ∧
  concreteL2MathlibFinTwoUnitRangeFacadeSurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibFinTwoUnitRangeFacadeSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinTwoUnitRangeFacadeSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinTwoUnitRangeFacadeSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinTwoUnitRangeFacadeSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinTwoUnitRangeFacadeSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinTwoUnitRangeFacadeSurface.boundaryNotSpectralAtomTheorem

/-- Readiness theorem for the public façade surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_range_facade_surface_ready :
    concreteAnalyticSpineL2MathlibFinTwoUnitRangeFacadeSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinTwoUnitRangeFacadeSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_two_unit_range_terminal_surface_ready <|
      And.intro concrete_l2_mathlib_fin_two_unit_range_facade_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial <| And.intro trivial <|
              And.intro trivial <| And.intro trivial trivial

/-- Boundary marker for the public façade surface. -/
def concreteAnalyticSpineL2MathlibFinTwoUnitRangeFacadeHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinTwoUnitRangeFacadeSurfaceReady

/-- Boundary theorem for the public façade surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_two_unit_range_facade_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinTwoUnitRangeFacadeHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_two_unit_range_facade_surface_ready

end

end MathlibAnalytic
end MGAP4D
