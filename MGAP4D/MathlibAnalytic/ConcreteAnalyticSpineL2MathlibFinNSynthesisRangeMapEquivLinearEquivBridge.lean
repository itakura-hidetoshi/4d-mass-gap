import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRangeMapEquiv

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- The non-linear range-map equivalence and the existing range linear equivalence
have the same forward map. -/
theorem concrete_l2_mathlib_fin_n_synthesis_range_map_equiv_apply_eq_linear_equiv_apply
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) (c : Fin m → ℝ) :
    concreteL2MathlibFinNSynthesisRangeMapEquiv hφ c =
      concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ c := rfl

/-- The chosen inverse of the range-map equivalence agrees with the inverse of
the range linear equivalence. -/
theorem concrete_l2_mathlib_fin_n_synthesis_range_map_equiv_symm_eq_linear_equiv_symm
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ)
    (v : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ)) :
    (concreteL2MathlibFinNSynthesisRangeMapEquiv hφ).symm v =
      (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ).symm v := by
  symm
  apply concrete_l2_mathlib_fin_n_synthesis_coefficients_eq_chosen_of_range_map_eq hφ
  change concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ
      ((concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ).symm v) = v
  exact (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ).apply_symm_apply v

/-- The underlying `Equiv` of the range linear equivalence has the same forward
map as the range-map equivalence. -/
theorem concrete_l2_mathlib_fin_n_synthesis_range_map_equiv_to_equiv_apply_eq
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) (c : Fin m → ℝ) :
    (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ).toEquiv c =
      concreteL2MathlibFinNSynthesisRangeMapEquiv hφ c := by
  rfl

/-- The underlying `Equiv` of the range linear equivalence has the same inverse
map as the range-map equivalence. -/
theorem concrete_l2_mathlib_fin_n_synthesis_range_map_equiv_to_equiv_symm_apply_eq
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ)
    (v : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ)) :
    (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ).toEquiv.symm v =
      (concreteL2MathlibFinNSynthesisRangeMapEquiv hφ).symm v := by
  exact (concrete_l2_mathlib_fin_n_synthesis_range_map_equiv_symm_eq_linear_equiv_symm hφ v).symm

/-- Adapter predicate for the range-map equivalence / linear-equivalence bridge. -/
def concreteL2MathlibFinNSynthesisRangeMapEquivLinearEquivBridgeAdapter : Prop :=
  ∀ {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) (c : Fin m → ℝ),
    concreteL2MathlibFinNSynthesisRangeMapEquiv hφ c =
      concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ c

/-- Adapter theorem for the range-map equivalence / linear-equivalence bridge. -/
theorem concrete_l2_mathlib_fin_n_synthesis_range_map_equiv_linear_equiv_bridge_adapter_ready :
    concreteL2MathlibFinNSynthesisRangeMapEquivLinearEquivBridgeAdapter := by
  intro m φ hφ c
  exact concrete_l2_mathlib_fin_n_synthesis_range_map_equiv_apply_eq_linear_equiv_apply hφ c

/-- Surface for the range-map equivalence / linear-equivalence bridge. -/
structure ConcreteL2MathlibFinNSynthesisRangeMapEquivLinearEquivBridgeSurface where
  coordinateRangeMapEquivReady :
    concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRangeMapEquivSurfaceReady
  rangeMapEquivLinearEquivBridgeAdapter :
    concreteL2MathlibFinNSynthesisRangeMapEquivLinearEquivBridgeAdapter
  boundaryRangeLocalOnly : Prop
  boundaryNotAmbientBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop
  boundaryNotPositiveSpectralWeightTheorem : Prop

/-- Concrete range-map equivalence / linear-equivalence bridge surface. -/
def concreteL2MathlibFinNSynthesisRangeMapEquivLinearEquivBridgeSurface :
    ConcreteL2MathlibFinNSynthesisRangeMapEquivLinearEquivBridgeSurface :=
  { coordinateRangeMapEquivReady :=
      concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_range_map_equiv_surface_ready
    rangeMapEquivLinearEquivBridgeAdapter :=
      concrete_l2_mathlib_fin_n_synthesis_range_map_equiv_linear_equiv_bridge_adapter_ready
    boundaryRangeLocalOnly := True
    boundaryNotAmbientBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True
    boundaryNotPositiveSpectralWeightTheorem := True }

/-- Readiness predicate for the range-map equivalence / linear-equivalence bridge. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisRangeMapEquivLinearEquivBridgeSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRangeMapEquivSurfaceReady ∧
  concreteL2MathlibFinNSynthesisRangeMapEquivLinearEquivBridgeAdapter ∧
  concreteL2MathlibFinNSynthesisRangeMapEquivLinearEquivBridgeSurface.boundaryRangeLocalOnly ∧
  concreteL2MathlibFinNSynthesisRangeMapEquivLinearEquivBridgeSurface.boundaryNotAmbientBasisTheorem ∧
  concreteL2MathlibFinNSynthesisRangeMapEquivLinearEquivBridgeSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinNSynthesisRangeMapEquivLinearEquivBridgeSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinNSynthesisRangeMapEquivLinearEquivBridgeSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinNSynthesisRangeMapEquivLinearEquivBridgeSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinNSynthesisRangeMapEquivLinearEquivBridgeSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinNSynthesisRangeMapEquivLinearEquivBridgeSurface.boundaryNotSpectralAtomTheorem ∧
  concreteL2MathlibFinNSynthesisRangeMapEquivLinearEquivBridgeSurface.boundaryNotPositiveSpectralWeightTheorem

/-- Readiness theorem for the range-map equivalence / linear-equivalence bridge. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_range_map_equiv_linear_equiv_bridge_surface_ready :
    concreteAnalyticSpineL2MathlibFinNSynthesisRangeMapEquivLinearEquivBridgeSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinNSynthesisRangeMapEquivLinearEquivBridgeSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_range_map_equiv_surface_ready <|
      And.intro concrete_l2_mathlib_fin_n_synthesis_range_map_equiv_linear_equiv_bridge_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial trivial

/-- Hard-residual boundary marker for the range-map equivalence / linear-equivalence bridge. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisRangeMapEquivLinearEquivBridgeHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisRangeMapEquivLinearEquivBridgeSurfaceReady

/-- Hard-residual boundary theorem for the range-map equivalence / linear-equivalence bridge. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_range_map_equiv_linear_equiv_bridge_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinNSynthesisRangeMapEquivLinearEquivBridgeHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_n_synthesis_range_map_equiv_linear_equiv_bridge_surface_ready

end

end MathlibAnalytic
end MGAP4D
