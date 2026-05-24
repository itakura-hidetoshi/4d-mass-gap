import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinNSynthesisRangeMapEquivLinearEquivBridge

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- The range linear equivalence has forward linear-map action equal to the
range-restricted synthesis map. -/
theorem concrete_l2_mathlib_fin_n_synthesis_linear_equiv_to_linear_map_apply_eq_range_map
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) (c : Fin m → ℝ) :
    (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ).toLinearMap c =
      concreteL2MathlibFiniteSynthesisRangeMap (Fin m)
        (concreteL2MathlibFinNSynthesisLinearMap m φ) c := rfl

/-- The range linear equivalence has forward linear-map action equal to the
underlying concrete synthesis linear map after coercing out of the range. -/
theorem concrete_l2_mathlib_fin_n_synthesis_linear_equiv_to_linear_map_apply_val_eq_linear_map_apply
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) (c : Fin m → ℝ) :
    ((concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ).toLinearMap c :
      lp (fun _ : ℕ => ℝ) 2) =
      concreteL2MathlibFinNSynthesisLinearMap m φ c := rfl

/-- The non-linear range-map equivalence and the linear equivalence have the
same underlying `ℓ²` value on coefficients. -/
theorem concrete_l2_mathlib_fin_n_synthesis_range_map_equiv_apply_val_eq_linear_map_apply
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) (c : Fin m → ℝ) :
    (concreteL2MathlibFinNSynthesisRangeMapEquiv hφ c : lp (fun _ : ℕ => ℝ) 2) =
      concreteL2MathlibFinNSynthesisLinearMap m φ c := rfl

/-- Forward equality between the range-map equivalence and the linear-map carrier
as functions into the range. -/
theorem concrete_l2_mathlib_fin_n_synthesis_range_map_equiv_funext_eq_linear_equiv
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) :
    (fun c : Fin m → ℝ => concreteL2MathlibFinNSynthesisRangeMapEquiv hφ c) =
      (fun c : Fin m → ℝ => concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ c) := by
  funext c
  exact concrete_l2_mathlib_fin_n_synthesis_range_map_equiv_apply_eq_linear_equiv_apply hφ c

/-- Adapter predicate for the range-map / linear-map identity layer. -/
def concreteL2MathlibFinNSynthesisRangeMapLinearMapIdentityAdapter : Prop :=
  ∀ {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) (c : Fin m → ℝ),
    ((concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ).toLinearMap c :
      lp (fun _ : ℕ => ℝ) 2) =
      concreteL2MathlibFinNSynthesisLinearMap m φ c

/-- Adapter theorem for the range-map / linear-map identity layer. -/
theorem concrete_l2_mathlib_fin_n_synthesis_range_map_linear_map_identity_adapter_ready :
    concreteL2MathlibFinNSynthesisRangeMapLinearMapIdentityAdapter := by
  intro m φ hφ c
  exact concrete_l2_mathlib_fin_n_synthesis_linear_equiv_to_linear_map_apply_val_eq_linear_map_apply hφ c

/-- Surface for the range-map / linear-map identity layer. -/
structure ConcreteL2MathlibFinNSynthesisRangeMapLinearMapIdentitySurface where
  rangeMapEquivLinearEquivBridgeReady :
    concreteAnalyticSpineL2MathlibFinNSynthesisRangeMapEquivLinearEquivBridgeSurfaceReady
  rangeMapLinearMapIdentityAdapter :
    concreteL2MathlibFinNSynthesisRangeMapLinearMapIdentityAdapter
  boundaryRangeLocalOnly : Prop
  boundaryNotAmbientBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop
  boundaryNotPositiveSpectralWeightTheorem : Prop

/-- Concrete range-map / linear-map identity surface. -/
def concreteL2MathlibFinNSynthesisRangeMapLinearMapIdentitySurface :
    ConcreteL2MathlibFinNSynthesisRangeMapLinearMapIdentitySurface :=
  { rangeMapEquivLinearEquivBridgeReady :=
      concrete_analytic_spine_l2_mathlib_fin_n_synthesis_range_map_equiv_linear_equiv_bridge_surface_ready
    rangeMapLinearMapIdentityAdapter :=
      concrete_l2_mathlib_fin_n_synthesis_range_map_linear_map_identity_adapter_ready
    boundaryRangeLocalOnly := True
    boundaryNotAmbientBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True
    boundaryNotPositiveSpectralWeightTheorem := True }

/-- Readiness predicate for the range-map / linear-map identity layer. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisRangeMapLinearMapIdentitySurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisRangeMapEquivLinearEquivBridgeSurfaceReady ∧
  concreteL2MathlibFinNSynthesisRangeMapLinearMapIdentityAdapter ∧
  concreteL2MathlibFinNSynthesisRangeMapLinearMapIdentitySurface.boundaryRangeLocalOnly ∧
  concreteL2MathlibFinNSynthesisRangeMapLinearMapIdentitySurface.boundaryNotAmbientBasisTheorem ∧
  concreteL2MathlibFinNSynthesisRangeMapLinearMapIdentitySurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinNSynthesisRangeMapLinearMapIdentitySurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinNSynthesisRangeMapLinearMapIdentitySurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinNSynthesisRangeMapLinearMapIdentitySurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinNSynthesisRangeMapLinearMapIdentitySurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinNSynthesisRangeMapLinearMapIdentitySurface.boundaryNotSpectralAtomTheorem ∧
  concreteL2MathlibFinNSynthesisRangeMapLinearMapIdentitySurface.boundaryNotPositiveSpectralWeightTheorem

/-- Readiness theorem for the range-map / linear-map identity layer. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_range_map_linear_map_identity_surface_ready :
    concreteAnalyticSpineL2MathlibFinNSynthesisRangeMapLinearMapIdentitySurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinNSynthesisRangeMapLinearMapIdentitySurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_n_synthesis_range_map_equiv_linear_equiv_bridge_surface_ready <|
      And.intro concrete_l2_mathlib_fin_n_synthesis_range_map_linear_map_identity_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial trivial

/-- Hard-residual boundary marker for the range-map / linear-map identity layer. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisRangeMapLinearMapIdentityHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisRangeMapLinearMapIdentitySurfaceReady

/-- Hard-residual boundary theorem for the range-map / linear-map identity layer. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_range_map_linear_map_identity_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinNSynthesisRangeMapLinearMapIdentityHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_n_synthesis_range_map_linear_map_identity_surface_ready

end

end MathlibAnalytic
end MGAP4D
