import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinNSynthesisCoordinateSumUniqueness

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Equality of two finite coordinate-unit synthesis sums forces equality of the
coefficient functions. -/
theorem concrete_l2_mathlib_fin_n_synthesis_sum_eq_sum_coefficients_eq
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) {c d : Fin m → ℝ}
    (h : (∑ i : Fin m, c i • concreteL2MathlibUnit (φ i) : lp (fun _ : ℕ => ℝ) 2) =
      ∑ i : Fin m, d i • concreteL2MathlibUnit (φ i)) :
    c = d := by
  let v := concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ c
  have hc : (v : lp (fun _ : ℕ => ℝ) 2) =
      ∑ i : Fin m, c i • concreteL2MathlibUnit (φ i) :=
    concrete_l2_mathlib_fin_n_synthesis_equiv_apply_val_eq_sum hφ c
  have hd : (v : lp (fun _ : ℕ => ℝ) 2) =
      ∑ i : Fin m, d i • concreteL2MathlibUnit (φ i) := by
    rw [hc]
    exact h
  exact concrete_l2_mathlib_fin_n_synthesis_sum_coefficients_unique_for_range_vector hφ hc hd

/-- Pointwise coefficient equality from equality of two finite coordinate-unit
synthesis sums. -/
theorem concrete_l2_mathlib_fin_n_synthesis_sum_eq_sum_coefficients_eq_apply
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) {c d : Fin m → ℝ}
    (h : (∑ i : Fin m, c i • concreteL2MathlibUnit (φ i) : lp (fun _ : ℕ => ℝ) 2) =
      ∑ i : Fin m, d i • concreteL2MathlibUnit (φ i))
    (i : Fin m) :
    c i = d i := by
  exact congrFun (concrete_l2_mathlib_fin_n_synthesis_sum_eq_sum_coefficients_eq hφ h) i

/-- The finite coordinate-unit synthesis value map is injective. -/
theorem concrete_l2_mathlib_fin_n_synthesis_value_map_injective
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) :
    Function.Injective
      (fun c : Fin m → ℝ =>
        (∑ i : Fin m, c i • concreteL2MathlibUnit (φ i) : lp (fun _ : ℕ => ℝ) 2)) := by
  intro c d h
  exact concrete_l2_mathlib_fin_n_synthesis_sum_eq_sum_coefficients_eq hφ h

/-- The canonical range equivalence is injective after forgetting to the
underlying `ℓ²` value. -/
theorem concrete_l2_mathlib_fin_n_synthesis_equiv_apply_val_injective
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) :
    Function.Injective
      (fun c : Fin m → ℝ =>
        (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ c :
          lp (fun _ : ℕ => ℝ) 2)) := by
  intro c d h
  have hsums :
      (∑ i : Fin m, c i • concreteL2MathlibUnit (φ i) : lp (fun _ : ℕ => ℝ) 2) =
        ∑ i : Fin m, d i • concreteL2MathlibUnit (φ i) := by
    rw [← concrete_l2_mathlib_fin_n_synthesis_equiv_apply_val_eq_sum hφ c]
    rw [← concrete_l2_mathlib_fin_n_synthesis_equiv_apply_val_eq_sum hφ d]
    exact h
  exact concrete_l2_mathlib_fin_n_synthesis_sum_eq_sum_coefficients_eq hφ hsums

/-- Adapter predicate for the finite synthesis value-injectivity layer. -/
def concreteL2MathlibFinNSynthesisCoordinateSynthesisInjectiveValueAdapter : Prop :=
  ∀ {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ),
    Function.Injective
      (fun c : Fin m → ℝ =>
        (∑ i : Fin m, c i • concreteL2MathlibUnit (φ i) : lp (fun _ : ℕ => ℝ) 2))

/-- Adapter theorem for the finite synthesis value-injectivity layer. -/
theorem concrete_l2_mathlib_fin_n_synthesis_coordinate_synthesis_injective_value_adapter_ready :
    concreteL2MathlibFinNSynthesisCoordinateSynthesisInjectiveValueAdapter := by
  intro m φ hφ
  exact concrete_l2_mathlib_fin_n_synthesis_value_map_injective hφ

/-- Surface for the finite synthesis value-injectivity layer. -/
structure ConcreteL2MathlibFinNSynthesisCoordinateSynthesisInjectiveValueSurface where
  coordinateSumUniquenessReady : concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateSumUniquenessSurfaceReady
  coordinateSynthesisInjectiveValueAdapter :
    concreteL2MathlibFinNSynthesisCoordinateSynthesisInjectiveValueAdapter
  boundaryRangeLocalOnly : Prop
  boundaryNotAmbientBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop
  boundaryNotPositiveSpectralWeightTheorem : Prop

/-- Concrete finite synthesis value-injectivity surface. -/
def concreteL2MathlibFinNSynthesisCoordinateSynthesisInjectiveValueSurface :
    ConcreteL2MathlibFinNSynthesisCoordinateSynthesisInjectiveValueSurface :=
  { coordinateSumUniquenessReady :=
      concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_sum_uniqueness_surface_ready
    coordinateSynthesisInjectiveValueAdapter :=
      concrete_l2_mathlib_fin_n_synthesis_coordinate_synthesis_injective_value_adapter_ready
    boundaryRangeLocalOnly := True
    boundaryNotAmbientBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True
    boundaryNotPositiveSpectralWeightTheorem := True }

/-- Readiness predicate for the finite synthesis value-injectivity surface. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateSynthesisInjectiveValueSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateSumUniquenessSurfaceReady ∧
  concreteL2MathlibFinNSynthesisCoordinateSynthesisInjectiveValueAdapter ∧
  concreteL2MathlibFinNSynthesisCoordinateSynthesisInjectiveValueSurface.boundaryRangeLocalOnly ∧
  concreteL2MathlibFinNSynthesisCoordinateSynthesisInjectiveValueSurface.boundaryNotAmbientBasisTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateSynthesisInjectiveValueSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateSynthesisInjectiveValueSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinNSynthesisCoordinateSynthesisInjectiveValueSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateSynthesisInjectiveValueSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinNSynthesisCoordinateSynthesisInjectiveValueSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinNSynthesisCoordinateSynthesisInjectiveValueSurface.boundaryNotSpectralAtomTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateSynthesisInjectiveValueSurface.boundaryNotPositiveSpectralWeightTheorem

/-- Readiness theorem for the finite synthesis value-injectivity surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_synthesis_injective_value_surface_ready :
    concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateSynthesisInjectiveValueSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateSynthesisInjectiveValueSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_sum_uniqueness_surface_ready <|
      And.intro concrete_l2_mathlib_fin_n_synthesis_coordinate_synthesis_injective_value_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial trivial

/-- Hard-residual boundary marker for the finite synthesis value-injectivity surface. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateSynthesisInjectiveValueHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateSynthesisInjectiveValueSurfaceReady

/-- Hard-residual boundary theorem for the finite synthesis value-injectivity surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_synthesis_injective_value_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateSynthesisInjectiveValueHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_synthesis_injective_value_surface_ready

end

end MathlibAnalytic
end MGAP4D
