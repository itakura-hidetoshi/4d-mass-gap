import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinNSynthesisCoordinateSynthesisInjectiveValue

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Equality of finite coordinate-unit synthesis values is equivalent to equality
of coefficient functions. -/
theorem concrete_l2_mathlib_fin_n_synthesis_sum_eq_sum_iff_coefficients_eq
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) (c d : Fin m → ℝ) :
    ((∑ i : Fin m, c i • concreteL2MathlibUnit (φ i) : lp (fun _ : ℕ => ℝ) 2) =
      ∑ i : Fin m, d i • concreteL2MathlibUnit (φ i)) ↔ c = d := by
  constructor
  · intro h
    exact concrete_l2_mathlib_fin_n_synthesis_sum_eq_sum_coefficients_eq hφ h
  · intro hcd
    rw [hcd]

/-- Pointwise equality of coefficients is equivalent to equality of finite
coordinate-unit synthesis values. -/
theorem concrete_l2_mathlib_fin_n_synthesis_sum_eq_sum_iff_coefficients_eq_pointwise
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) (c d : Fin m → ℝ) :
    ((∑ i : Fin m, c i • concreteL2MathlibUnit (φ i) : lp (fun _ : ℕ => ℝ) 2) =
      ∑ i : Fin m, d i • concreteL2MathlibUnit (φ i)) ↔
      ∀ i : Fin m, c i = d i := by
  constructor
  · intro h i
    exact concrete_l2_mathlib_fin_n_synthesis_sum_eq_sum_coefficients_eq_apply hφ h i
  · intro hpoint
    apply (concrete_l2_mathlib_fin_n_synthesis_sum_eq_sum_iff_coefficients_eq hφ c d).2
    funext i
    exact hpoint i

/-- Underlying-value equality of canonical range classifiers is equivalent to
equality of coefficient functions. -/
theorem concrete_l2_mathlib_fin_n_synthesis_equiv_apply_val_eq_iff_coefficients_eq
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) (c d : Fin m → ℝ) :
    ((concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ c :
      lp (fun _ : ℕ => ℝ) 2) =
      (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ d :
        lp (fun _ : ℕ => ℝ) 2)) ↔ c = d := by
  constructor
  · intro h
    exact concrete_l2_mathlib_fin_n_synthesis_equiv_apply_val_injective hφ h
  · intro hcd
    rw [hcd]

/-- Adapter predicate for the finite synthesis equality-iff layer. -/
def concreteL2MathlibFinNSynthesisCoordinateSynthesisEqualityIffAdapter : Prop :=
  ∀ {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) (c d : Fin m → ℝ),
    ((∑ i : Fin m, c i • concreteL2MathlibUnit (φ i) : lp (fun _ : ℕ => ℝ) 2) =
      ∑ i : Fin m, d i • concreteL2MathlibUnit (φ i)) ↔ c = d

/-- Adapter theorem for the finite synthesis equality-iff layer. -/
theorem concrete_l2_mathlib_fin_n_synthesis_coordinate_synthesis_equality_iff_adapter_ready :
    concreteL2MathlibFinNSynthesisCoordinateSynthesisEqualityIffAdapter := by
  intro m φ hφ c d
  exact concrete_l2_mathlib_fin_n_synthesis_sum_eq_sum_iff_coefficients_eq hφ c d

/-- Surface for the finite synthesis equality-iff layer. -/
structure ConcreteL2MathlibFinNSynthesisCoordinateSynthesisEqualityIffSurface where
  coordinateSynthesisInjectiveValueReady :
    concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateSynthesisInjectiveValueSurfaceReady
  coordinateSynthesisEqualityIffAdapter :
    concreteL2MathlibFinNSynthesisCoordinateSynthesisEqualityIffAdapter
  boundaryRangeLocalOnly : Prop
  boundaryNotAmbientBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop
  boundaryNotPositiveSpectralWeightTheorem : Prop

/-- Concrete finite synthesis equality-iff surface. -/
def concreteL2MathlibFinNSynthesisCoordinateSynthesisEqualityIffSurface :
    ConcreteL2MathlibFinNSynthesisCoordinateSynthesisEqualityIffSurface :=
  { coordinateSynthesisInjectiveValueReady :=
      concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_synthesis_injective_value_surface_ready
    coordinateSynthesisEqualityIffAdapter :=
      concrete_l2_mathlib_fin_n_synthesis_coordinate_synthesis_equality_iff_adapter_ready
    boundaryRangeLocalOnly := True
    boundaryNotAmbientBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True
    boundaryNotPositiveSpectralWeightTheorem := True }

/-- Readiness predicate for the finite synthesis equality-iff surface. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateSynthesisEqualityIffSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateSynthesisInjectiveValueSurfaceReady ∧
  concreteL2MathlibFinNSynthesisCoordinateSynthesisEqualityIffAdapter ∧
  concreteL2MathlibFinNSynthesisCoordinateSynthesisEqualityIffSurface.boundaryRangeLocalOnly ∧
  concreteL2MathlibFinNSynthesisCoordinateSynthesisEqualityIffSurface.boundaryNotAmbientBasisTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateSynthesisEqualityIffSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateSynthesisEqualityIffSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinNSynthesisCoordinateSynthesisEqualityIffSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateSynthesisEqualityIffSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinNSynthesisCoordinateSynthesisEqualityIffSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinNSynthesisCoordinateSynthesisEqualityIffSurface.boundaryNotSpectralAtomTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateSynthesisEqualityIffSurface.boundaryNotPositiveSpectralWeightTheorem

/-- Readiness theorem for the finite synthesis equality-iff surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_synthesis_equality_iff_surface_ready :
    concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateSynthesisEqualityIffSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateSynthesisEqualityIffSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_synthesis_injective_value_surface_ready <|
      And.intro concrete_l2_mathlib_fin_n_synthesis_coordinate_synthesis_equality_iff_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial trivial

/-- Hard-residual boundary marker for the finite synthesis equality-iff surface. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateSynthesisEqualityIffHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateSynthesisEqualityIffSurfaceReady

/-- Hard-residual boundary theorem for the finite synthesis equality-iff surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_synthesis_equality_iff_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateSynthesisEqualityIffHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_synthesis_equality_iff_surface_ready

end

end MathlibAnalytic
end MGAP4D
