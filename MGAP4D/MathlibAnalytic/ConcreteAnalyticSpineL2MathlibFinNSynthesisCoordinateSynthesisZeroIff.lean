import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinNSynthesisCoordinateSynthesisEqualityIff

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- A finite coordinate-unit synthesis value is zero iff all coefficients are
zero. -/
theorem concrete_l2_mathlib_fin_n_synthesis_sum_eq_zero_iff_coefficients_eq_zero
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) (c : Fin m → ℝ) :
    ((∑ i : Fin m, c i • concreteL2MathlibUnit (φ i) : lp (fun _ : ℕ => ℝ) 2) = 0) ↔
      c = 0 := by
  have hmain := concrete_l2_mathlib_fin_n_synthesis_sum_eq_sum_iff_coefficients_eq hφ c 0
  simpa using hmain

/-- Pointwise zero form for finite coordinate-unit synthesis values. -/
theorem concrete_l2_mathlib_fin_n_synthesis_sum_eq_zero_iff_coefficients_eq_zero_pointwise
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) (c : Fin m → ℝ) :
    ((∑ i : Fin m, c i • concreteL2MathlibUnit (φ i) : lp (fun _ : ℕ => ℝ) 2) = 0) ↔
      ∀ i : Fin m, c i = 0 := by
  constructor
  · intro h i
    have hc := (concrete_l2_mathlib_fin_n_synthesis_sum_eq_zero_iff_coefficients_eq_zero hφ c).1 h
    exact congrFun hc i
  · intro hpoint
    apply (concrete_l2_mathlib_fin_n_synthesis_sum_eq_zero_iff_coefficients_eq_zero hφ c).2
    funext i
    exact hpoint i

/-- Zero synthesis value forces each selected coefficient to be zero. -/
theorem concrete_l2_mathlib_fin_n_synthesis_sum_eq_zero_coefficients_apply
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) {c : Fin m → ℝ}
    (h : (∑ i : Fin m, c i • concreteL2MathlibUnit (φ i) : lp (fun _ : ℕ => ℝ) 2) = 0)
    (i : Fin m) :
    c i = 0 := by
  exact (concrete_l2_mathlib_fin_n_synthesis_sum_eq_zero_iff_coefficients_eq_zero_pointwise hφ c).1 h i

/-- The canonical range classifier has underlying zero value iff its coefficient
function is zero. -/
theorem concrete_l2_mathlib_fin_n_synthesis_equiv_apply_val_eq_zero_iff_coefficients_eq_zero
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) (c : Fin m → ℝ) :
    ((concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ c :
      lp (fun _ : ℕ => ℝ) 2) = 0) ↔ c = 0 := by
  rw [concrete_l2_mathlib_fin_n_synthesis_equiv_apply_val_eq_sum hφ c]
  exact concrete_l2_mathlib_fin_n_synthesis_sum_eq_zero_iff_coefficients_eq_zero hφ c

/-- Adapter predicate for the finite synthesis zero-iff layer. -/
def concreteL2MathlibFinNSynthesisCoordinateSynthesisZeroIffAdapter : Prop :=
  ∀ {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) (c : Fin m → ℝ),
    ((∑ i : Fin m, c i • concreteL2MathlibUnit (φ i) : lp (fun _ : ℕ => ℝ) 2) = 0) ↔
      c = 0

/-- Adapter theorem for the finite synthesis zero-iff layer. -/
theorem concrete_l2_mathlib_fin_n_synthesis_coordinate_synthesis_zero_iff_adapter_ready :
    concreteL2MathlibFinNSynthesisCoordinateSynthesisZeroIffAdapter := by
  intro m φ hφ c
  exact concrete_l2_mathlib_fin_n_synthesis_sum_eq_zero_iff_coefficients_eq_zero hφ c

/-- Surface for the finite synthesis zero-iff layer. -/
structure ConcreteL2MathlibFinNSynthesisCoordinateSynthesisZeroIffSurface where
  coordinateSynthesisEqualityIffReady :
    concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateSynthesisEqualityIffSurfaceReady
  coordinateSynthesisZeroIffAdapter :
    concreteL2MathlibFinNSynthesisCoordinateSynthesisZeroIffAdapter
  boundaryRangeLocalOnly : Prop
  boundaryNotAmbientBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop
  boundaryNotPositiveSpectralWeightTheorem : Prop

/-- Concrete finite synthesis zero-iff surface. -/
def concreteL2MathlibFinNSynthesisCoordinateSynthesisZeroIffSurface :
    ConcreteL2MathlibFinNSynthesisCoordinateSynthesisZeroIffSurface :=
  { coordinateSynthesisEqualityIffReady :=
      concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_synthesis_equality_iff_surface_ready
    coordinateSynthesisZeroIffAdapter :=
      concrete_l2_mathlib_fin_n_synthesis_coordinate_synthesis_zero_iff_adapter_ready
    boundaryRangeLocalOnly := True
    boundaryNotAmbientBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True
    boundaryNotPositiveSpectralWeightTheorem := True }

/-- Readiness predicate for the finite synthesis zero-iff surface. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateSynthesisZeroIffSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateSynthesisEqualityIffSurfaceReady ∧
  concreteL2MathlibFinNSynthesisCoordinateSynthesisZeroIffAdapter ∧
  concreteL2MathlibFinNSynthesisCoordinateSynthesisZeroIffSurface.boundaryRangeLocalOnly ∧
  concreteL2MathlibFinNSynthesisCoordinateSynthesisZeroIffSurface.boundaryNotAmbientBasisTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateSynthesisZeroIffSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateSynthesisZeroIffSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinNSynthesisCoordinateSynthesisZeroIffSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateSynthesisZeroIffSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinNSynthesisCoordinateSynthesisZeroIffSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinNSynthesisCoordinateSynthesisZeroIffSurface.boundaryNotSpectralAtomTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateSynthesisZeroIffSurface.boundaryNotPositiveSpectralWeightTheorem

/-- Readiness theorem for the finite synthesis zero-iff surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_synthesis_zero_iff_surface_ready :
    concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateSynthesisZeroIffSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateSynthesisZeroIffSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_synthesis_equality_iff_surface_ready <|
      And.intro concrete_l2_mathlib_fin_n_synthesis_coordinate_synthesis_zero_iff_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial trivial

/-- Hard-residual boundary marker for the finite synthesis zero-iff surface. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateSynthesisZeroIffHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateSynthesisZeroIffSurfaceReady

/-- Hard-residual boundary theorem for the finite synthesis zero-iff surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_synthesis_zero_iff_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateSynthesisZeroIffHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_synthesis_zero_iff_surface_ready

end

end MathlibAnalytic
end MGAP4D
