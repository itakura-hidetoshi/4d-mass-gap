import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRangeMapInverseLaws

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- The equivalence between finite coefficient functions and the finite synthesis
range induced by the range-restricted synthesis map. -/
def concreteL2MathlibFinNSynthesisRangeMapEquiv
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) :
    (Fin m → ℝ) ≃ concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ) where
  toFun := concreteL2MathlibFiniteSynthesisRangeMap (Fin m)
    (concreteL2MathlibFinNSynthesisLinearMap m φ)
  invFun := concreteL2MathlibFinNSynthesisChosenRangeMapCoefficients hφ
  left_inv := concrete_l2_mathlib_fin_n_synthesis_chosen_left_inverse_range_map hφ
  right_inv := concrete_l2_mathlib_fin_n_synthesis_chosen_right_inverse_range_map hφ

/-- The equivalence applies as the range-restricted synthesis map. -/
theorem concrete_l2_mathlib_fin_n_synthesis_range_map_equiv_apply
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) (c : Fin m → ℝ) :
    concreteL2MathlibFinNSynthesisRangeMapEquiv hφ c =
      concreteL2MathlibFiniteSynthesisRangeMap (Fin m)
        (concreteL2MathlibFinNSynthesisLinearMap m φ) c := rfl

/-- The inverse of the range-map equivalence is the chosen coefficient map. -/
theorem concrete_l2_mathlib_fin_n_synthesis_range_map_equiv_symm_apply
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ)
    (v : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ)) :
    (concreteL2MathlibFinNSynthesisRangeMapEquiv hφ).symm v =
      concreteL2MathlibFinNSynthesisChosenRangeMapCoefficients hφ v := rfl

/-- The range-map equivalence followed by its inverse is identity on coefficient
functions. -/
theorem concrete_l2_mathlib_fin_n_synthesis_range_map_equiv_symm_apply_apply
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) (c : Fin m → ℝ) :
    (concreteL2MathlibFinNSynthesisRangeMapEquiv hφ).symm
      (concreteL2MathlibFinNSynthesisRangeMapEquiv hφ c) = c := by
  exact concrete_l2_mathlib_fin_n_synthesis_chosen_coefficients_of_range_map_eq hφ c

/-- The inverse of the range-map equivalence followed by the equivalence is
identity on the finite synthesis range. -/
theorem concrete_l2_mathlib_fin_n_synthesis_range_map_equiv_apply_symm_apply
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ)
    (v : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ)) :
    concreteL2MathlibFinNSynthesisRangeMapEquiv hφ
      ((concreteL2MathlibFinNSynthesisRangeMapEquiv hφ).symm v) = v := by
  exact concrete_l2_mathlib_fin_n_synthesis_range_map_chosen_coefficients_eq_self hφ v

/-- Adapter predicate for the range-map equivalence layer. -/
def concreteL2MathlibFinNSynthesisCoordinateRangeMapEquivAdapter : Prop :=
  ∀ {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) (c : Fin m → ℝ),
    (concreteL2MathlibFinNSynthesisRangeMapEquiv hφ).symm
      (concreteL2MathlibFinNSynthesisRangeMapEquiv hφ c) = c

/-- Adapter theorem for the range-map equivalence layer. -/
theorem concrete_l2_mathlib_fin_n_synthesis_coordinate_range_map_equiv_adapter_ready :
    concreteL2MathlibFinNSynthesisCoordinateRangeMapEquivAdapter := by
  intro m φ hφ c
  exact concrete_l2_mathlib_fin_n_synthesis_range_map_equiv_symm_apply_apply hφ c

/-- Surface for the range-map equivalence layer. -/
structure ConcreteL2MathlibFinNSynthesisCoordinateRangeMapEquivSurface where
  coordinateRangeMapInverseLawsReady :
    concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRangeMapInverseLawsSurfaceReady
  coordinateRangeMapEquivAdapter :
    concreteL2MathlibFinNSynthesisCoordinateRangeMapEquivAdapter
  boundaryRangeLocalOnly : Prop
  boundaryNotAmbientBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop
  boundaryNotPositiveSpectralWeightTheorem : Prop

/-- Concrete range-map equivalence surface. -/
def concreteL2MathlibFinNSynthesisCoordinateRangeMapEquivSurface :
    ConcreteL2MathlibFinNSynthesisCoordinateRangeMapEquivSurface :=
  { coordinateRangeMapInverseLawsReady :=
      concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_range_map_inverse_laws_surface_ready
    coordinateRangeMapEquivAdapter :=
      concrete_l2_mathlib_fin_n_synthesis_coordinate_range_map_equiv_adapter_ready
    boundaryRangeLocalOnly := True
    boundaryNotAmbientBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True
    boundaryNotPositiveSpectralWeightTheorem := True }

/-- Readiness predicate for the range-map equivalence surface. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRangeMapEquivSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRangeMapInverseLawsSurfaceReady ∧
  concreteL2MathlibFinNSynthesisCoordinateRangeMapEquivAdapter ∧
  concreteL2MathlibFinNSynthesisCoordinateRangeMapEquivSurface.boundaryRangeLocalOnly ∧
  concreteL2MathlibFinNSynthesisCoordinateRangeMapEquivSurface.boundaryNotAmbientBasisTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateRangeMapEquivSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateRangeMapEquivSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinNSynthesisCoordinateRangeMapEquivSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateRangeMapEquivSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinNSynthesisCoordinateRangeMapEquivSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinNSynthesisCoordinateRangeMapEquivSurface.boundaryNotSpectralAtomTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateRangeMapEquivSurface.boundaryNotPositiveSpectralWeightTheorem

/-- Readiness theorem for the range-map equivalence surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_range_map_equiv_surface_ready :
    concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRangeMapEquivSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRangeMapEquivSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_range_map_inverse_laws_surface_ready <|
      And.intro concrete_l2_mathlib_fin_n_synthesis_coordinate_range_map_equiv_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial trivial

/-- Hard-residual boundary marker for the range-map equivalence surface. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRangeMapEquivHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRangeMapEquivSurfaceReady

/-- Hard-residual boundary theorem for the range-map equivalence surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_range_map_equiv_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRangeMapEquivHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_range_map_equiv_surface_ready

end

end MathlibAnalytic
end MGAP4D
