import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRangeMapChosenInverse

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- The chosen coefficient map is a left inverse of the range-restricted
synthesis map. -/
theorem concrete_l2_mathlib_fin_n_synthesis_chosen_left_inverse_range_map
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) :
    Function.LeftInverse
      (concreteL2MathlibFinNSynthesisChosenRangeMapCoefficients hφ)
      (concreteL2MathlibFiniteSynthesisRangeMap (Fin m)
        (concreteL2MathlibFinNSynthesisLinearMap m φ)) := by
  intro c
  exact concrete_l2_mathlib_fin_n_synthesis_chosen_coefficients_of_range_map_eq hφ c

/-- The chosen coefficient map is a right inverse of the range-restricted
synthesis map. -/
theorem concrete_l2_mathlib_fin_n_synthesis_chosen_right_inverse_range_map
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) :
    Function.RightInverse
      (concreteL2MathlibFinNSynthesisChosenRangeMapCoefficients hφ)
      (concreteL2MathlibFiniteSynthesisRangeMap (Fin m)
        (concreteL2MathlibFinNSynthesisLinearMap m φ)) := by
  intro v
  exact concrete_l2_mathlib_fin_n_synthesis_range_map_chosen_coefficients_eq_self hφ v

/-- The chosen coefficient map is bijective. -/
theorem concrete_l2_mathlib_fin_n_synthesis_chosen_coefficients_bijective
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) :
    Function.Bijective
      (concreteL2MathlibFinNSynthesisChosenRangeMapCoefficients hφ :
        concreteL2MathlibFiniteSynthesisRange (Fin m)
          (concreteL2MathlibFinNSynthesisLinearMap m φ) → Fin m → ℝ) := by
  constructor
  · intro v w h
    calc
      v = concreteL2MathlibFiniteSynthesisRangeMap (Fin m)
            (concreteL2MathlibFinNSynthesisLinearMap m φ)
            (concreteL2MathlibFinNSynthesisChosenRangeMapCoefficients hφ v) :=
        (concrete_l2_mathlib_fin_n_synthesis_range_map_chosen_coefficients_eq_self hφ v).symm
      _ = concreteL2MathlibFiniteSynthesisRangeMap (Fin m)
            (concreteL2MathlibFinNSynthesisLinearMap m φ)
            (concreteL2MathlibFinNSynthesisChosenRangeMapCoefficients hφ w) := by rw [h]
      _ = w := concrete_l2_mathlib_fin_n_synthesis_range_map_chosen_coefficients_eq_self hφ w
  · intro c
    refine ⟨concreteL2MathlibFiniteSynthesisRangeMap (Fin m)
        (concreteL2MathlibFinNSynthesisLinearMap m φ) c, ?_⟩
    exact concrete_l2_mathlib_fin_n_synthesis_chosen_coefficients_of_range_map_eq hφ c

/-- The range map is bijective, recovered from the chosen inverse laws. -/
theorem concrete_l2_mathlib_fin_n_synthesis_range_map_bijective_from_chosen_inverse
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) :
    Function.Bijective
      (concreteL2MathlibFiniteSynthesisRangeMap (Fin m)
        (concreteL2MathlibFinNSynthesisLinearMap m φ)) := by
  exact concrete_l2_mathlib_fin_n_synthesis_range_map_bijective_from_linear_map_injective hφ

/-- Adapter predicate for the chosen inverse-laws layer. -/
def concreteL2MathlibFinNSynthesisCoordinateRangeMapInverseLawsAdapter : Prop :=
  ∀ {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ),
    Function.LeftInverse
      (concreteL2MathlibFinNSynthesisChosenRangeMapCoefficients hφ)
      (concreteL2MathlibFiniteSynthesisRangeMap (Fin m)
        (concreteL2MathlibFinNSynthesisLinearMap m φ)) ∧
    Function.RightInverse
      (concreteL2MathlibFinNSynthesisChosenRangeMapCoefficients hφ)
      (concreteL2MathlibFiniteSynthesisRangeMap (Fin m)
        (concreteL2MathlibFinNSynthesisLinearMap m φ))

/-- Adapter theorem for the chosen inverse-laws layer. -/
theorem concrete_l2_mathlib_fin_n_synthesis_coordinate_range_map_inverse_laws_adapter_ready :
    concreteL2MathlibFinNSynthesisCoordinateRangeMapInverseLawsAdapter := by
  intro m φ hφ
  exact ⟨concrete_l2_mathlib_fin_n_synthesis_chosen_left_inverse_range_map hφ,
    concrete_l2_mathlib_fin_n_synthesis_chosen_right_inverse_range_map hφ⟩

/-- Surface for the chosen inverse-laws layer. -/
structure ConcreteL2MathlibFinNSynthesisCoordinateRangeMapInverseLawsSurface where
  coordinateRangeMapChosenInverseReady :
    concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRangeMapChosenInverseSurfaceReady
  coordinateRangeMapInverseLawsAdapter :
    concreteL2MathlibFinNSynthesisCoordinateRangeMapInverseLawsAdapter
  boundaryRangeLocalOnly : Prop
  boundaryNotAmbientBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop
  boundaryNotPositiveSpectralWeightTheorem : Prop

/-- Concrete chosen inverse-laws surface. -/
def concreteL2MathlibFinNSynthesisCoordinateRangeMapInverseLawsSurface :
    ConcreteL2MathlibFinNSynthesisCoordinateRangeMapInverseLawsSurface :=
  { coordinateRangeMapChosenInverseReady :=
      concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_range_map_chosen_inverse_surface_ready
    coordinateRangeMapInverseLawsAdapter :=
      concrete_l2_mathlib_fin_n_synthesis_coordinate_range_map_inverse_laws_adapter_ready
    boundaryRangeLocalOnly := True
    boundaryNotAmbientBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True
    boundaryNotPositiveSpectralWeightTheorem := True }

/-- Readiness predicate for the chosen inverse-laws surface. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRangeMapInverseLawsSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRangeMapChosenInverseSurfaceReady ∧
  concreteL2MathlibFinNSynthesisCoordinateRangeMapInverseLawsAdapter ∧
  concreteL2MathlibFinNSynthesisCoordinateRangeMapInverseLawsSurface.boundaryRangeLocalOnly ∧
  concreteL2MathlibFinNSynthesisCoordinateRangeMapInverseLawsSurface.boundaryNotAmbientBasisTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateRangeMapInverseLawsSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateRangeMapInverseLawsSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinNSynthesisCoordinateRangeMapInverseLawsSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateRangeMapInverseLawsSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinNSynthesisCoordinateRangeMapInverseLawsSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinNSynthesisCoordinateRangeMapInverseLawsSurface.boundaryNotSpectralAtomTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateRangeMapInverseLawsSurface.boundaryNotPositiveSpectralWeightTheorem

/-- Readiness theorem for the chosen inverse-laws surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_range_map_inverse_laws_surface_ready :
    concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRangeMapInverseLawsSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRangeMapInverseLawsSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_range_map_chosen_inverse_surface_ready <|
      And.intro concrete_l2_mathlib_fin_n_synthesis_coordinate_range_map_inverse_laws_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial trivial

/-- Hard-residual boundary marker for the chosen inverse-laws surface. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRangeMapInverseLawsHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRangeMapInverseLawsSurfaceReady

/-- Hard-residual boundary theorem for the chosen inverse-laws surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_range_map_inverse_laws_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRangeMapInverseLawsHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_range_map_inverse_laws_surface_ready

end

end MathlibAnalytic
end MGAP4D
