import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRangeMapExistsUnique

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- The coefficient function chosen from the unique range-map representation of
a range vector. -/
def concreteL2MathlibFinNSynthesisChosenRangeMapCoefficients
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ)
    (v : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ)) : Fin m → ℝ :=
  Classical.choose
    (concrete_l2_mathlib_fin_n_synthesis_exists_unique_coefficients_for_range_map hφ v)

/-- The chosen coefficient function synthesizes back to the original range
vector. -/
theorem concrete_l2_mathlib_fin_n_synthesis_range_map_chosen_coefficients_eq_self
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ)
    (v : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ)) :
    concreteL2MathlibFiniteSynthesisRangeMap (Fin m)
        (concreteL2MathlibFinNSynthesisLinearMap m φ)
        (concreteL2MathlibFinNSynthesisChosenRangeMapCoefficients hφ v) = v := by
  exact (Classical.choose_spec
    (concrete_l2_mathlib_fin_n_synthesis_exists_unique_coefficients_for_range_map hφ v)).1

/-- Any coefficient function synthesizing to a range vector is equal to the
chosen coefficient function for that vector. -/
theorem concrete_l2_mathlib_fin_n_synthesis_coefficients_eq_chosen_of_range_map_eq
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ)
    {v : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ)}
    {c : Fin m → ℝ}
    (hc : concreteL2MathlibFiniteSynthesisRangeMap (Fin m)
        (concreteL2MathlibFinNSynthesisLinearMap m φ) c = v) :
    c = concreteL2MathlibFinNSynthesisChosenRangeMapCoefficients hφ v := by
  exact (Classical.choose_spec
    (concrete_l2_mathlib_fin_n_synthesis_exists_unique_coefficients_for_range_map hφ v)).2 c hc

/-- The chosen coefficient function for `rangeMap c` is exactly `c`. -/
theorem concrete_l2_mathlib_fin_n_synthesis_chosen_coefficients_of_range_map_eq
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) (c : Fin m → ℝ) :
    concreteL2MathlibFinNSynthesisChosenRangeMapCoefficients hφ
      (concreteL2MathlibFiniteSynthesisRangeMap (Fin m)
        (concreteL2MathlibFinNSynthesisLinearMap m φ) c) = c := by
  symm
  exact concrete_l2_mathlib_fin_n_synthesis_coefficients_eq_chosen_of_range_map_eq hφ rfl

/-- Pointwise form of the chosen-coefficients roundtrip for `rangeMap c`. -/
theorem concrete_l2_mathlib_fin_n_synthesis_chosen_coefficients_of_range_map_eq_apply
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) (c : Fin m → ℝ)
    (i : Fin m) :
    concreteL2MathlibFinNSynthesisChosenRangeMapCoefficients hφ
      (concreteL2MathlibFiniteSynthesisRangeMap (Fin m)
        (concreteL2MathlibFinNSynthesisLinearMap m φ) c) i = c i := by
  exact congrFun
    (concrete_l2_mathlib_fin_n_synthesis_chosen_coefficients_of_range_map_eq hφ c) i

/-- Adapter predicate for the chosen range-map inverse layer. -/
def concreteL2MathlibFinNSynthesisCoordinateRangeMapChosenInverseAdapter : Prop :=
  ∀ {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ),
    ∀ v : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ),
      concreteL2MathlibFiniteSynthesisRangeMap (Fin m)
        (concreteL2MathlibFinNSynthesisLinearMap m φ)
        (concreteL2MathlibFinNSynthesisChosenRangeMapCoefficients hφ v) = v

/-- Adapter theorem for the chosen range-map inverse layer. -/
theorem concrete_l2_mathlib_fin_n_synthesis_coordinate_range_map_chosen_inverse_adapter_ready :
    concreteL2MathlibFinNSynthesisCoordinateRangeMapChosenInverseAdapter := by
  intro m φ hφ v
  exact concrete_l2_mathlib_fin_n_synthesis_range_map_chosen_coefficients_eq_self hφ v

/-- Surface for the chosen range-map inverse layer. -/
structure ConcreteL2MathlibFinNSynthesisCoordinateRangeMapChosenInverseSurface where
  coordinateRangeMapExistsUniqueReady :
    concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRangeMapExistsUniqueSurfaceReady
  coordinateRangeMapChosenInverseAdapter :
    concreteL2MathlibFinNSynthesisCoordinateRangeMapChosenInverseAdapter
  boundaryRangeLocalOnly : Prop
  boundaryNotAmbientBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop
  boundaryNotPositiveSpectralWeightTheorem : Prop

/-- Concrete chosen range-map inverse surface. -/
def concreteL2MathlibFinNSynthesisCoordinateRangeMapChosenInverseSurface :
    ConcreteL2MathlibFinNSynthesisCoordinateRangeMapChosenInverseSurface :=
  { coordinateRangeMapExistsUniqueReady :=
      concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_range_map_exists_unique_surface_ready
    coordinateRangeMapChosenInverseAdapter :=
      concrete_l2_mathlib_fin_n_synthesis_coordinate_range_map_chosen_inverse_adapter_ready
    boundaryRangeLocalOnly := True
    boundaryNotAmbientBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True
    boundaryNotPositiveSpectralWeightTheorem := True }

/-- Readiness predicate for the chosen range-map inverse surface. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRangeMapChosenInverseSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRangeMapExistsUniqueSurfaceReady ∧
  concreteL2MathlibFinNSynthesisCoordinateRangeMapChosenInverseAdapter ∧
  concreteL2MathlibFinNSynthesisCoordinateRangeMapChosenInverseSurface.boundaryRangeLocalOnly ∧
  concreteL2MathlibFinNSynthesisCoordinateRangeMapChosenInverseSurface.boundaryNotAmbientBasisTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateRangeMapChosenInverseSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateRangeMapChosenInverseSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinNSynthesisCoordinateRangeMapChosenInverseSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateRangeMapChosenInverseSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinNSynthesisCoordinateRangeMapChosenInverseSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinNSynthesisCoordinateRangeMapChosenInverseSurface.boundaryNotSpectralAtomTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateRangeMapChosenInverseSurface.boundaryNotPositiveSpectralWeightTheorem

/-- Readiness theorem for the chosen range-map inverse surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_range_map_chosen_inverse_surface_ready :
    concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRangeMapChosenInverseSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRangeMapChosenInverseSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_range_map_exists_unique_surface_ready <|
      And.intro concrete_l2_mathlib_fin_n_synthesis_coordinate_range_map_chosen_inverse_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial trivial

/-- Hard-residual boundary marker for the chosen range-map inverse surface. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRangeMapChosenInverseHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRangeMapChosenInverseSurfaceReady

/-- Hard-residual boundary theorem for the chosen range-map inverse surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_range_map_chosen_inverse_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRangeMapChosenInverseHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_range_map_chosen_inverse_surface_ready

end

end MathlibAnalytic
end MGAP4D
