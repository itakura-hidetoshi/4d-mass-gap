import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinNSynthesisCoordinateLinearMapInjective

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- The range-restricted concrete `Fin m` synthesis map is bijective under an
injective selected-index map. -/
theorem concrete_l2_mathlib_fin_n_synthesis_range_map_bijective_from_linear_map_injective
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) :
    Function.Bijective
      (concreteL2MathlibFiniteSynthesisRangeMap (Fin m)
        (concreteL2MathlibFinNSynthesisLinearMap m φ)) := by
  exact concrete_l2_mathlib_fin_n_synthesis_range_map_bijective_of_injective hφ

/-- The range-restricted concrete `Fin m` synthesis map is injective. -/
theorem concrete_l2_mathlib_fin_n_synthesis_range_map_injective_from_linear_map_injective
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) :
    Function.Injective
      (concreteL2MathlibFiniteSynthesisRangeMap (Fin m)
        (concreteL2MathlibFinNSynthesisLinearMap m φ)) := by
  exact (concrete_l2_mathlib_fin_n_synthesis_range_map_bijective_from_linear_map_injective hφ).1

/-- The range-restricted concrete `Fin m` synthesis map is surjective. -/
theorem concrete_l2_mathlib_fin_n_synthesis_range_map_surjective_from_linear_map_injective
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) :
    Function.Surjective
      (concreteL2MathlibFiniteSynthesisRangeMap (Fin m)
        (concreteL2MathlibFinNSynthesisLinearMap m φ)) := by
  exact (concrete_l2_mathlib_fin_n_synthesis_range_map_bijective_from_linear_map_injective hφ).2

/-- Equality after the range-restricted synthesis map is equivalent to equality
of coefficient functions. -/
theorem concrete_l2_mathlib_fin_n_synthesis_range_map_apply_eq_iff
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) (c d : Fin m → ℝ) :
    concreteL2MathlibFiniteSynthesisRangeMap (Fin m)
        (concreteL2MathlibFinNSynthesisLinearMap m φ) c =
      concreteL2MathlibFiniteSynthesisRangeMap (Fin m)
        (concreteL2MathlibFinNSynthesisLinearMap m φ) d ↔ c = d := by
  constructor
  · intro h
    exact concrete_l2_mathlib_fin_n_synthesis_range_map_injective_from_linear_map_injective hφ h
  · intro hcd
    rw [hcd]

/-- Adapter predicate for the range-map bijectivity layer. -/
def concreteL2MathlibFinNSynthesisCoordinateRangeMapBijectiveAdapter : Prop :=
  ∀ {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ),
    Function.Bijective
      (concreteL2MathlibFiniteSynthesisRangeMap (Fin m)
        (concreteL2MathlibFinNSynthesisLinearMap m φ))

/-- Adapter theorem for the range-map bijectivity layer. -/
theorem concrete_l2_mathlib_fin_n_synthesis_coordinate_range_map_bijective_adapter_ready :
    concreteL2MathlibFinNSynthesisCoordinateRangeMapBijectiveAdapter := by
  intro m φ hφ
  exact concrete_l2_mathlib_fin_n_synthesis_range_map_bijective_from_linear_map_injective hφ

/-- Surface for the range-map bijectivity layer. -/
structure ConcreteL2MathlibFinNSynthesisCoordinateRangeMapBijectiveSurface where
  coordinateLinearMapInjectiveReady :
    concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateLinearMapInjectiveSurfaceReady
  coordinateRangeMapBijectiveAdapter :
    concreteL2MathlibFinNSynthesisCoordinateRangeMapBijectiveAdapter
  boundaryRangeLocalOnly : Prop
  boundaryNotAmbientBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop
  boundaryNotPositiveSpectralWeightTheorem : Prop

/-- Concrete range-map bijectivity surface. -/
def concreteL2MathlibFinNSynthesisCoordinateRangeMapBijectiveSurface :
    ConcreteL2MathlibFinNSynthesisCoordinateRangeMapBijectiveSurface :=
  { coordinateLinearMapInjectiveReady :=
      concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_linear_map_injective_surface_ready
    coordinateRangeMapBijectiveAdapter :=
      concrete_l2_mathlib_fin_n_synthesis_coordinate_range_map_bijective_adapter_ready
    boundaryRangeLocalOnly := True
    boundaryNotAmbientBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True
    boundaryNotPositiveSpectralWeightTheorem := True }

/-- Readiness predicate for the range-map bijectivity surface. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRangeMapBijectiveSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateLinearMapInjectiveSurfaceReady ∧
  concreteL2MathlibFinNSynthesisCoordinateRangeMapBijectiveAdapter ∧
  concreteL2MathlibFinNSynthesisCoordinateRangeMapBijectiveSurface.boundaryRangeLocalOnly ∧
  concreteL2MathlibFinNSynthesisCoordinateRangeMapBijectiveSurface.boundaryNotAmbientBasisTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateRangeMapBijectiveSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateRangeMapBijectiveSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinNSynthesisCoordinateRangeMapBijectiveSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateRangeMapBijectiveSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinNSynthesisCoordinateRangeMapBijectiveSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinNSynthesisCoordinateRangeMapBijectiveSurface.boundaryNotSpectralAtomTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateRangeMapBijectiveSurface.boundaryNotPositiveSpectralWeightTheorem

/-- Readiness theorem for the range-map bijectivity surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_range_map_bijective_surface_ready :
    concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRangeMapBijectiveSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRangeMapBijectiveSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_linear_map_injective_surface_ready <|
      And.intro concrete_l2_mathlib_fin_n_synthesis_coordinate_range_map_bijective_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial trivial

/-- Hard-residual boundary marker for the range-map bijectivity surface. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRangeMapBijectiveHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRangeMapBijectiveSurfaceReady

/-- Hard-residual boundary theorem for the range-map bijectivity surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_range_map_bijective_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRangeMapBijectiveHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_range_map_bijective_surface_ready

end

end MathlibAnalytic
end MGAP4D
