import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRangeMapBijective

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Every vector in the finite synthesis range is obtained from a unique
coefficient function by the range-restricted synthesis map. -/
theorem concrete_l2_mathlib_fin_n_synthesis_exists_unique_coefficients_for_range_map
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ)
    (v : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ)) :
    ∃! c : Fin m → ℝ,
      concreteL2MathlibFiniteSynthesisRangeMap (Fin m)
        (concreteL2MathlibFinNSynthesisLinearMap m φ) c = v := by
  rcases concrete_l2_mathlib_fin_n_synthesis_range_map_surjective_from_linear_map_injective hφ v with
    ⟨c, hc⟩
  refine ⟨c, hc, ?_⟩
  intro d hd
  exact (concrete_l2_mathlib_fin_n_synthesis_range_map_apply_eq_iff hφ d c).1 (hd.trans hc.symm)

/-- The unique coefficient function for a range vector is its recovered
coordinate function. -/
theorem concrete_l2_mathlib_fin_n_synthesis_unique_range_map_coefficients_eq_coordinates
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ)
    (v : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ))
    {c : Fin m → ℝ}
    (hc : concreteL2MathlibFiniteSynthesisRangeMap (Fin m)
        (concreteL2MathlibFinNSynthesisLinearMap m φ) c = v) :
    c = concreteL2MathlibFinNSynthesisRangeCoordinatesOfInjective hφ v := by
  have hcoord :
      concreteL2MathlibFinNSynthesisRangeCoordinatesOfInjective hφ
        (concreteL2MathlibFiniteSynthesisRangeMap (Fin m)
          (concreteL2MathlibFinNSynthesisLinearMap m φ) c) = c := by
    exact concrete_l2_mathlib_fin_n_synthesis_coordinates_of_range_map hφ c
  rw [hc] at hcoord
  exact hcoord.symm

/-- The recovered coordinate function maps back to the original range vector
under the range-restricted synthesis map. -/
theorem concrete_l2_mathlib_fin_n_synthesis_range_map_coordinates_eq_self
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ)
    (v : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ)) :
    concreteL2MathlibFiniteSynthesisRangeMap (Fin m)
        (concreteL2MathlibFinNSynthesisLinearMap m φ)
        (concreteL2MathlibFinNSynthesisRangeCoordinatesOfInjective hφ v) = v := by
  exact concrete_l2_mathlib_fin_n_synthesis_range_coordinates_synthesize_of_injective hφ v

/-- Adapter predicate for the range-map unique-coefficients layer. -/
def concreteL2MathlibFinNSynthesisCoordinateRangeMapExistsUniqueAdapter : Prop :=
  ∀ {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ),
    ∀ v : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ),
      ∃! c : Fin m → ℝ,
        concreteL2MathlibFiniteSynthesisRangeMap (Fin m)
          (concreteL2MathlibFinNSynthesisLinearMap m φ) c = v

/-- Adapter theorem for the range-map unique-coefficients layer. -/
theorem concrete_l2_mathlib_fin_n_synthesis_coordinate_range_map_exists_unique_adapter_ready :
    concreteL2MathlibFinNSynthesisCoordinateRangeMapExistsUniqueAdapter := by
  intro m φ hφ v
  exact concrete_l2_mathlib_fin_n_synthesis_exists_unique_coefficients_for_range_map hφ v

/-- Surface for the range-map unique-coefficients layer. -/
structure ConcreteL2MathlibFinNSynthesisCoordinateRangeMapExistsUniqueSurface where
  coordinateRangeMapBijectiveReady :
    concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRangeMapBijectiveSurfaceReady
  coordinateRangeMapExistsUniqueAdapter :
    concreteL2MathlibFinNSynthesisCoordinateRangeMapExistsUniqueAdapter
  boundaryRangeLocalOnly : Prop
  boundaryNotAmbientBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop
  boundaryNotPositiveSpectralWeightTheorem : Prop

/-- Concrete range-map unique-coefficients surface. -/
def concreteL2MathlibFinNSynthesisCoordinateRangeMapExistsUniqueSurface :
    ConcreteL2MathlibFinNSynthesisCoordinateRangeMapExistsUniqueSurface :=
  { coordinateRangeMapBijectiveReady :=
      concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_range_map_bijective_surface_ready
    coordinateRangeMapExistsUniqueAdapter :=
      concrete_l2_mathlib_fin_n_synthesis_coordinate_range_map_exists_unique_adapter_ready
    boundaryRangeLocalOnly := True
    boundaryNotAmbientBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True
    boundaryNotPositiveSpectralWeightTheorem := True }

/-- Readiness predicate for the range-map unique-coefficients surface. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRangeMapExistsUniqueSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRangeMapBijectiveSurfaceReady ∧
  concreteL2MathlibFinNSynthesisCoordinateRangeMapExistsUniqueAdapter ∧
  concreteL2MathlibFinNSynthesisCoordinateRangeMapExistsUniqueSurface.boundaryRangeLocalOnly ∧
  concreteL2MathlibFinNSynthesisCoordinateRangeMapExistsUniqueSurface.boundaryNotAmbientBasisTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateRangeMapExistsUniqueSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateRangeMapExistsUniqueSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinNSynthesisCoordinateRangeMapExistsUniqueSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateRangeMapExistsUniqueSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinNSynthesisCoordinateRangeMapExistsUniqueSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinNSynthesisCoordinateRangeMapExistsUniqueSurface.boundaryNotSpectralAtomTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateRangeMapExistsUniqueSurface.boundaryNotPositiveSpectralWeightTheorem

/-- Readiness theorem for the range-map unique-coefficients surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_range_map_exists_unique_surface_ready :
    concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRangeMapExistsUniqueSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRangeMapExistsUniqueSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_range_map_bijective_surface_ready <|
      And.intro concrete_l2_mathlib_fin_n_synthesis_coordinate_range_map_exists_unique_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial trivial

/-- Hard-residual boundary marker for the range-map unique-coefficients surface. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRangeMapExistsUniqueHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRangeMapExistsUniqueSurfaceReady

/-- Hard-residual boundary theorem for the range-map unique-coefficients surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_range_map_exists_unique_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateRangeMapExistsUniqueHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_range_map_exists_unique_surface_ready

end

end MathlibAnalytic
end MGAP4D
