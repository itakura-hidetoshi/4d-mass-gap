import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinNSynthesisBidirectionalEquiv

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- The range-local synthesis equivalence is bijective as a function. -/
theorem concrete_l2_mathlib_fin_n_synthesis_range_equiv_bijective
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) :
    Function.Bijective (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ) := by
  constructor
  · intro c d hcd
    have hleft := concrete_l2_mathlib_fin_n_synthesis_range_equiv_left_inverse hφ
    exact hleft.injective hcd
  · intro v
    refine ⟨concreteL2MathlibFinNSynthesisRangeCoordinatesOfInjective hφ v, ?_⟩
    exact concrete_l2_mathlib_fin_n_synthesis_range_equiv_right_inverse hφ v

/-- The coordinate reconstruction map is bijective as a function. -/
theorem concrete_l2_mathlib_fin_n_synthesis_coordinates_bijective
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) :
    Function.Bijective (concreteL2MathlibFinNSynthesisRangeCoordinatesOfInjective hφ) := by
  constructor
  · intro v w hvw
    have hright := concrete_l2_mathlib_fin_n_synthesis_range_equiv_right_inverse hφ
    calc
      v = concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ
            (concreteL2MathlibFinNSynthesisRangeCoordinatesOfInjective hφ v) :=
          (hright v).symm
      _ = concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ
            (concreteL2MathlibFinNSynthesisRangeCoordinatesOfInjective hφ w) := by
          rw [hvw]
      _ = w := hright w
  · intro c
    refine ⟨concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ c, ?_⟩
    exact concrete_l2_mathlib_fin_n_synthesis_range_equiv_left_inverse hφ c

/-- Bijective-map adapter for the general `Fin m` range-local carrier. -/
def concreteL2MathlibFinNSynthesisBijectiveMapsAdapter : Prop :=
  ∀ {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ),
    Function.Bijective (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ) ∧
    Function.Bijective (concreteL2MathlibFinNSynthesisRangeCoordinatesOfInjective hφ)

/-- Adapter theorem for the bijective-map layer. -/
theorem concrete_l2_mathlib_fin_n_synthesis_bijective_maps_adapter_ready :
    concreteL2MathlibFinNSynthesisBijectiveMapsAdapter := by
  intro m φ hφ
  exact ⟨
    concrete_l2_mathlib_fin_n_synthesis_range_equiv_bijective hφ,
    concrete_l2_mathlib_fin_n_synthesis_coordinates_bijective hφ⟩

/-- Surface for the bijective-map layer. -/
structure ConcreteL2MathlibFinNSynthesisBijectiveMapsSurface where
  bidirectionalEquivReady : concreteAnalyticSpineL2MathlibFinNSynthesisBidirectionalEquivSurfaceReady
  bijectiveMapsAdapter : concreteL2MathlibFinNSynthesisBijectiveMapsAdapter
  boundaryRangeLocalOnly : Prop
  boundaryNotAmbientBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop
  boundaryNotPositiveSpectralWeightTheorem : Prop

/-- Concrete bijective-map surface. -/
def concreteL2MathlibFinNSynthesisBijectiveMapsSurface :
    ConcreteL2MathlibFinNSynthesisBijectiveMapsSurface :=
  { bidirectionalEquivReady :=
      concrete_analytic_spine_l2_mathlib_fin_n_synthesis_bidirectional_equiv_surface_ready
    bijectiveMapsAdapter :=
      concrete_l2_mathlib_fin_n_synthesis_bijective_maps_adapter_ready
    boundaryRangeLocalOnly := True
    boundaryNotAmbientBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True
    boundaryNotPositiveSpectralWeightTheorem := True }

/-- Readiness predicate for the bijective-map surface. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisBijectiveMapsSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisBidirectionalEquivSurfaceReady ∧
  concreteL2MathlibFinNSynthesisBijectiveMapsAdapter ∧
  concreteL2MathlibFinNSynthesisBijectiveMapsSurface.boundaryRangeLocalOnly ∧
  concreteL2MathlibFinNSynthesisBijectiveMapsSurface.boundaryNotAmbientBasisTheorem ∧
  concreteL2MathlibFinNSynthesisBijectiveMapsSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinNSynthesisBijectiveMapsSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinNSynthesisBijectiveMapsSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinNSynthesisBijectiveMapsSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinNSynthesisBijectiveMapsSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinNSynthesisBijectiveMapsSurface.boundaryNotSpectralAtomTheorem ∧
  concreteL2MathlibFinNSynthesisBijectiveMapsSurface.boundaryNotPositiveSpectralWeightTheorem

/-- Readiness theorem for the bijective-map surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_bijective_maps_surface_ready :
    concreteAnalyticSpineL2MathlibFinNSynthesisBijectiveMapsSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinNSynthesisBijectiveMapsSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_n_synthesis_bidirectional_equiv_surface_ready <|
      And.intro concrete_l2_mathlib_fin_n_synthesis_bijective_maps_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial trivial

/-- Hard-residual boundary marker for the bijective-map surface. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisBijectiveMapsHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisBijectiveMapsSurfaceReady

/-- Hard-residual boundary theorem for the bijective-map surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_bijective_maps_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinNSynthesisBijectiveMapsHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_n_synthesis_bijective_maps_surface_ready

end

end MathlibAnalytic
end MGAP4D
