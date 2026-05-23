import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFiniteCarrierLadderSummary

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Generic range of a finite-coefficient synthesis linear map into the completed
Mathlib `ℓ²(ℕ, ℝ)` carrier.

The coefficient type `ι` is intentionally left abstract.  Later leaves can
specialize it to `Fin m` and instantiate `T` by a coordinate-unit synthesis map. -/
def concreteL2MathlibFiniteSynthesisRange (ι : Type*)
    (T : (ι → ℝ) →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 2) :
    Submodule ℝ (lp (fun _ : ℕ => ℝ) 2) :=
  LinearMap.range T

/-- The synthesis map with codomain restricted to its own range. -/
def concreteL2MathlibFiniteSynthesisRangeMap (ι : Type*)
    (T : (ι → ℝ) →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 2) :
    (ι → ℝ) →ₗ[ℝ] concreteL2MathlibFiniteSynthesisRange ι T where
  toFun c := ⟨T c, ⟨c, rfl⟩⟩
  map_add' := by
    intro c d
    exact Subtype.ext (map_add T c d)
  map_smul' := by
    intro a c
    exact Subtype.ext (map_smul T a c)

/-- The range-restricted synthesis map has the original synthesis vector as its
underlying value. -/
theorem concrete_l2_mathlib_finite_synthesis_range_map_apply_val
    (ι : Type*) (T : (ι → ℝ) →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 2) (c : ι → ℝ) :
    (concreteL2MathlibFiniteSynthesisRangeMap ι T c : lp (fun _ : ℕ => ℝ) 2) =
      T c := by
  rfl

/-- Membership in the generic synthesis range is exactly existence of a
coefficient vector whose synthesis gives the target vector. -/
theorem concrete_l2_mathlib_finite_synthesis_mem_range_iff
    (ι : Type*) (T : (ι → ℝ) →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 2)
    (v : lp (fun _ : ℕ => ℝ) 2) :
    v ∈ concreteL2MathlibFiniteSynthesisRange ι T ↔ ∃ c : ι → ℝ, T c = v := by
  rfl

/-- The range-restricted synthesis map is always surjective onto the named range. -/
theorem concrete_l2_mathlib_finite_synthesis_range_map_surjective
    (ι : Type*) (T : (ι → ℝ) →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 2) :
    Function.Surjective (concreteL2MathlibFiniteSynthesisRangeMap ι T) := by
  intro v
  rcases v.property with ⟨c, hc⟩
  exact ⟨c, Subtype.ext hc⟩

/-- If the original synthesis map is injective, then the range-restricted map is
injective. -/
theorem concrete_l2_mathlib_finite_synthesis_range_map_injective_of_injective
    (ι : Type*) (T : (ι → ℝ) →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 2)
    (hT : Function.Injective T) :
    Function.Injective (concreteL2MathlibFiniteSynthesisRangeMap ι T) := by
  intro c d hcd
  apply hT
  exact congrArg (fun v : concreteL2MathlibFiniteSynthesisRange ι T =>
    (v : lp (fun _ : ℕ => ℝ) 2)) hcd

/-- If the kernel of the original synthesis map is bottom, then the
range-restricted map is injective. -/
theorem concrete_l2_mathlib_finite_synthesis_range_map_injective_of_ker_eq_bot
    (ι : Type*) (T : (ι → ℝ) →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 2)
    (hker : LinearMap.ker T = ⊥) :
    Function.Injective (concreteL2MathlibFiniteSynthesisRangeMap ι T) := by
  have hT : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot]
    exact hker
  exact concrete_l2_mathlib_finite_synthesis_range_map_injective_of_injective ι T hT

/-- If the kernel of the original synthesis map is bottom, then the
range-restricted synthesis map is bijective. -/
theorem concrete_l2_mathlib_finite_synthesis_range_map_bijective_of_ker_eq_bot
    (ι : Type*) (T : (ι → ℝ) →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 2)
    (hker : LinearMap.ker T = ⊥) :
    Function.Bijective (concreteL2MathlibFiniteSynthesisRangeMap ι T) :=
  ⟨
    concrete_l2_mathlib_finite_synthesis_range_map_injective_of_ker_eq_bot ι T hker,
    concrete_l2_mathlib_finite_synthesis_range_map_surjective ι T⟩

/-- Generic linear equivalence between a coefficient space and the range of an
injective synthesis map. -/
def concreteL2MathlibFiniteSynthesisRangeLinearEquiv (ι : Type*)
    (T : (ι → ℝ) →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 2)
    (hker : LinearMap.ker T = ⊥) :
    (ι → ℝ) ≃ₗ[ℝ] concreteL2MathlibFiniteSynthesisRange ι T :=
  LinearEquiv.ofBijective
    (concreteL2MathlibFiniteSynthesisRangeMap ι T)
    (concrete_l2_mathlib_finite_synthesis_range_map_bijective_of_ker_eq_bot ι T hker)

/-- The forward map of the generic range equivalence is the range-restricted
synthesis map. -/
theorem concrete_l2_mathlib_finite_synthesis_range_linear_equiv_apply
    (ι : Type*) (T : (ι → ℝ) →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 2)
    (hker : LinearMap.ker T = ⊥) (c : ι → ℝ) :
    concreteL2MathlibFiniteSynthesisRangeLinearEquiv ι T hker c =
      concreteL2MathlibFiniteSynthesisRangeMap ι T c := by
  rfl

/-- Generic coordinate reconstruction on the range of an injective synthesis map. -/
def concreteL2MathlibFiniteSynthesisRangeCoordinates (ι : Type*)
    (T : (ι → ℝ) →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 2)
    (hker : LinearMap.ker T = ⊥)
    (v : concreteL2MathlibFiniteSynthesisRange ι T) : ι → ℝ :=
  (concreteL2MathlibFiniteSynthesisRangeLinearEquiv ι T hker).symm v

/-- Re-synthesizing the reconstructed coordinates gives back the range vector. -/
theorem concrete_l2_mathlib_finite_synthesis_range_coordinates_synthesize
    (ι : Type*) (T : (ι → ℝ) →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 2)
    (hker : LinearMap.ker T = ⊥)
    (v : concreteL2MathlibFiniteSynthesisRange ι T) :
    concreteL2MathlibFiniteSynthesisRangeLinearEquiv ι T hker
        (concreteL2MathlibFiniteSynthesisRangeCoordinates ι T hker v) = v := by
  unfold concreteL2MathlibFiniteSynthesisRangeCoordinates
  exact (concreteL2MathlibFiniteSynthesisRangeLinearEquiv ι T hker).apply_symm_apply v

/-- Any coefficient vector synthesizing to a range vector equals the reconstructed
coordinate vector. -/
theorem concrete_l2_mathlib_finite_synthesis_range_coordinates_unique
    (ι : Type*) (T : (ι → ℝ) →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 2)
    (hker : LinearMap.ker T = ⊥)
    {v : concreteL2MathlibFiniteSynthesisRange ι T} {c : ι → ℝ}
    (hc : concreteL2MathlibFiniteSynthesisRangeLinearEquiv ι T hker c = v) :
    c = concreteL2MathlibFiniteSynthesisRangeCoordinates ι T hker v := by
  exact Eq.symm ((concreteL2MathlibFiniteSynthesisRangeLinearEquiv ι T hker).symm_apply_eq.mpr hc.symm)

/-- Generic template adapter: kernel-bottom synthesis maps give bijective range
maps and coordinate reconstruction. -/
def concreteL2MathlibFiniteSynthesisRangeTemplateAdapter : Prop :=
  ∀ (ι : Type*) (T : (ι → ℝ) →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 2),
    LinearMap.ker T = ⊥ →
      Function.Bijective (concreteL2MathlibFiniteSynthesisRangeMap ι T) ∧
      ∀ v : concreteL2MathlibFiniteSynthesisRange ι T,
        concreteL2MathlibFiniteSynthesisRangeLinearEquiv ι T ‹LinearMap.ker T = ⊥›
          (concreteL2MathlibFiniteSynthesisRangeCoordinates ι T ‹LinearMap.ker T = ⊥› v) = v

/-- Adapter theorem for the generic finite synthesis range template. -/
theorem concrete_l2_mathlib_finite_synthesis_range_template_adapter_ready :
    concreteL2MathlibFiniteSynthesisRangeTemplateAdapter := by
  intro ι T hker
  exact ⟨
    concrete_l2_mathlib_finite_synthesis_range_map_bijective_of_ker_eq_bot ι T hker,
    by intro v; exact concrete_l2_mathlib_finite_synthesis_range_coordinates_synthesize ι T hker v⟩

/-- Surface for the generic finite synthesis range template.

This is the first abstraction step beyond the `Fin 2`/`Fin 3` carrier ladder.  It
still does not prove that a coordinate-unit synthesis map has bottom kernel for
an arbitrary finite injective index map.  Instead, it proves the reusable Mathlib
range/equivalence/reconstruction mechanism once the kernel-bottom theorem is
available. -/
structure ConcreteL2MathlibFiniteSynthesisRangeTemplateSurface where
  finiteCarrierLadderReady : concreteAnalyticSpineL2MathlibFiniteCarrierLadderSummarySurfaceReady
  rangeTemplateAdapter : concreteL2MathlibFiniteSynthesisRangeTemplateAdapter
  boundaryKernelBottomForGeneralCoordinateSynthesisNotClaimed : Prop
  boundaryNotGeneralFiniteFamilyLinearIndependence : Prop
  boundaryNotBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop
  boundaryNotPositiveSpectralWeightTheorem : Prop

/-- Concrete generic finite synthesis range template surface. -/
def concreteL2MathlibFiniteSynthesisRangeTemplateSurface :
    ConcreteL2MathlibFiniteSynthesisRangeTemplateSurface :=
  { finiteCarrierLadderReady :=
      concrete_analytic_spine_l2_mathlib_finite_carrier_ladder_summary_surface_ready
    rangeTemplateAdapter :=
      concrete_l2_mathlib_finite_synthesis_range_template_adapter_ready
    boundaryKernelBottomForGeneralCoordinateSynthesisNotClaimed := True
    boundaryNotGeneralFiniteFamilyLinearIndependence := True
    boundaryNotBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True
    boundaryNotPositiveSpectralWeightTheorem := True }

/-- Readiness predicate for the generic finite synthesis range template surface. -/
def concreteAnalyticSpineL2MathlibFiniteSynthesisRangeTemplateSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFiniteCarrierLadderSummarySurfaceReady ∧
  concreteL2MathlibFiniteSynthesisRangeTemplateAdapter ∧
  concreteL2MathlibFiniteSynthesisRangeTemplateSurface.boundaryKernelBottomForGeneralCoordinateSynthesisNotClaimed ∧
  concreteL2MathlibFiniteSynthesisRangeTemplateSurface.boundaryNotGeneralFiniteFamilyLinearIndependence ∧
  concreteL2MathlibFiniteSynthesisRangeTemplateSurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibFiniteSynthesisRangeTemplateSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFiniteSynthesisRangeTemplateSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFiniteSynthesisRangeTemplateSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFiniteSynthesisRangeTemplateSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFiniteSynthesisRangeTemplateSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFiniteSynthesisRangeTemplateSurface.boundaryNotSpectralAtomTheorem ∧
  concreteL2MathlibFiniteSynthesisRangeTemplateSurface.boundaryNotPositiveSpectralWeightTheorem

/-- Readiness theorem for the generic finite synthesis range template surface. -/
theorem concrete_analytic_spine_l2_mathlib_finite_synthesis_range_template_surface_ready :
    concreteAnalyticSpineL2MathlibFiniteSynthesisRangeTemplateSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFiniteSynthesisRangeTemplateSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_finite_carrier_ladder_summary_surface_ready <|
      And.intro concrete_l2_mathlib_finite_synthesis_range_template_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial <| And.intro trivial trivial

/-- Hard-residual boundary marker for the generic finite synthesis range template. -/
def concreteAnalyticSpineL2MathlibFiniteSynthesisRangeTemplateHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFiniteSynthesisRangeTemplateSurfaceReady

/-- Hard-residual boundary theorem for the generic finite synthesis range template. -/
theorem concrete_analytic_spine_l2_mathlib_finite_synthesis_range_template_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFiniteSynthesisRangeTemplateHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_finite_synthesis_range_template_surface_ready

end

end MathlibAnalytic
end MGAP4D
