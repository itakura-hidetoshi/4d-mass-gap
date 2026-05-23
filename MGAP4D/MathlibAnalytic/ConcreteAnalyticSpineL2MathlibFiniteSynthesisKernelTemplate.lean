import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFiniteSynthesisRangeTemplate

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Zero-fiber coefficient triviality for a generic finite-coefficient synthesis
linear map.

This is the abstract hypothesis that later coordinate-unit synthesis maps must
prove from coordinate separation / finite support arguments. -/
def concreteL2MathlibFiniteSynthesisZeroFiberCoeffTrivial (ι : Type*)
    (T : (ι → ℝ) →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 2) : Prop :=
  ∀ c : ι → ℝ, T c = 0 → ∀ i : ι, c i = 0

/-- If the zero fiber is coefficient-trivial, then the synthesis map has bottom
kernel. -/
theorem concrete_l2_mathlib_finite_synthesis_ker_eq_bot_of_zero_fiber_coeff_trivial
    (ι : Type*) (T : (ι → ℝ) →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 2)
    (hzero : concreteL2MathlibFiniteSynthesisZeroFiberCoeffTrivial ι T) :
    LinearMap.ker T = ⊥ := by
  ext c
  constructor
  · intro hc
    have hTc : T c = 0 := hc
    have hcoeff : ∀ i : ι, c i = 0 := hzero c hTc
    ext i
    exact hcoeff i
  · intro hc
    have hc0 : c = 0 := by
      simpa using hc
    rw [hc0]
    simp

/-- Conversely, a bottom kernel gives coefficient-trivial zero fiber. -/
theorem concrete_l2_mathlib_finite_synthesis_zero_fiber_coeff_trivial_of_ker_eq_bot
    (ι : Type*) (T : (ι → ℝ) →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 2)
    (hker : LinearMap.ker T = ⊥) :
    concreteL2MathlibFiniteSynthesisZeroFiberCoeffTrivial ι T := by
  intro c hc i
  have hc_mem : c ∈ LinearMap.ker T := hc
  have hc_bot : c ∈ (⊥ : Submodule ℝ (ι → ℝ)) := by
    simpa [hker] using hc_mem
  have hc0 : c = 0 := by
    simpa using hc_bot
  exact congrArg (fun f : ι → ℝ => f i) hc0

/-- Kernel-bottom is equivalent to coefficient-trivial zero fiber for synthesis
maps from function coefficient spaces. -/
theorem concrete_l2_mathlib_finite_synthesis_ker_eq_bot_iff_zero_fiber_coeff_trivial
    (ι : Type*) (T : (ι → ℝ) →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 2) :
    LinearMap.ker T = ⊥ ↔ concreteL2MathlibFiniteSynthesisZeroFiberCoeffTrivial ι T := by
  constructor
  · intro hker
    exact concrete_l2_mathlib_finite_synthesis_zero_fiber_coeff_trivial_of_ker_eq_bot ι T hker
  · intro hzero
    exact concrete_l2_mathlib_finite_synthesis_ker_eq_bot_of_zero_fiber_coeff_trivial ι T hzero

/-- Zero-fiber coefficient triviality gives injectivity of the original synthesis
map. -/
theorem concrete_l2_mathlib_finite_synthesis_injective_of_zero_fiber_coeff_trivial
    (ι : Type*) (T : (ι → ℝ) →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 2)
    (hzero : concreteL2MathlibFiniteSynthesisZeroFiberCoeffTrivial ι T) :
    Function.Injective T := by
  rw [← LinearMap.ker_eq_bot]
  exact concrete_l2_mathlib_finite_synthesis_ker_eq_bot_of_zero_fiber_coeff_trivial ι T hzero

/-- Zero-fiber coefficient triviality gives bijectivity of the range-restricted
synthesis map. -/
theorem concrete_l2_mathlib_finite_synthesis_range_map_bijective_of_zero_fiber_coeff_trivial
    (ι : Type*) (T : (ι → ℝ) →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 2)
    (hzero : concreteL2MathlibFiniteSynthesisZeroFiberCoeffTrivial ι T) :
    Function.Bijective (concreteL2MathlibFiniteSynthesisRangeMap ι T) := by
  exact concrete_l2_mathlib_finite_synthesis_range_map_bijective_of_ker_eq_bot ι T
    (concrete_l2_mathlib_finite_synthesis_ker_eq_bot_of_zero_fiber_coeff_trivial ι T hzero)

/-- Zero-fiber coefficient triviality gives the generic range linear equivalence. -/
def concreteL2MathlibFiniteSynthesisRangeLinearEquivOfZeroFiberCoeffTrivial
    (ι : Type*) (T : (ι → ℝ) →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 2)
    (hzero : concreteL2MathlibFiniteSynthesisZeroFiberCoeffTrivial ι T) :
    (ι → ℝ) ≃ₗ[ℝ] concreteL2MathlibFiniteSynthesisRange ι T :=
  concreteL2MathlibFiniteSynthesisRangeLinearEquiv ι T
    (concrete_l2_mathlib_finite_synthesis_ker_eq_bot_of_zero_fiber_coeff_trivial ι T hzero)

/-- Zero-fiber coefficient triviality gives generic coordinate reconstruction on
the range. -/
def concreteL2MathlibFiniteSynthesisRangeCoordinatesOfZeroFiberCoeffTrivial
    (ι : Type*) (T : (ι → ℝ) →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 2)
    (hzero : concreteL2MathlibFiniteSynthesisZeroFiberCoeffTrivial ι T)
    (v : concreteL2MathlibFiniteSynthesisRange ι T) : ι → ℝ :=
  concreteL2MathlibFiniteSynthesisRangeCoordinates ι T
    (concrete_l2_mathlib_finite_synthesis_ker_eq_bot_of_zero_fiber_coeff_trivial ι T hzero) v

/-- Re-synthesizing the coordinates reconstructed under zero-fiber coefficient
triviality gives back the range vector. -/
theorem concrete_l2_mathlib_finite_synthesis_range_coordinates_synthesize_of_zero_fiber_coeff_trivial
    (ι : Type*) (T : (ι → ℝ) →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 2)
    (hzero : concreteL2MathlibFiniteSynthesisZeroFiberCoeffTrivial ι T)
    (v : concreteL2MathlibFiniteSynthesisRange ι T) :
    concreteL2MathlibFiniteSynthesisRangeLinearEquivOfZeroFiberCoeffTrivial ι T hzero
        (concreteL2MathlibFiniteSynthesisRangeCoordinatesOfZeroFiberCoeffTrivial ι T hzero v) = v := by
  unfold concreteL2MathlibFiniteSynthesisRangeLinearEquivOfZeroFiberCoeffTrivial
  unfold concreteL2MathlibFiniteSynthesisRangeCoordinatesOfZeroFiberCoeffTrivial
  exact concrete_l2_mathlib_finite_synthesis_range_coordinates_synthesize ι T
    (concrete_l2_mathlib_finite_synthesis_ker_eq_bot_of_zero_fiber_coeff_trivial ι T hzero) v

/-- Adapter predicate for the finite synthesis kernel template. -/
def concreteL2MathlibFiniteSynthesisKernelTemplateAdapter : Prop :=
  ∀ (ι : Type*) (T : (ι → ℝ) →ₗ[ℝ] lp (fun _ : ℕ => ℝ) 2),
    concreteL2MathlibFiniteSynthesisZeroFiberCoeffTrivial ι T →
      LinearMap.ker T = ⊥ ∧
      Function.Injective T ∧
      Function.Bijective (concreteL2MathlibFiniteSynthesisRangeMap ι T) ∧
      ∀ v : concreteL2MathlibFiniteSynthesisRange ι T,
        concreteL2MathlibFiniteSynthesisRangeLinearEquivOfZeroFiberCoeffTrivial ι T ‹concreteL2MathlibFiniteSynthesisZeroFiberCoeffTrivial ι T›
          (concreteL2MathlibFiniteSynthesisRangeCoordinatesOfZeroFiberCoeffTrivial ι T ‹concreteL2MathlibFiniteSynthesisZeroFiberCoeffTrivial ι T› v) = v

/-- Adapter theorem for the finite synthesis kernel template. -/
theorem concrete_l2_mathlib_finite_synthesis_kernel_template_adapter_ready :
    concreteL2MathlibFiniteSynthesisKernelTemplateAdapter := by
  intro ι T hzero
  exact ⟨
    concrete_l2_mathlib_finite_synthesis_ker_eq_bot_of_zero_fiber_coeff_trivial ι T hzero,
    concrete_l2_mathlib_finite_synthesis_injective_of_zero_fiber_coeff_trivial ι T hzero,
    concrete_l2_mathlib_finite_synthesis_range_map_bijective_of_zero_fiber_coeff_trivial ι T hzero,
    by
      intro v
      exact concrete_l2_mathlib_finite_synthesis_range_coordinates_synthesize_of_zero_fiber_coeff_trivial ι T hzero v⟩

/-- Surface for the finite synthesis kernel template.

This is the second abstraction step beyond the `Fin 2`/`Fin 3` carrier ladder.
It isolates the exact proof obligation needed for a future all-`Fin n`
coordinate-unit synthesis theorem: prove coefficient-triviality of the zero
fiber.  Once that is proved, the kernel, injectivity, range equivalence, and
coordinate reconstruction all follow from this template. -/
structure ConcreteL2MathlibFiniteSynthesisKernelTemplateSurface where
  rangeTemplateReady : concreteAnalyticSpineL2MathlibFiniteSynthesisRangeTemplateSurfaceReady
  kernelTemplateAdapter : concreteL2MathlibFiniteSynthesisKernelTemplateAdapter
  boundaryZeroFiberForGeneralCoordinateSynthesisNotClaimed : Prop
  boundaryNotGeneralFiniteFamilyLinearIndependence : Prop
  boundaryNotBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop
  boundaryNotPositiveSpectralWeightTheorem : Prop

/-- Concrete finite synthesis kernel template surface. -/
def concreteL2MathlibFiniteSynthesisKernelTemplateSurface :
    ConcreteL2MathlibFiniteSynthesisKernelTemplateSurface :=
  { rangeTemplateReady :=
      concrete_analytic_spine_l2_mathlib_finite_synthesis_range_template_surface_ready
    kernelTemplateAdapter :=
      concrete_l2_mathlib_finite_synthesis_kernel_template_adapter_ready
    boundaryZeroFiberForGeneralCoordinateSynthesisNotClaimed := True
    boundaryNotGeneralFiniteFamilyLinearIndependence := True
    boundaryNotBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True
    boundaryNotPositiveSpectralWeightTheorem := True }

/-- Readiness predicate for the finite synthesis kernel template surface. -/
def concreteAnalyticSpineL2MathlibFiniteSynthesisKernelTemplateSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFiniteSynthesisRangeTemplateSurfaceReady ∧
  concreteL2MathlibFiniteSynthesisKernelTemplateAdapter ∧
  concreteL2MathlibFiniteSynthesisKernelTemplateSurface.boundaryZeroFiberForGeneralCoordinateSynthesisNotClaimed ∧
  concreteL2MathlibFiniteSynthesisKernelTemplateSurface.boundaryNotGeneralFiniteFamilyLinearIndependence ∧
  concreteL2MathlibFiniteSynthesisKernelTemplateSurface.boundaryNotBasisTheorem ∧
  concreteL2MathlibFiniteSynthesisKernelTemplateSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFiniteSynthesisKernelTemplateSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFiniteSynthesisKernelTemplateSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFiniteSynthesisKernelTemplateSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFiniteSynthesisKernelTemplateSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFiniteSynthesisKernelTemplateSurface.boundaryNotSpectralAtomTheorem ∧
  concreteL2MathlibFiniteSynthesisKernelTemplateSurface.boundaryNotPositiveSpectralWeightTheorem

/-- Readiness theorem for the finite synthesis kernel template surface. -/
theorem concrete_analytic_spine_l2_mathlib_finite_synthesis_kernel_template_surface_ready :
    concreteAnalyticSpineL2MathlibFiniteSynthesisKernelTemplateSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFiniteSynthesisKernelTemplateSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_finite_synthesis_range_template_surface_ready <|
      And.intro concrete_l2_mathlib_finite_synthesis_kernel_template_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial <| And.intro trivial trivial

/-- Hard-residual boundary marker for the finite synthesis kernel template. -/
def concreteAnalyticSpineL2MathlibFiniteSynthesisKernelTemplateHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFiniteSynthesisKernelTemplateSurfaceReady

/-- Hard-residual boundary theorem for the finite synthesis kernel template. -/
theorem concrete_analytic_spine_l2_mathlib_finite_synthesis_kernel_template_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFiniteSynthesisKernelTemplateHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_finite_synthesis_kernel_template_surface_ready

end

end MathlibAnalytic
end MGAP4D
