import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinNSynthesisCoordinateSynthesisZeroIff

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- The concrete `Fin m` synthesis linear map has trivial kernel under an
injective selected-index map. -/
theorem concrete_l2_mathlib_fin_n_synthesis_linear_map_ker_eq_bot_of_injective
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) :
    LinearMap.ker (concreteL2MathlibFinNSynthesisLinearMap m φ) = ⊥ := by
  exact LinearMap.ker_eq_bot.2
    (concrete_l2_mathlib_fin_n_synthesis_value_map_injective hφ)

/-- Membership in the concrete synthesis kernel is equivalent to being the zero
coefficient vector. -/
theorem concrete_l2_mathlib_fin_n_synthesis_mem_ker_iff_eq_zero
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) (c : Fin m → ℝ) :
    c ∈ LinearMap.ker (concreteL2MathlibFinNSynthesisLinearMap m φ) ↔ c = 0 := by
  rw [concrete_l2_mathlib_fin_n_synthesis_linear_map_ker_eq_bot_of_injective hφ]
  simp

/-- Kernel membership forces every coefficient to vanish. -/
theorem concrete_l2_mathlib_fin_n_synthesis_mem_ker_coefficients_apply_eq_zero
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) {c : Fin m → ℝ}
    (hc : c ∈ LinearMap.ker (concreteL2MathlibFinNSynthesisLinearMap m φ))
    (i : Fin m) :
    c i = 0 := by
  have hczero := (concrete_l2_mathlib_fin_n_synthesis_mem_ker_iff_eq_zero hφ c).1 hc
  exact congrFun hczero i

/-- The concrete synthesis linear map sends a coefficient vector to zero iff the
coefficient vector itself is zero. -/
theorem concrete_l2_mathlib_fin_n_synthesis_linear_map_apply_eq_zero_iff
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) (c : Fin m → ℝ) :
    concreteL2MathlibFinNSynthesisLinearMap m φ c = 0 ↔ c = 0 := by
  rw [← LinearMap.mem_ker]
  exact concrete_l2_mathlib_fin_n_synthesis_mem_ker_iff_eq_zero hφ c

/-- Adapter predicate for the kernel-zero layer. -/
def concreteL2MathlibFinNSynthesisCoordinateKernelZeroAdapter : Prop :=
  ∀ {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ),
    LinearMap.ker (concreteL2MathlibFinNSynthesisLinearMap m φ) = ⊥

/-- Adapter theorem for the kernel-zero layer. -/
theorem concrete_l2_mathlib_fin_n_synthesis_coordinate_kernel_zero_adapter_ready :
    concreteL2MathlibFinNSynthesisCoordinateKernelZeroAdapter := by
  intro m φ hφ
  exact concrete_l2_mathlib_fin_n_synthesis_linear_map_ker_eq_bot_of_injective hφ

/-- Surface for the concrete kernel-zero layer. -/
structure ConcreteL2MathlibFinNSynthesisCoordinateKernelZeroSurface where
  coordinateSynthesisZeroIffReady :
    concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateSynthesisZeroIffSurfaceReady
  coordinateKernelZeroAdapter : concreteL2MathlibFinNSynthesisCoordinateKernelZeroAdapter
  boundaryRangeLocalOnly : Prop
  boundaryNotAmbientBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop
  boundaryNotPositiveSpectralWeightTheorem : Prop

/-- Concrete kernel-zero surface. -/
def concreteL2MathlibFinNSynthesisCoordinateKernelZeroSurface :
    ConcreteL2MathlibFinNSynthesisCoordinateKernelZeroSurface :=
  { coordinateSynthesisZeroIffReady :=
      concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_synthesis_zero_iff_surface_ready
    coordinateKernelZeroAdapter :=
      concrete_l2_mathlib_fin_n_synthesis_coordinate_kernel_zero_adapter_ready
    boundaryRangeLocalOnly := True
    boundaryNotAmbientBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True
    boundaryNotPositiveSpectralWeightTheorem := True }

/-- Readiness predicate for the concrete kernel-zero surface. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateKernelZeroSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateSynthesisZeroIffSurfaceReady ∧
  concreteL2MathlibFinNSynthesisCoordinateKernelZeroAdapter ∧
  concreteL2MathlibFinNSynthesisCoordinateKernelZeroSurface.boundaryRangeLocalOnly ∧
  concreteL2MathlibFinNSynthesisCoordinateKernelZeroSurface.boundaryNotAmbientBasisTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateKernelZeroSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateKernelZeroSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinNSynthesisCoordinateKernelZeroSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateKernelZeroSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinNSynthesisCoordinateKernelZeroSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinNSynthesisCoordinateKernelZeroSurface.boundaryNotSpectralAtomTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateKernelZeroSurface.boundaryNotPositiveSpectralWeightTheorem

/-- Readiness theorem for the concrete kernel-zero surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_kernel_zero_surface_ready :
    concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateKernelZeroSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateKernelZeroSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_synthesis_zero_iff_surface_ready <|
      And.intro concrete_l2_mathlib_fin_n_synthesis_coordinate_kernel_zero_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial trivial

/-- Hard-residual boundary marker for the concrete kernel-zero surface. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateKernelZeroHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateKernelZeroSurfaceReady

/-- Hard-residual boundary theorem for the concrete kernel-zero surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_kernel_zero_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateKernelZeroHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_kernel_zero_surface_ready

end

end MathlibAnalytic
end MGAP4D
