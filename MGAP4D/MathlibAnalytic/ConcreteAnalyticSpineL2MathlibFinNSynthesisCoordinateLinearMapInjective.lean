import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinNSynthesisCoordinateKernelZero

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- The concrete `Fin m` synthesis linear map is injective under an injective
selected-index map. -/
theorem concrete_l2_mathlib_fin_n_synthesis_linear_map_injective_of_injective
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) :
    Function.Injective (concreteL2MathlibFinNSynthesisLinearMap m φ) := by
  exact LinearMap.ker_eq_bot.1
    (concrete_l2_mathlib_fin_n_synthesis_linear_map_ker_eq_bot_of_injective hφ)

/-- Equality after applying the concrete synthesis linear map is equivalent to
equality of coefficient functions. -/
theorem concrete_l2_mathlib_fin_n_synthesis_linear_map_apply_eq_iff
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) (c d : Fin m → ℝ) :
    concreteL2MathlibFinNSynthesisLinearMap m φ c =
      concreteL2MathlibFinNSynthesisLinearMap m φ d ↔ c = d := by
  constructor
  · intro h
    exact concrete_l2_mathlib_fin_n_synthesis_linear_map_injective_of_injective hφ h
  · intro hcd
    rw [hcd]

/-- Pointwise coefficient equality form of linear-map synthesis equality. -/
theorem concrete_l2_mathlib_fin_n_synthesis_linear_map_apply_eq_iff_pointwise
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) (c d : Fin m → ℝ) :
    concreteL2MathlibFinNSynthesisLinearMap m φ c =
      concreteL2MathlibFinNSynthesisLinearMap m φ d ↔
        ∀ i : Fin m, c i = d i := by
  constructor
  · intro h i
    exact congrFun
      ((concrete_l2_mathlib_fin_n_synthesis_linear_map_apply_eq_iff hφ c d).1 h) i
  · intro hpoint
    apply (concrete_l2_mathlib_fin_n_synthesis_linear_map_apply_eq_iff hφ c d).2
    funext i
    exact hpoint i

/-- Adapter predicate for the synthesis linear-map injectivity layer. -/
def concreteL2MathlibFinNSynthesisCoordinateLinearMapInjectiveAdapter : Prop :=
  ∀ {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ),
    Function.Injective (concreteL2MathlibFinNSynthesisLinearMap m φ)

/-- Adapter theorem for the synthesis linear-map injectivity layer. -/
theorem concrete_l2_mathlib_fin_n_synthesis_coordinate_linear_map_injective_adapter_ready :
    concreteL2MathlibFinNSynthesisCoordinateLinearMapInjectiveAdapter := by
  intro m φ hφ
  exact concrete_l2_mathlib_fin_n_synthesis_linear_map_injective_of_injective hφ

/-- Surface for the synthesis linear-map injectivity layer. -/
structure ConcreteL2MathlibFinNSynthesisCoordinateLinearMapInjectiveSurface where
  coordinateKernelZeroReady : concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateKernelZeroSurfaceReady
  coordinateLinearMapInjectiveAdapter :
    concreteL2MathlibFinNSynthesisCoordinateLinearMapInjectiveAdapter
  boundaryRangeLocalOnly : Prop
  boundaryNotAmbientBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop
  boundaryNotPositiveSpectralWeightTheorem : Prop

/-- Concrete synthesis linear-map injectivity surface. -/
def concreteL2MathlibFinNSynthesisCoordinateLinearMapInjectiveSurface :
    ConcreteL2MathlibFinNSynthesisCoordinateLinearMapInjectiveSurface :=
  { coordinateKernelZeroReady :=
      concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_kernel_zero_surface_ready
    coordinateLinearMapInjectiveAdapter :=
      concrete_l2_mathlib_fin_n_synthesis_coordinate_linear_map_injective_adapter_ready
    boundaryRangeLocalOnly := True
    boundaryNotAmbientBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True
    boundaryNotPositiveSpectralWeightTheorem := True }

/-- Readiness predicate for the synthesis linear-map injectivity surface. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateLinearMapInjectiveSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateKernelZeroSurfaceReady ∧
  concreteL2MathlibFinNSynthesisCoordinateLinearMapInjectiveAdapter ∧
  concreteL2MathlibFinNSynthesisCoordinateLinearMapInjectiveSurface.boundaryRangeLocalOnly ∧
  concreteL2MathlibFinNSynthesisCoordinateLinearMapInjectiveSurface.boundaryNotAmbientBasisTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateLinearMapInjectiveSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateLinearMapInjectiveSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinNSynthesisCoordinateLinearMapInjectiveSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateLinearMapInjectiveSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinNSynthesisCoordinateLinearMapInjectiveSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinNSynthesisCoordinateLinearMapInjectiveSurface.boundaryNotSpectralAtomTheorem ∧
  concreteL2MathlibFinNSynthesisCoordinateLinearMapInjectiveSurface.boundaryNotPositiveSpectralWeightTheorem

/-- Readiness theorem for the synthesis linear-map injectivity surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_linear_map_injective_surface_ready :
    concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateLinearMapInjectiveSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateLinearMapInjectiveSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_kernel_zero_surface_ready <|
      And.intro concrete_l2_mathlib_fin_n_synthesis_coordinate_linear_map_injective_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial trivial

/-- Hard-residual boundary marker for the synthesis linear-map injectivity surface. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateLinearMapInjectiveHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateLinearMapInjectiveSurfaceReady

/-- Hard-residual boundary theorem for the synthesis linear-map injectivity surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_linear_map_injective_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinNSynthesisCoordinateLinearMapInjectiveHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coordinate_linear_map_injective_surface_ready

end

end MathlibAnalytic
end MGAP4D
