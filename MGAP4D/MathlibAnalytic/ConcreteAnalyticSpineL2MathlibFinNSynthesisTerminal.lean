import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinNSynthesisRangeDecomposition

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Terminal adapter for the general `Fin m` coordinate-unit synthesis carrier.

For an injective selected-index map `φ : Fin m → ℕ`, the general finite synthesis
linear map has bottom kernel, is injective, has a bijective range-restricted map,
and every vector in the range decomposes as the finite sum of its recovered
coordinates times the selected coordinate units. -/
def concreteL2MathlibFinNSynthesisTerminalAdapter : Prop :=
  ∀ {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ),
    LinearMap.ker (concreteL2MathlibFinNSynthesisLinearMap m φ) = ⊥ ∧
    Function.Injective (concreteL2MathlibFinNSynthesisLinearMap m φ) ∧
    Function.Bijective
      (concreteL2MathlibFiniteSynthesisRangeMap (Fin m)
        (concreteL2MathlibFinNSynthesisLinearMap m φ)) ∧
    (∀ v : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ),
      (v : lp (fun _ : ℕ => ℝ) 2) =
        ∑ i : Fin m,
          concreteL2MathlibFinNSynthesisRangeCoordinatesOfInjective hφ v i •
            concreteL2MathlibUnit (φ i))

/-- Terminal adapter theorem for the general `Fin m` coordinate-unit synthesis
carrier. -/
theorem concrete_l2_mathlib_fin_n_synthesis_terminal_adapter_ready :
    concreteL2MathlibFinNSynthesisTerminalAdapter := by
  intro m φ hφ
  exact ⟨
    concrete_l2_mathlib_fin_n_synthesis_ker_eq_bot_of_injective hφ,
    concrete_l2_mathlib_fin_n_synthesis_linear_map_injective_of_injective hφ,
    concrete_l2_mathlib_fin_n_synthesis_range_map_bijective_of_injective hφ,
    by intro v; exact concrete_l2_mathlib_fin_n_synthesis_range_decompose_val hφ v⟩

/-- Terminal surface for the general `Fin m` coordinate-unit synthesis carrier.

This is the first general finite-coordinate carrier surface replacing the former
`Fin 2`/`Fin 3` only ladder.  It remains finite-dimensional/range-local and does
not assert a basis theorem for the ambient `ℓ²`, dense span, finite-support domain
equivalence, unbounded operator facts, self-adjointness, PVM, spectral atom, or
positive spectral weight. -/
structure ConcreteL2MathlibFinNSynthesisTerminalSurface where
  rangeDecompositionReady : concreteAnalyticSpineL2MathlibFinNSynthesisRangeDecompositionSurfaceReady
  terminalAdapter : concreteL2MathlibFinNSynthesisTerminalAdapter
  boundaryRangeLocalOnly : Prop
  boundaryNotAmbientBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop
  boundaryNotPositiveSpectralWeightTheorem : Prop

/-- Concrete terminal surface for the general `Fin m` coordinate-unit synthesis
carrier. -/
def concreteL2MathlibFinNSynthesisTerminalSurface :
    ConcreteL2MathlibFinNSynthesisTerminalSurface :=
  { rangeDecompositionReady :=
      concrete_analytic_spine_l2_mathlib_fin_n_synthesis_range_decomposition_surface_ready
    terminalAdapter :=
      concrete_l2_mathlib_fin_n_synthesis_terminal_adapter_ready
    boundaryRangeLocalOnly := True
    boundaryNotAmbientBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True
    boundaryNotPositiveSpectralWeightTheorem := True }

/-- Readiness predicate for the terminal general `Fin m` coordinate-unit synthesis
surface. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisTerminalSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisRangeDecompositionSurfaceReady ∧
  concreteL2MathlibFinNSynthesisTerminalAdapter ∧
  concreteL2MathlibFinNSynthesisTerminalSurface.boundaryRangeLocalOnly ∧
  concreteL2MathlibFinNSynthesisTerminalSurface.boundaryNotAmbientBasisTheorem ∧
  concreteL2MathlibFinNSynthesisTerminalSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinNSynthesisTerminalSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinNSynthesisTerminalSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinNSynthesisTerminalSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinNSynthesisTerminalSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinNSynthesisTerminalSurface.boundaryNotSpectralAtomTheorem ∧
  concreteL2MathlibFinNSynthesisTerminalSurface.boundaryNotPositiveSpectralWeightTheorem

/-- Readiness theorem for the terminal general `Fin m` coordinate-unit synthesis
surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_terminal_surface_ready :
    concreteAnalyticSpineL2MathlibFinNSynthesisTerminalSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinNSynthesisTerminalSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_n_synthesis_range_decomposition_surface_ready <|
      And.intro concrete_l2_mathlib_fin_n_synthesis_terminal_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial trivial

/-- Hard-residual boundary marker for the terminal general `Fin m` synthesis
surface. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisTerminalHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisTerminalSurfaceReady

/-- Hard-residual boundary theorem for the terminal general `Fin m` synthesis
surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_terminal_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinNSynthesisTerminalHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_n_synthesis_terminal_surface_ready

end

end MathlibAnalytic
end MGAP4D
