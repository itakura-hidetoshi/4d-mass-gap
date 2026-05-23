import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinNSynthesisTerminal

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Coefficient roundtrip for the general `Fin m` coordinate-unit synthesis range.

For an injective selected-index map `φ : Fin m → ℕ`, applying the range linear
isomorphism to a coefficient vector and then reconstructing coordinates returns
exactly the original coefficient vector.  This is the left inverse side of the
range-local carrier equivalence. -/
theorem concrete_l2_mathlib_fin_n_synthesis_coordinates_of_equiv_apply
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) (c : Fin m → ℝ) :
    concreteL2MathlibFinNSynthesisRangeCoordinatesOfInjective hφ
        (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ c) = c := by
  change (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ).symm
      (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ c) = c
  exact (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ).symm_apply_apply c

/-- Pointwise form of the coefficient roundtrip theorem. -/
theorem concrete_l2_mathlib_fin_n_synthesis_coordinates_of_equiv_apply_apply
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ)
    (c : Fin m → ℝ) (i : Fin m) :
    concreteL2MathlibFinNSynthesisRangeCoordinatesOfInjective hφ
        (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ c) i = c i := by
  exact congrFun
    (concrete_l2_mathlib_fin_n_synthesis_coordinates_of_equiv_apply hφ c) i

/-- Re-synthesizing the coefficient roundtrip reconstructs the original synthesized
range vector. -/
theorem concrete_l2_mathlib_fin_n_synthesis_equiv_apply_recovered_coordinates
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) (c : Fin m → ℝ) :
    concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ
        (concreteL2MathlibFinNSynthesisRangeCoordinatesOfInjective hφ
          (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ c)) =
      concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ c := by
  rw [concrete_l2_mathlib_fin_n_synthesis_coordinates_of_equiv_apply hφ c]

/-- Adapter predicate for the coefficient roundtrip layer. -/
def concreteL2MathlibFinNSynthesisCoefficientRoundtripAdapter : Prop :=
  ∀ {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) (c : Fin m → ℝ),
    concreteL2MathlibFinNSynthesisRangeCoordinatesOfInjective hφ
        (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ c) = c

/-- Adapter theorem for the coefficient roundtrip layer. -/
theorem concrete_l2_mathlib_fin_n_synthesis_coefficient_roundtrip_adapter_ready :
    concreteL2MathlibFinNSynthesisCoefficientRoundtripAdapter := by
  intro m φ hφ c
  exact concrete_l2_mathlib_fin_n_synthesis_coordinates_of_equiv_apply hφ c

/-- Surface for the coefficient roundtrip layer. -/
structure ConcreteL2MathlibFinNSynthesisCoefficientRoundtripSurface where
  terminalReady : concreteAnalyticSpineL2MathlibFinNSynthesisTerminalSurfaceReady
  coefficientRoundtripAdapter : concreteL2MathlibFinNSynthesisCoefficientRoundtripAdapter
  boundaryRangeLocalOnly : Prop
  boundaryNotAmbientBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop
  boundaryNotPositiveSpectralWeightTheorem : Prop

/-- Concrete coefficient roundtrip surface. -/
def concreteL2MathlibFinNSynthesisCoefficientRoundtripSurface :
    ConcreteL2MathlibFinNSynthesisCoefficientRoundtripSurface :=
  { terminalReady :=
      concrete_analytic_spine_l2_mathlib_fin_n_synthesis_terminal_surface_ready
    coefficientRoundtripAdapter :=
      concrete_l2_mathlib_fin_n_synthesis_coefficient_roundtrip_adapter_ready
    boundaryRangeLocalOnly := True
    boundaryNotAmbientBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True
    boundaryNotPositiveSpectralWeightTheorem := True }

/-- Readiness predicate for the coefficient roundtrip surface. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisCoefficientRoundtripSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisTerminalSurfaceReady ∧
  concreteL2MathlibFinNSynthesisCoefficientRoundtripAdapter ∧
  concreteL2MathlibFinNSynthesisCoefficientRoundtripSurface.boundaryRangeLocalOnly ∧
  concreteL2MathlibFinNSynthesisCoefficientRoundtripSurface.boundaryNotAmbientBasisTheorem ∧
  concreteL2MathlibFinNSynthesisCoefficientRoundtripSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinNSynthesisCoefficientRoundtripSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinNSynthesisCoefficientRoundtripSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinNSynthesisCoefficientRoundtripSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinNSynthesisCoefficientRoundtripSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinNSynthesisCoefficientRoundtripSurface.boundaryNotSpectralAtomTheorem ∧
  concreteL2MathlibFinNSynthesisCoefficientRoundtripSurface.boundaryNotPositiveSpectralWeightTheorem

/-- Readiness theorem for the coefficient roundtrip surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coefficient_roundtrip_surface_ready :
    concreteAnalyticSpineL2MathlibFinNSynthesisCoefficientRoundtripSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinNSynthesisCoefficientRoundtripSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_n_synthesis_terminal_surface_ready <|
      And.intro concrete_l2_mathlib_fin_n_synthesis_coefficient_roundtrip_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial trivial

/-- Hard-residual boundary marker for the coefficient roundtrip surface. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisCoefficientRoundtripHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisCoefficientRoundtripSurfaceReady

/-- Hard-residual boundary theorem for the coefficient roundtrip surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coefficient_roundtrip_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinNSynthesisCoefficientRoundtripHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coefficient_roundtrip_surface_ready

end

end MathlibAnalytic
end MGAP4D
