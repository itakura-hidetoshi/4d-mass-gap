import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinNSynthesisCoefficientRoundtrip

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Left-inverse form of the range-local `Fin m` synthesis equivalence.

Applying the synthesis range equivalence and then reconstructing coordinates
returns the original coefficient vector. -/
theorem concrete_l2_mathlib_fin_n_synthesis_range_equiv_left_inverse
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) :
    Function.LeftInverse
      (concreteL2MathlibFinNSynthesisRangeCoordinatesOfInjective hφ)
      (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ) := by
  intro c
  exact concrete_l2_mathlib_fin_n_synthesis_coordinates_of_equiv_apply hφ c

/-- Right-inverse form of the range-local `Fin m` synthesis equivalence.

Re-synthesizing the reconstructed coordinates of a range vector gives back that
range vector. -/
theorem concrete_l2_mathlib_fin_n_synthesis_range_equiv_right_inverse
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) :
    Function.RightInverse
      (concreteL2MathlibFinNSynthesisRangeCoordinatesOfInjective hφ)
      (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ) := by
  intro v
  exact concrete_l2_mathlib_fin_n_synthesis_coordinates_synthesize_of_injective hφ v

/-- Bidirectional range-local equivalence package for the general `Fin m`
coordinate-unit synthesis carrier. -/
def concreteL2MathlibFinNSynthesisBidirectionalEquivAdapter : Prop :=
  ∀ {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ),
    Function.LeftInverse
      (concreteL2MathlibFinNSynthesisRangeCoordinatesOfInjective hφ)
      (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ) ∧
    Function.RightInverse
      (concreteL2MathlibFinNSynthesisRangeCoordinatesOfInjective hφ)
      (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ)

/-- Adapter theorem for the bidirectional equivalence package. -/
theorem concrete_l2_mathlib_fin_n_synthesis_bidirectional_equiv_adapter_ready :
    concreteL2MathlibFinNSynthesisBidirectionalEquivAdapter := by
  intro m φ hφ
  exact ⟨
    concrete_l2_mathlib_fin_n_synthesis_range_equiv_left_inverse hφ,
    concrete_l2_mathlib_fin_n_synthesis_range_equiv_right_inverse hφ⟩

/-- Surface for the bidirectional range-local equivalence layer. -/
structure ConcreteL2MathlibFinNSynthesisBidirectionalEquivSurface where
  coefficientRoundtripReady : concreteAnalyticSpineL2MathlibFinNSynthesisCoefficientRoundtripSurfaceReady
  bidirectionalEquivAdapter : concreteL2MathlibFinNSynthesisBidirectionalEquivAdapter
  boundaryRangeLocalOnly : Prop
  boundaryNotAmbientBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop
  boundaryNotPositiveSpectralWeightTheorem : Prop

/-- Concrete bidirectional range-local equivalence surface. -/
def concreteL2MathlibFinNSynthesisBidirectionalEquivSurface :
    ConcreteL2MathlibFinNSynthesisBidirectionalEquivSurface :=
  { coefficientRoundtripReady :=
      concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coefficient_roundtrip_surface_ready
    bidirectionalEquivAdapter :=
      concrete_l2_mathlib_fin_n_synthesis_bidirectional_equiv_adapter_ready
    boundaryRangeLocalOnly := True
    boundaryNotAmbientBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True
    boundaryNotPositiveSpectralWeightTheorem := True }

/-- Readiness predicate for the bidirectional range-local equivalence surface. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisBidirectionalEquivSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisCoefficientRoundtripSurfaceReady ∧
  concreteL2MathlibFinNSynthesisBidirectionalEquivAdapter ∧
  concreteL2MathlibFinNSynthesisBidirectionalEquivSurface.boundaryRangeLocalOnly ∧
  concreteL2MathlibFinNSynthesisBidirectionalEquivSurface.boundaryNotAmbientBasisTheorem ∧
  concreteL2MathlibFinNSynthesisBidirectionalEquivSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinNSynthesisBidirectionalEquivSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinNSynthesisBidirectionalEquivSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinNSynthesisBidirectionalEquivSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinNSynthesisBidirectionalEquivSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinNSynthesisBidirectionalEquivSurface.boundaryNotSpectralAtomTheorem ∧
  concreteL2MathlibFinNSynthesisBidirectionalEquivSurface.boundaryNotPositiveSpectralWeightTheorem

/-- Readiness theorem for the bidirectional range-local equivalence surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_bidirectional_equiv_surface_ready :
    concreteAnalyticSpineL2MathlibFinNSynthesisBidirectionalEquivSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinNSynthesisBidirectionalEquivSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_n_synthesis_coefficient_roundtrip_surface_ready <|
      And.intro concrete_l2_mathlib_fin_n_synthesis_bidirectional_equiv_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial trivial

/-- Hard-residual boundary marker for the bidirectional equivalence surface. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisBidirectionalEquivHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisBidirectionalEquivSurfaceReady

/-- Hard-residual boundary theorem for the bidirectional equivalence surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_bidirectional_equiv_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinNSynthesisBidirectionalEquivHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_n_synthesis_bidirectional_equiv_surface_ready

end

end MathlibAnalytic
end MGAP4D
