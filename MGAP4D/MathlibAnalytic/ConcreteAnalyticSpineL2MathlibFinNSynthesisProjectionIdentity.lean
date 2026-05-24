import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinNSynthesisInverseIdentification

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Re-synthesis after coordinate reconstruction is the identity on the finite
synthesis range. -/
theorem concrete_l2_mathlib_fin_n_synthesis_projection_identity_range
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ)
    (v : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ)) :
    concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ
        (concreteL2MathlibFinNSynthesisRangeCoordinatesOfInjective hφ v) = v := by
  exact concrete_l2_mathlib_fin_n_synthesis_coordinates_synthesize_of_injective hφ v

/-- Underlying-value form of the projection identity. -/
theorem concrete_l2_mathlib_fin_n_synthesis_projection_identity_val
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ)
    (v : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ)) :
    (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ
        (concreteL2MathlibFinNSynthesisRangeCoordinatesOfInjective hφ v) :
      lp (fun _ : ℕ => ℝ) 2) = (v : lp (fun _ : ℕ => ℝ) 2) := by
  exact congrArg (fun w : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ) =>
      (w : lp (fun _ : ℕ => ℝ) 2))
    (concrete_l2_mathlib_fin_n_synthesis_projection_identity_range hφ v)

/-- The projection identity expressed as the finite coordinate-unit decomposition
of the underlying `ℓ²` value. -/
theorem concrete_l2_mathlib_fin_n_synthesis_projection_identity_decomposition
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ)
    (v : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ)) :
    (v : lp (fun _ : ℕ => ℝ) 2) =
      ∑ i : Fin m,
        concreteL2MathlibFinNSynthesisRangeCoordinatesOfInjective hφ v i •
          concreteL2MathlibUnit (φ i) := by
  exact concrete_l2_mathlib_fin_n_synthesis_range_decompose_val hφ v

/-- Adapter predicate for the projection-identity layer. -/
def concreteL2MathlibFinNSynthesisProjectionIdentityAdapter : Prop :=
  ∀ {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ),
    ∀ v : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ),
      concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ
          (concreteL2MathlibFinNSynthesisRangeCoordinatesOfInjective hφ v) = v

/-- Adapter theorem for the projection-identity layer. -/
theorem concrete_l2_mathlib_fin_n_synthesis_projection_identity_adapter_ready :
    concreteL2MathlibFinNSynthesisProjectionIdentityAdapter := by
  intro m φ hφ v
  exact concrete_l2_mathlib_fin_n_synthesis_projection_identity_range hφ v

/-- Surface for the projection-identity layer. -/
structure ConcreteL2MathlibFinNSynthesisProjectionIdentitySurface where
  inverseIdentificationReady : concreteAnalyticSpineL2MathlibFinNSynthesisInverseIdentificationSurfaceReady
  projectionIdentityAdapter : concreteL2MathlibFinNSynthesisProjectionIdentityAdapter
  boundaryRangeLocalOnly : Prop
  boundaryNotAmbientBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop
  boundaryNotPositiveSpectralWeightTheorem : Prop

/-- Concrete projection-identity surface. -/
def concreteL2MathlibFinNSynthesisProjectionIdentitySurface :
    ConcreteL2MathlibFinNSynthesisProjectionIdentitySurface :=
  { inverseIdentificationReady :=
      concrete_analytic_spine_l2_mathlib_fin_n_synthesis_inverse_identification_surface_ready
    projectionIdentityAdapter :=
      concrete_l2_mathlib_fin_n_synthesis_projection_identity_adapter_ready
    boundaryRangeLocalOnly := True
    boundaryNotAmbientBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True
    boundaryNotPositiveSpectralWeightTheorem := True }

/-- Readiness predicate for the projection-identity surface. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisProjectionIdentitySurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisInverseIdentificationSurfaceReady ∧
  concreteL2MathlibFinNSynthesisProjectionIdentityAdapter ∧
  concreteL2MathlibFinNSynthesisProjectionIdentitySurface.boundaryRangeLocalOnly ∧
  concreteL2MathlibFinNSynthesisProjectionIdentitySurface.boundaryNotAmbientBasisTheorem ∧
  concreteL2MathlibFinNSynthesisProjectionIdentitySurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinNSynthesisProjectionIdentitySurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinNSynthesisProjectionIdentitySurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinNSynthesisProjectionIdentitySurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinNSynthesisProjectionIdentitySurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinNSynthesisProjectionIdentitySurface.boundaryNotSpectralAtomTheorem ∧
  concreteL2MathlibFinNSynthesisProjectionIdentitySurface.boundaryNotPositiveSpectralWeightTheorem

/-- Readiness theorem for the projection-identity surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_projection_identity_surface_ready :
    concreteAnalyticSpineL2MathlibFinNSynthesisProjectionIdentitySurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinNSynthesisProjectionIdentitySurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_n_synthesis_inverse_identification_surface_ready <|
      And.intro concrete_l2_mathlib_fin_n_synthesis_projection_identity_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial trivial

/-- Hard-residual boundary marker for the projection-identity surface. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisProjectionIdentityHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisProjectionIdentitySurfaceReady

/-- Hard-residual boundary theorem for the projection-identity surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_projection_identity_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinNSynthesisProjectionIdentityHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_n_synthesis_projection_identity_surface_ready

end

end MathlibAnalytic
end MGAP4D
