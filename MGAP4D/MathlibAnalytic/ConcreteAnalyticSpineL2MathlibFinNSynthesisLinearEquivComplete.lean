import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinNSynthesisLinearEquivSymmIdentity

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Forward roundtrip of the completed finite synthesis linear equivalence. -/
theorem concrete_l2_mathlib_fin_n_synthesis_linear_equiv_complete_symm_apply_apply
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) (c : Fin m → ℝ) :
    (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ).symm
      (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ c) = c := by
  exact (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ).symm_apply_apply c

/-- Inverse roundtrip of the completed finite synthesis linear equivalence. -/
theorem concrete_l2_mathlib_fin_n_synthesis_linear_equiv_complete_apply_symm_apply
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ)
    (v : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ)) :
    concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ
      ((concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ).symm v) = v := by
  exact (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ).apply_symm_apply v

/-- Forward map of the completed finite synthesis linear equivalence preserves addition. -/
theorem concrete_l2_mathlib_fin_n_synthesis_linear_equiv_complete_map_add
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ)
    (c d : Fin m → ℝ) :
    concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ (c + d) =
      concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ c +
        concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ d := by
  exact map_add (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ) c d

/-- Forward map of the completed finite synthesis linear equivalence preserves scalar multiplication. -/
theorem concrete_l2_mathlib_fin_n_synthesis_linear_equiv_complete_map_smul
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ)
    (a : ℝ) (c : Fin m → ℝ) :
    concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ (a • c) =
      a • concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ c := by
  exact map_smul (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ) a c

/-- Inverse map of the completed finite synthesis linear equivalence preserves addition. -/
theorem concrete_l2_mathlib_fin_n_synthesis_linear_equiv_complete_symm_map_add
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ)
    (v w : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ)) :
    (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ).symm (v + w) =
      (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ).symm v +
        (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ).symm w := by
  exact concrete_l2_mathlib_fin_n_synthesis_linear_equiv_symm_add hφ v w

/-- Inverse map of the completed finite synthesis linear equivalence preserves scalar multiplication. -/
theorem concrete_l2_mathlib_fin_n_synthesis_linear_equiv_complete_symm_map_smul
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ)
    (a : ℝ)
    (v : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ)) :
    (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ).symm (a • v) =
      a • (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ).symm v := by
  exact concrete_l2_mathlib_fin_n_synthesis_linear_equiv_symm_smul hφ a v

/-- Adapter predicate for the completed finite synthesis linear equivalence. -/
def concreteL2MathlibFinNSynthesisLinearEquivCompleteAdapter : Prop :=
  ∀ {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ),
    (∀ c : Fin m → ℝ,
      (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ).symm
        (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ c) = c) ∧
    (∀ v : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ),
      concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ
        ((concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ).symm v) = v)

/-- Adapter theorem for the completed finite synthesis linear equivalence. -/
theorem concrete_l2_mathlib_fin_n_synthesis_linear_equiv_complete_adapter_ready :
    concreteL2MathlibFinNSynthesisLinearEquivCompleteAdapter := by
  intro m φ hφ
  exact ⟨concrete_l2_mathlib_fin_n_synthesis_linear_equiv_complete_symm_apply_apply hφ,
    concrete_l2_mathlib_fin_n_synthesis_linear_equiv_complete_apply_symm_apply hφ⟩

/-- Surface for the completed finite synthesis linear equivalence. -/
structure ConcreteL2MathlibFinNSynthesisLinearEquivCompleteSurface where
  linearEquivSymmIdentityReady :
    concreteAnalyticSpineL2MathlibFinNSynthesisLinearEquivSymmIdentitySurfaceReady
  linearEquivCompleteAdapter : concreteL2MathlibFinNSynthesisLinearEquivCompleteAdapter
  boundaryRangeLocalOnly : Prop
  boundaryNotAmbientBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop
  boundaryNotPositiveSpectralWeightTheorem : Prop

/-- Concrete completed finite synthesis linear equivalence surface. -/
def concreteL2MathlibFinNSynthesisLinearEquivCompleteSurface :
    ConcreteL2MathlibFinNSynthesisLinearEquivCompleteSurface :=
  { linearEquivSymmIdentityReady :=
      concrete_analytic_spine_l2_mathlib_fin_n_synthesis_linear_equiv_symm_identity_surface_ready
    linearEquivCompleteAdapter :=
      concrete_l2_mathlib_fin_n_synthesis_linear_equiv_complete_adapter_ready
    boundaryRangeLocalOnly := True
    boundaryNotAmbientBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True
    boundaryNotPositiveSpectralWeightTheorem := True }

/-- Readiness predicate for the completed finite synthesis linear equivalence. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisLinearEquivCompleteSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisLinearEquivSymmIdentitySurfaceReady ∧
  concreteL2MathlibFinNSynthesisLinearEquivCompleteAdapter ∧
  concreteL2MathlibFinNSynthesisLinearEquivCompleteSurface.boundaryRangeLocalOnly ∧
  concreteL2MathlibFinNSynthesisLinearEquivCompleteSurface.boundaryNotAmbientBasisTheorem ∧
  concreteL2MathlibFinNSynthesisLinearEquivCompleteSurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinNSynthesisLinearEquivCompleteSurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinNSynthesisLinearEquivCompleteSurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinNSynthesisLinearEquivCompleteSurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinNSynthesisLinearEquivCompleteSurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinNSynthesisLinearEquivCompleteSurface.boundaryNotSpectralAtomTheorem ∧
  concreteL2MathlibFinNSynthesisLinearEquivCompleteSurface.boundaryNotPositiveSpectralWeightTheorem

/-- Readiness theorem for the completed finite synthesis linear equivalence. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_linear_equiv_complete_surface_ready :
    concreteAnalyticSpineL2MathlibFinNSynthesisLinearEquivCompleteSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinNSynthesisLinearEquivCompleteSurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_n_synthesis_linear_equiv_symm_identity_surface_ready <|
      And.intro concrete_l2_mathlib_fin_n_synthesis_linear_equiv_complete_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial trivial

/-- Hard-residual boundary marker for the completed finite synthesis linear equivalence. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisLinearEquivCompleteHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisLinearEquivCompleteSurfaceReady

/-- Hard-residual boundary theorem for the completed finite synthesis linear equivalence. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_linear_equiv_complete_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinNSynthesisLinearEquivCompleteHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_n_synthesis_linear_equiv_complete_surface_ready

end

end MathlibAnalytic
end MGAP4D
