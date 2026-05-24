import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinNSynthesisChosenInverseLinearity

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- The chosen inverse coefficient map agrees with the inverse of the range
linear equivalence. -/
theorem concrete_l2_mathlib_fin_n_synthesis_chosen_coefficients_eq_linear_equiv_symm
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ)
    (v : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ)) :
    concreteL2MathlibFinNSynthesisChosenRangeMapCoefficients hφ v =
      (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ).symm v := by
  exact concrete_l2_mathlib_fin_n_synthesis_range_map_equiv_symm_eq_linear_equiv_symm hφ v

/-- The inverse of the range linear equivalence agrees with the chosen inverse
coefficient map. -/
theorem concrete_l2_mathlib_fin_n_synthesis_linear_equiv_symm_eq_chosen_coefficients
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ)
    (v : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ)) :
    (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ).symm v =
      concreteL2MathlibFinNSynthesisChosenRangeMapCoefficients hφ v := by
  exact (concrete_l2_mathlib_fin_n_synthesis_chosen_coefficients_eq_linear_equiv_symm hφ v).symm

/-- The inverse linear equivalence preserves addition, expressed through the
chosen inverse bridge. -/
theorem concrete_l2_mathlib_fin_n_synthesis_linear_equiv_symm_add
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ)
    (v w : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ)) :
    (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ).symm (v + w) =
      (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ).symm v +
        (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ).symm w := by
  exact map_add (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ).symm v w

/-- The inverse linear equivalence preserves scalar multiplication, expressed
through the chosen inverse bridge. -/
theorem concrete_l2_mathlib_fin_n_synthesis_linear_equiv_symm_smul
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ)
    (a : ℝ)
    (v : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ)) :
    (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ).symm (a • v) =
      a • (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ).symm v := by
  exact map_smul (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ).symm a v

/-- Function extensionality form: the chosen inverse equals the inverse of the
range linear equivalence. -/
theorem concrete_l2_mathlib_fin_n_synthesis_chosen_funext_eq_linear_equiv_symm
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) :
    (fun v : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ) =>
        concreteL2MathlibFinNSynthesisChosenRangeMapCoefficients hφ v) =
      (fun v : concreteL2MathlibFiniteSynthesisRange (Fin m)
        (concreteL2MathlibFinNSynthesisLinearMap m φ) =>
          (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ).symm v) := by
  funext v
  exact concrete_l2_mathlib_fin_n_synthesis_chosen_coefficients_eq_linear_equiv_symm hφ v

/-- Adapter predicate for the linear-equivalence inverse identity layer. -/
def concreteL2MathlibFinNSynthesisLinearEquivSymmIdentityAdapter : Prop :=
  ∀ {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ),
    ∀ v : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ),
      concreteL2MathlibFinNSynthesisChosenRangeMapCoefficients hφ v =
        (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ).symm v

/-- Adapter theorem for the linear-equivalence inverse identity layer. -/
theorem concrete_l2_mathlib_fin_n_synthesis_linear_equiv_symm_identity_adapter_ready :
    concreteL2MathlibFinNSynthesisLinearEquivSymmIdentityAdapter := by
  intro m φ hφ v
  exact concrete_l2_mathlib_fin_n_synthesis_chosen_coefficients_eq_linear_equiv_symm hφ v

/-- Surface for the linear-equivalence inverse identity layer. -/
structure ConcreteL2MathlibFinNSynthesisLinearEquivSymmIdentitySurface where
  chosenInverseLinearityReady :
    concreteAnalyticSpineL2MathlibFinNSynthesisChosenInverseLinearitySurfaceReady
  linearEquivSymmIdentityAdapter :
    concreteL2MathlibFinNSynthesisLinearEquivSymmIdentityAdapter
  boundaryRangeLocalOnly : Prop
  boundaryNotAmbientBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop
  boundaryNotPositiveSpectralWeightTheorem : Prop

/-- Concrete linear-equivalence inverse identity surface. -/
def concreteL2MathlibFinNSynthesisLinearEquivSymmIdentitySurface :
    ConcreteL2MathlibFinNSynthesisLinearEquivSymmIdentitySurface :=
  { chosenInverseLinearityReady :=
      concrete_analytic_spine_l2_mathlib_fin_n_synthesis_chosen_inverse_linearity_surface_ready
    linearEquivSymmIdentityAdapter :=
      concrete_l2_mathlib_fin_n_synthesis_linear_equiv_symm_identity_adapter_ready
    boundaryRangeLocalOnly := True
    boundaryNotAmbientBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True
    boundaryNotPositiveSpectralWeightTheorem := True }

/-- Readiness predicate for the linear-equivalence inverse identity layer. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisLinearEquivSymmIdentitySurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisChosenInverseLinearitySurfaceReady ∧
  concreteL2MathlibFinNSynthesisLinearEquivSymmIdentityAdapter ∧
  concreteL2MathlibFinNSynthesisLinearEquivSymmIdentitySurface.boundaryRangeLocalOnly ∧
  concreteL2MathlibFinNSynthesisLinearEquivSymmIdentitySurface.boundaryNotAmbientBasisTheorem ∧
  concreteL2MathlibFinNSynthesisLinearEquivSymmIdentitySurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinNSynthesisLinearEquivSymmIdentitySurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinNSynthesisLinearEquivSymmIdentitySurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinNSynthesisLinearEquivSymmIdentitySurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinNSynthesisLinearEquivSymmIdentitySurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinNSynthesisLinearEquivSymmIdentitySurface.boundaryNotSpectralAtomTheorem ∧
  concreteL2MathlibFinNSynthesisLinearEquivSymmIdentitySurface.boundaryNotPositiveSpectralWeightTheorem

/-- Readiness theorem for the linear-equivalence inverse identity layer. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_linear_equiv_symm_identity_surface_ready :
    concreteAnalyticSpineL2MathlibFinNSynthesisLinearEquivSymmIdentitySurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinNSynthesisLinearEquivSymmIdentitySurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_n_synthesis_chosen_inverse_linearity_surface_ready <|
      And.intro concrete_l2_mathlib_fin_n_synthesis_linear_equiv_symm_identity_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial trivial

/-- Hard-residual boundary marker for the linear-equivalence inverse identity layer. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisLinearEquivSymmIdentityHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisLinearEquivSymmIdentitySurfaceReady

/-- Hard-residual boundary theorem for the linear-equivalence inverse identity layer. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_linear_equiv_symm_identity_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinNSynthesisLinearEquivSymmIdentityHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_n_synthesis_linear_equiv_symm_identity_surface_ready

end

end MathlibAnalytic
end MGAP4D
