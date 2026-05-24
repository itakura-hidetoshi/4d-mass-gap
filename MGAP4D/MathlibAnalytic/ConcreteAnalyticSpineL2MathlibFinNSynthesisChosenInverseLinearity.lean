import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinNSynthesisRangeMapLinearity

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- The chosen inverse coefficient map preserves addition. -/
theorem concrete_l2_mathlib_fin_n_synthesis_chosen_coefficients_add
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ)
    (v w : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ)) :
    concreteL2MathlibFinNSynthesisChosenRangeMapCoefficients hφ (v + w) =
      concreteL2MathlibFinNSynthesisChosenRangeMapCoefficients hφ v +
        concreteL2MathlibFinNSynthesisChosenRangeMapCoefficients hφ w := by
  symm
  apply concrete_l2_mathlib_fin_n_synthesis_coefficients_eq_chosen_of_range_map_eq hφ
  rw [concrete_l2_mathlib_fin_n_synthesis_range_map_add hφ]
  rw [concrete_l2_mathlib_fin_n_synthesis_range_map_chosen_coefficients_eq_self hφ v]
  rw [concrete_l2_mathlib_fin_n_synthesis_range_map_chosen_coefficients_eq_self hφ w]

/-- The chosen inverse coefficient map preserves scalar multiplication. -/
theorem concrete_l2_mathlib_fin_n_synthesis_chosen_coefficients_smul
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ)
    (a : ℝ)
    (v : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ)) :
    concreteL2MathlibFinNSynthesisChosenRangeMapCoefficients hφ (a • v) =
      a • concreteL2MathlibFinNSynthesisChosenRangeMapCoefficients hφ v := by
  symm
  apply concrete_l2_mathlib_fin_n_synthesis_coefficients_eq_chosen_of_range_map_eq hφ
  rw [concrete_l2_mathlib_fin_n_synthesis_range_map_smul hφ]
  rw [concrete_l2_mathlib_fin_n_synthesis_range_map_chosen_coefficients_eq_self hφ v]

/-- The inverse of the range-map equivalence preserves addition. -/
theorem concrete_l2_mathlib_fin_n_synthesis_range_map_equiv_symm_add
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ)
    (v w : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ)) :
    (concreteL2MathlibFinNSynthesisRangeMapEquiv hφ).symm (v + w) =
      (concreteL2MathlibFinNSynthesisRangeMapEquiv hφ).symm v +
        (concreteL2MathlibFinNSynthesisRangeMapEquiv hφ).symm w := by
  change concreteL2MathlibFinNSynthesisChosenRangeMapCoefficients hφ (v + w) =
      concreteL2MathlibFinNSynthesisChosenRangeMapCoefficients hφ v +
        concreteL2MathlibFinNSynthesisChosenRangeMapCoefficients hφ w
  exact concrete_l2_mathlib_fin_n_synthesis_chosen_coefficients_add hφ v w

/-- The inverse of the range-map equivalence preserves scalar multiplication. -/
theorem concrete_l2_mathlib_fin_n_synthesis_range_map_equiv_symm_smul
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ)
    (a : ℝ)
    (v : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ)) :
    (concreteL2MathlibFinNSynthesisRangeMapEquiv hφ).symm (a • v) =
      a • (concreteL2MathlibFinNSynthesisRangeMapEquiv hφ).symm v := by
  change concreteL2MathlibFinNSynthesisChosenRangeMapCoefficients hφ (a • v) =
      a • concreteL2MathlibFinNSynthesisChosenRangeMapCoefficients hφ v
  exact concrete_l2_mathlib_fin_n_synthesis_chosen_coefficients_smul hφ a v

/-- Adapter predicate for the chosen inverse linearity layer. -/
def concreteL2MathlibFinNSynthesisChosenInverseLinearityAdapter : Prop :=
  ∀ {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ),
    (∀ v w : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ),
      concreteL2MathlibFinNSynthesisChosenRangeMapCoefficients hφ (v + w) =
        concreteL2MathlibFinNSynthesisChosenRangeMapCoefficients hφ v +
          concreteL2MathlibFinNSynthesisChosenRangeMapCoefficients hφ w) ∧
    (∀ (a : ℝ) (v : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ)),
      concreteL2MathlibFinNSynthesisChosenRangeMapCoefficients hφ (a • v) =
        a • concreteL2MathlibFinNSynthesisChosenRangeMapCoefficients hφ v)

/-- Adapter theorem for the chosen inverse linearity layer. -/
theorem concrete_l2_mathlib_fin_n_synthesis_chosen_inverse_linearity_adapter_ready :
    concreteL2MathlibFinNSynthesisChosenInverseLinearityAdapter := by
  intro m φ hφ
  exact ⟨concrete_l2_mathlib_fin_n_synthesis_chosen_coefficients_add hφ,
    concrete_l2_mathlib_fin_n_synthesis_chosen_coefficients_smul hφ⟩

/-- Surface for the chosen inverse linearity layer. -/
structure ConcreteL2MathlibFinNSynthesisChosenInverseLinearitySurface where
  rangeMapLinearityReady : concreteAnalyticSpineL2MathlibFinNSynthesisRangeMapLinearitySurfaceReady
  chosenInverseLinearityAdapter : concreteL2MathlibFinNSynthesisChosenInverseLinearityAdapter
  boundaryRangeLocalOnly : Prop
  boundaryNotAmbientBasisTheorem : Prop
  boundaryNotDenseSpanTheorem : Prop
  boundaryNotFiniteSupportDomainEquivalence : Prop
  boundaryNotUnboundedOperatorDomainTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotSpectralAtomTheorem : Prop
  boundaryNotPositiveSpectralWeightTheorem : Prop

/-- Concrete chosen inverse linearity surface. -/
def concreteL2MathlibFinNSynthesisChosenInverseLinearitySurface :
    ConcreteL2MathlibFinNSynthesisChosenInverseLinearitySurface :=
  { rangeMapLinearityReady :=
      concrete_analytic_spine_l2_mathlib_fin_n_synthesis_range_map_linearity_surface_ready
    chosenInverseLinearityAdapter :=
      concrete_l2_mathlib_fin_n_synthesis_chosen_inverse_linearity_adapter_ready
    boundaryRangeLocalOnly := True
    boundaryNotAmbientBasisTheorem := True
    boundaryNotDenseSpanTheorem := True
    boundaryNotFiniteSupportDomainEquivalence := True
    boundaryNotUnboundedOperatorDomainTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotSpectralAtomTheorem := True
    boundaryNotPositiveSpectralWeightTheorem := True }

/-- Readiness predicate for the chosen inverse linearity layer. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisChosenInverseLinearitySurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisRangeMapLinearitySurfaceReady ∧
  concreteL2MathlibFinNSynthesisChosenInverseLinearityAdapter ∧
  concreteL2MathlibFinNSynthesisChosenInverseLinearitySurface.boundaryRangeLocalOnly ∧
  concreteL2MathlibFinNSynthesisChosenInverseLinearitySurface.boundaryNotAmbientBasisTheorem ∧
  concreteL2MathlibFinNSynthesisChosenInverseLinearitySurface.boundaryNotDenseSpanTheorem ∧
  concreteL2MathlibFinNSynthesisChosenInverseLinearitySurface.boundaryNotFiniteSupportDomainEquivalence ∧
  concreteL2MathlibFinNSynthesisChosenInverseLinearitySurface.boundaryNotUnboundedOperatorDomainTheorem ∧
  concreteL2MathlibFinNSynthesisChosenInverseLinearitySurface.boundaryNotSelfAdjointness ∧
  concreteL2MathlibFinNSynthesisChosenInverseLinearitySurface.boundaryNotPVMConstruction ∧
  concreteL2MathlibFinNSynthesisChosenInverseLinearitySurface.boundaryNotSpectralAtomTheorem ∧
  concreteL2MathlibFinNSynthesisChosenInverseLinearitySurface.boundaryNotPositiveSpectralWeightTheorem

/-- Readiness theorem for the chosen inverse linearity layer. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_chosen_inverse_linearity_surface_ready :
    concreteAnalyticSpineL2MathlibFinNSynthesisChosenInverseLinearitySurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinNSynthesisChosenInverseLinearitySurfaceReady
  exact And.intro
    concrete_analytic_spine_l2_mathlib_fin_n_synthesis_range_map_linearity_surface_ready <|
      And.intro concrete_l2_mathlib_fin_n_synthesis_chosen_inverse_linearity_adapter_ready <|
        And.intro trivial <| And.intro trivial <| And.intro trivial <|
          And.intro trivial <| And.intro trivial <| And.intro trivial <|
            And.intro trivial <| And.intro trivial trivial

/-- Hard-residual boundary marker for the chosen inverse linearity layer. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisChosenInverseLinearityHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisChosenInverseLinearitySurfaceReady

/-- Hard-residual boundary theorem for the chosen inverse linearity layer. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_chosen_inverse_linearity_hard_residual_boundary_held :
    concreteAnalyticSpineL2MathlibFinNSynthesisChosenInverseLinearityHardResidualBoundaryHeld := by
  exact concrete_analytic_spine_l2_mathlib_fin_n_synthesis_chosen_inverse_linearity_surface_ready

end

end MathlibAnalytic
end MGAP4D
