import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinNSynthesisCarrierCompleteAPIBundle

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- The completed finite synthesis linear equivalence is bijective. -/
theorem concrete_l2_mathlib_fin_n_synthesis_carrier_complete_linear_equiv_bijective
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) :
    Function.Bijective
      (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ :
        (Fin m → ℝ) → concreteL2MathlibFiniteSynthesisRange (Fin m)
          (concreteL2MathlibFinNSynthesisLinearMap m φ)) := by
  exact (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ).bijective

/-- The inverse of the completed finite synthesis linear equivalence is bijective. -/
theorem concrete_l2_mathlib_fin_n_synthesis_carrier_complete_linear_equiv_symm_bijective
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) :
    Function.Bijective
      ((concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ).symm :
        concreteL2MathlibFiniteSynthesisRange (Fin m)
          (concreteL2MathlibFinNSynthesisLinearMap m φ) → (Fin m → ℝ)) := by
  exact (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ).symm.bijective

/-- The completed finite synthesis API exposes bijectivity in both directions. -/
def concreteL2MathlibFinNSynthesisCarrierCompleteBijectiveAPI
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) : Prop :=
  Function.Bijective
      (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ :
        (Fin m → ℝ) → concreteL2MathlibFiniteSynthesisRange (Fin m)
          (concreteL2MathlibFinNSynthesisLinearMap m φ)) ∧
  Function.Bijective
      ((concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ).symm :
        concreteL2MathlibFiniteSynthesisRange (Fin m)
          (concreteL2MathlibFinNSynthesisLinearMap m φ) → (Fin m → ℝ))

/-- Bijective API theorem for the completed finite synthesis carrier. -/
theorem concrete_l2_mathlib_fin_n_synthesis_carrier_complete_bijective_api_ready
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) :
    concreteL2MathlibFinNSynthesisCarrierCompleteBijectiveAPI hφ := by
  exact ⟨
    concrete_l2_mathlib_fin_n_synthesis_carrier_complete_linear_equiv_bijective hφ,
    concrete_l2_mathlib_fin_n_synthesis_carrier_complete_linear_equiv_symm_bijective hφ⟩

/-- Completed API bundle plus bidirectional bijectivity. -/
def concreteL2MathlibFinNSynthesisCarrierCompleteAPIBundleWithBijective
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) : Prop :=
  concreteL2MathlibFinNSynthesisCarrierCompleteAPIBundleWithBoundary hφ ∧
  concreteL2MathlibFinNSynthesisCarrierCompleteBijectiveAPI hφ

/-- Completed API bundle plus bidirectional bijectivity theorem. -/
theorem concrete_l2_mathlib_fin_n_synthesis_carrier_complete_api_bundle_with_bijective_ready
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) :
    concreteL2MathlibFinNSynthesisCarrierCompleteAPIBundleWithBijective hφ := by
  exact ⟨
    concrete_l2_mathlib_fin_n_synthesis_carrier_complete_api_bundle_with_boundary_ready hφ,
    concrete_l2_mathlib_fin_n_synthesis_carrier_complete_bijective_api_ready hφ⟩

/-- Surface for the completed finite synthesis carrier bijective API. -/
structure ConcreteL2MathlibFinNSynthesisCarrierCompleteBijectiveAPISurface where
  apiBundleSurfaceReady : concreteAnalyticSpineL2MathlibFinNSynthesisCarrierCompleteAPIBundleSurfaceReady
  bijectiveAPIReady : ∀ {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ),
    concreteL2MathlibFinNSynthesisCarrierCompleteBijectiveAPI hφ
  boundaryRangeLocalOnly : concreteL2MathlibFinNSynthesisCarrierCompleteTerminalSurface.boundaryRangeLocalOnly
  hardBoundaryHeld : concreteAnalyticSpineL2MathlibFinNSynthesisCarrierCompleteTerminalHardResidualBoundaryHeld

/-- Concrete completed finite synthesis carrier bijective API surface. -/
def concreteL2MathlibFinNSynthesisCarrierCompleteBijectiveAPISurface :
    ConcreteL2MathlibFinNSynthesisCarrierCompleteBijectiveAPISurface :=
  { apiBundleSurfaceReady :=
      concrete_analytic_spine_l2_mathlib_fin_n_synthesis_carrier_complete_api_bundle_surface_ready
    bijectiveAPIReady := concrete_l2_mathlib_fin_n_synthesis_carrier_complete_bijective_api_ready
    boundaryRangeLocalOnly := concrete_l2_mathlib_fin_n_synthesis_terminal_boundary_range_local_only
    hardBoundaryHeld := concrete_l2_mathlib_fin_n_synthesis_terminal_hard_residual_boundary_held }

/-- Readiness predicate for the completed finite synthesis carrier bijective API surface. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisCarrierCompleteBijectiveAPISurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisCarrierCompleteAPIBundleSurfaceReady ∧
  (∀ {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ),
    concreteL2MathlibFinNSynthesisCarrierCompleteBijectiveAPI hφ) ∧
  concreteL2MathlibFinNSynthesisCarrierCompleteTerminalSurface.boundaryRangeLocalOnly ∧
  concreteAnalyticSpineL2MathlibFinNSynthesisCarrierCompleteTerminalHardResidualBoundaryHeld

/-- Readiness theorem for the completed finite synthesis carrier bijective API surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_carrier_complete_bijective_api_surface_ready :
    concreteAnalyticSpineL2MathlibFinNSynthesisCarrierCompleteBijectiveAPISurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinNSynthesisCarrierCompleteBijectiveAPISurfaceReady
  exact ⟨
    concrete_analytic_spine_l2_mathlib_fin_n_synthesis_carrier_complete_api_bundle_surface_ready,
    concrete_l2_mathlib_fin_n_synthesis_carrier_complete_bijective_api_ready,
    concrete_l2_mathlib_fin_n_synthesis_terminal_boundary_range_local_only,
    concrete_l2_mathlib_fin_n_synthesis_terminal_hard_residual_boundary_held⟩

end

end MathlibAnalytic
end MGAP4D
