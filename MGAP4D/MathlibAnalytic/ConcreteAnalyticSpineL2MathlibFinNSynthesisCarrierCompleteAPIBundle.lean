import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinNSynthesisCarrierCompleteImportSmoke

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- API bundle for the completed finite synthesis linear equivalence. -/
def concreteL2MathlibFinNSynthesisCarrierCompleteAPIBundle
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) : Prop :=
  (∀ c : Fin m → ℝ,
      (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ).symm
        (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ c) = c) ∧
  (∀ v : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ),
      concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ
        ((concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ).symm v) = v) ∧
  (∀ c d : Fin m → ℝ,
      concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ (c + d) =
        concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ c +
          concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ d) ∧
  (∀ (a : ℝ) (c : Fin m → ℝ),
      concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ (a • c) =
        a • concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ c) ∧
  (∀ v w : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ),
      (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ).symm (v + w) =
        (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ).symm v +
          (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ).symm w) ∧
  (∀ (a : ℝ) (v : concreteL2MathlibFiniteSynthesisRange (Fin m)
      (concreteL2MathlibFinNSynthesisLinearMap m φ)),
      (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ).symm (a • v) =
        a • (concreteL2MathlibFinNSynthesisRangeLinearEquivOfInjective hφ).symm v)

/-- API bundle theorem for the completed finite synthesis linear equivalence. -/
theorem concrete_l2_mathlib_fin_n_synthesis_carrier_complete_api_bundle_ready
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) :
    concreteL2MathlibFinNSynthesisCarrierCompleteAPIBundle hφ := by
  unfold concreteL2MathlibFinNSynthesisCarrierCompleteAPIBundle
  exact ⟨
    concrete_l2_mathlib_fin_n_synthesis_linear_equiv_complete_symm_apply_apply hφ,
    concrete_l2_mathlib_fin_n_synthesis_linear_equiv_complete_apply_symm_apply hφ,
    concrete_l2_mathlib_fin_n_synthesis_linear_equiv_complete_map_add hφ,
    concrete_l2_mathlib_fin_n_synthesis_linear_equiv_complete_map_smul hφ,
    concrete_l2_mathlib_fin_n_synthesis_linear_equiv_complete_symm_map_add hφ,
    concrete_l2_mathlib_fin_n_synthesis_linear_equiv_complete_symm_map_smul hφ⟩

/-- API bundle plus terminal-boundary readiness for the completed finite synthesis carrier. -/
def concreteL2MathlibFinNSynthesisCarrierCompleteAPIBundleWithBoundary
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) : Prop :=
  concreteL2MathlibFinNSynthesisCarrierCompleteAPIBundle hφ ∧
  concreteAnalyticSpineL2MathlibFinNSynthesisCarrierCompleteImportSmokeSurfaceReady

/-- API bundle plus terminal-boundary theorem for the completed finite synthesis carrier. -/
theorem concrete_l2_mathlib_fin_n_synthesis_carrier_complete_api_bundle_with_boundary_ready
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) :
    concreteL2MathlibFinNSynthesisCarrierCompleteAPIBundleWithBoundary hφ := by
  exact ⟨
    concrete_l2_mathlib_fin_n_synthesis_carrier_complete_api_bundle_ready hφ,
    concrete_analytic_spine_l2_mathlib_fin_n_synthesis_carrier_complete_import_smoke_surface_ready⟩

/-- Surface for the completed finite synthesis carrier API bundle. -/
structure ConcreteL2MathlibFinNSynthesisCarrierCompleteAPIBundleSurface where
  importSmokeReady : concreteAnalyticSpineL2MathlibFinNSynthesisCarrierCompleteImportSmokeSurfaceReady
  apiBundleReady : ∀ {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ),
    concreteL2MathlibFinNSynthesisCarrierCompleteAPIBundle hφ
  boundaryRangeLocalOnly : concreteL2MathlibFinNSynthesisCarrierCompleteTerminalSurface.boundaryRangeLocalOnly
  hardBoundaryHeld : concreteAnalyticSpineL2MathlibFinNSynthesisCarrierCompleteTerminalHardResidualBoundaryHeld

/-- Concrete completed finite synthesis carrier API bundle surface. -/
def concreteL2MathlibFinNSynthesisCarrierCompleteAPIBundleSurface :
    ConcreteL2MathlibFinNSynthesisCarrierCompleteAPIBundleSurface :=
  { importSmokeReady :=
      concrete_analytic_spine_l2_mathlib_fin_n_synthesis_carrier_complete_import_smoke_surface_ready
    apiBundleReady := concrete_l2_mathlib_fin_n_synthesis_carrier_complete_api_bundle_ready
    boundaryRangeLocalOnly := concrete_l2_mathlib_fin_n_synthesis_terminal_boundary_range_local_only
    hardBoundaryHeld := concrete_l2_mathlib_fin_n_synthesis_terminal_hard_residual_boundary_held }

/-- Readiness predicate for the completed finite synthesis carrier API bundle surface. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisCarrierCompleteAPIBundleSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisCarrierCompleteImportSmokeSurfaceReady ∧
  (∀ {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ),
    concreteL2MathlibFinNSynthesisCarrierCompleteAPIBundle hφ) ∧
  concreteL2MathlibFinNSynthesisCarrierCompleteTerminalSurface.boundaryRangeLocalOnly ∧
  concreteAnalyticSpineL2MathlibFinNSynthesisCarrierCompleteTerminalHardResidualBoundaryHeld

/-- Readiness theorem for the completed finite synthesis carrier API bundle surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_carrier_complete_api_bundle_surface_ready :
    concreteAnalyticSpineL2MathlibFinNSynthesisCarrierCompleteAPIBundleSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinNSynthesisCarrierCompleteAPIBundleSurfaceReady
  exact ⟨
    concrete_analytic_spine_l2_mathlib_fin_n_synthesis_carrier_complete_import_smoke_surface_ready,
    concrete_l2_mathlib_fin_n_synthesis_carrier_complete_api_bundle_ready,
    concrete_l2_mathlib_fin_n_synthesis_terminal_boundary_range_local_only,
    concrete_l2_mathlib_fin_n_synthesis_terminal_hard_residual_boundary_held⟩

end

end MathlibAnalytic
end MGAP4D
