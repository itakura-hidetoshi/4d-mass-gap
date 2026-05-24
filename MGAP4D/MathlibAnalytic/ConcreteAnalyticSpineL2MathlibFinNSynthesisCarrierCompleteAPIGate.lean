import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinNSynthesisCarrierCompleteAPIBundle

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
Canonical gate for the completed finite synthesis carrier API.

This gate is intentionally range-local.  It re-exports the completed API bundle
and the terminal boundary witness as the stable downstream entry point, without
claiming any ambient Hilbert-basis, dense-domain, self-adjointness, PVM,
spectral-atom, or positive-weight theorem.
-/
def concreteL2MathlibFinNSynthesisCarrierCompleteAPIGate
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) : Prop :=
  concreteL2MathlibFinNSynthesisCarrierCompleteAPIBundle hφ ∧
  concreteL2MathlibFinNSynthesisCarrierCompleteAPIBundleWithBoundary hφ

/-- Readiness theorem for the canonical completed finite synthesis carrier API gate. -/
theorem concrete_l2_mathlib_fin_n_synthesis_carrier_complete_api_gate_ready
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) :
    concreteL2MathlibFinNSynthesisCarrierCompleteAPIGate hφ := by
  exact ⟨
    concrete_l2_mathlib_fin_n_synthesis_carrier_complete_api_bundle_ready hφ,
    concrete_l2_mathlib_fin_n_synthesis_carrier_complete_api_bundle_with_boundary_ready hφ⟩

/--
Surface for the canonical completed finite synthesis carrier API gate.

The surface keeps the proof-carrying finite-coordinate API separate from the
later full spectral-audit lane.
-/
structure ConcreteL2MathlibFinNSynthesisCarrierCompleteAPIGateSurface where
  apiBundleSurfaceReady : concreteAnalyticSpineL2MathlibFinNSynthesisCarrierCompleteAPIBundleSurfaceReady
  apiGateReady : ∀ {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ),
    concreteL2MathlibFinNSynthesisCarrierCompleteAPIGate hφ
  boundaryRangeLocalOnly : concreteL2MathlibFinNSynthesisCarrierCompleteTerminalSurface.boundaryRangeLocalOnly
  hardBoundaryHeld : concreteAnalyticSpineL2MathlibFinNSynthesisCarrierCompleteTerminalHardResidualBoundaryHeld

/-- Concrete surface for the canonical completed finite synthesis carrier API gate. -/
def concreteL2MathlibFinNSynthesisCarrierCompleteAPIGateSurface :
    ConcreteL2MathlibFinNSynthesisCarrierCompleteAPIGateSurface :=
  { apiBundleSurfaceReady :=
      concrete_analytic_spine_l2_mathlib_fin_n_synthesis_carrier_complete_api_bundle_surface_ready
    apiGateReady := concrete_l2_mathlib_fin_n_synthesis_carrier_complete_api_gate_ready
    boundaryRangeLocalOnly := concrete_l2_mathlib_fin_n_synthesis_terminal_boundary_range_local_only
    hardBoundaryHeld := concrete_l2_mathlib_fin_n_synthesis_terminal_hard_residual_boundary_held }

/-- Readiness predicate for the canonical completed finite synthesis carrier API gate surface. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisCarrierCompleteAPIGateSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisCarrierCompleteAPIBundleSurfaceReady ∧
  (∀ {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ),
    concreteL2MathlibFinNSynthesisCarrierCompleteAPIGate hφ) ∧
  concreteL2MathlibFinNSynthesisCarrierCompleteTerminalSurface.boundaryRangeLocalOnly ∧
  concreteAnalyticSpineL2MathlibFinNSynthesisCarrierCompleteTerminalHardResidualBoundaryHeld

/-- Readiness theorem for the canonical completed finite synthesis carrier API gate surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_carrier_complete_api_gate_surface_ready :
    concreteAnalyticSpineL2MathlibFinNSynthesisCarrierCompleteAPIGateSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinNSynthesisCarrierCompleteAPIGateSurfaceReady
  exact ⟨
    concrete_analytic_spine_l2_mathlib_fin_n_synthesis_carrier_complete_api_bundle_surface_ready,
    concrete_l2_mathlib_fin_n_synthesis_carrier_complete_api_gate_ready,
    concrete_l2_mathlib_fin_n_synthesis_terminal_boundary_range_local_only,
    concrete_l2_mathlib_fin_n_synthesis_terminal_hard_residual_boundary_held⟩

end

end MathlibAnalytic
end MGAP4D
