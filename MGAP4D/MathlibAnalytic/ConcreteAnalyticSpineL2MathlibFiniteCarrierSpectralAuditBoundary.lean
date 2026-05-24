import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinNSynthesisCarrierCompleteAPIGate

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
Finite-carrier spectral audit boundary.

This boundary records exactly what the completed finite synthesis carrier API gate
is allowed to export toward the later spectral lane.  It is a proof-carrying
finite-coordinate interface, not a full unbounded Hilbert-space spectral theorem.
-/
def concreteL2MathlibFiniteCarrierSpectralAuditBoundary
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) : Prop :=
  concreteL2MathlibFinNSynthesisCarrierCompleteAPIGate hφ ∧
  concreteL2MathlibFinNSynthesisCarrierCompleteTerminalSurface.boundaryRangeLocalOnly ∧
  concreteAnalyticSpineL2MathlibFinNSynthesisCarrierCompleteTerminalHardResidualBoundaryHeld

/-- Readiness theorem for the finite-carrier spectral audit boundary. -/
theorem concrete_l2_mathlib_finite_carrier_spectral_audit_boundary_ready
    {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ) :
    concreteL2MathlibFiniteCarrierSpectralAuditBoundary hφ := by
  unfold concreteL2MathlibFiniteCarrierSpectralAuditBoundary
  exact ⟨
    concrete_l2_mathlib_fin_n_synthesis_carrier_complete_api_gate_ready hφ,
    concrete_l2_mathlib_fin_n_synthesis_terminal_boundary_range_local_only,
    concrete_l2_mathlib_fin_n_synthesis_terminal_hard_residual_boundary_held⟩

/--
Negative boundary marker: the finite carrier audit boundary is not packaged here
as an ambient basis theorem, dense-domain theorem, unbounded-operator theorem,
self-adjointness theorem, PVM theorem, spectral-atom theorem, or positive-weight
theorem.
-/
def concreteL2MathlibFiniteCarrierSpectralAuditHardResidualBoundaryHeld : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisCarrierCompleteTerminalHardResidualBoundaryHeld

/-- The finite-carrier spectral audit hard residual boundary is held. -/
theorem concrete_l2_mathlib_finite_carrier_spectral_audit_hard_residual_boundary_held :
    concreteL2MathlibFiniteCarrierSpectralAuditHardResidualBoundaryHeld := by
  exact concrete_l2_mathlib_fin_n_synthesis_terminal_hard_residual_boundary_held

/-- Surface for the finite-carrier spectral audit boundary. -/
structure ConcreteL2MathlibFiniteCarrierSpectralAuditBoundarySurface where
  apiGateSurfaceReady : concreteAnalyticSpineL2MathlibFinNSynthesisCarrierCompleteAPIGateSurfaceReady
  boundaryReady : ∀ {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ),
    concreteL2MathlibFiniteCarrierSpectralAuditBoundary hφ
  rangeLocalOnly : concreteL2MathlibFinNSynthesisCarrierCompleteTerminalSurface.boundaryRangeLocalOnly
  hardResidualBoundaryHeld : concreteL2MathlibFiniteCarrierSpectralAuditHardResidualBoundaryHeld

/-- Concrete finite-carrier spectral audit boundary surface. -/
def concreteL2MathlibFiniteCarrierSpectralAuditBoundarySurface :
    ConcreteL2MathlibFiniteCarrierSpectralAuditBoundarySurface :=
  { apiGateSurfaceReady :=
      concrete_analytic_spine_l2_mathlib_fin_n_synthesis_carrier_complete_api_gate_surface_ready
    boundaryReady := concrete_l2_mathlib_finite_carrier_spectral_audit_boundary_ready
    rangeLocalOnly := concrete_l2_mathlib_fin_n_synthesis_terminal_boundary_range_local_only
    hardResidualBoundaryHeld :=
      concrete_l2_mathlib_finite_carrier_spectral_audit_hard_residual_boundary_held }

/-- Readiness predicate for the finite-carrier spectral audit boundary surface. -/
def concreteAnalyticSpineL2MathlibFiniteCarrierSpectralAuditBoundarySurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisCarrierCompleteAPIGateSurfaceReady ∧
  (∀ {m : ℕ} {φ : Fin m → ℕ} (hφ : Function.Injective φ),
    concreteL2MathlibFiniteCarrierSpectralAuditBoundary hφ) ∧
  concreteL2MathlibFinNSynthesisCarrierCompleteTerminalSurface.boundaryRangeLocalOnly ∧
  concreteL2MathlibFiniteCarrierSpectralAuditHardResidualBoundaryHeld

/-- Readiness theorem for the finite-carrier spectral audit boundary surface. -/
theorem concrete_analytic_spine_l2_mathlib_finite_carrier_spectral_audit_boundary_surface_ready :
    concreteAnalyticSpineL2MathlibFiniteCarrierSpectralAuditBoundarySurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFiniteCarrierSpectralAuditBoundarySurfaceReady
  exact ⟨
    concrete_analytic_spine_l2_mathlib_fin_n_synthesis_carrier_complete_api_gate_surface_ready,
    concrete_l2_mathlib_finite_carrier_spectral_audit_boundary_ready,
    concrete_l2_mathlib_fin_n_synthesis_terminal_boundary_range_local_only,
    concrete_l2_mathlib_finite_carrier_spectral_audit_hard_residual_boundary_held⟩

end

end MathlibAnalytic
end MGAP4D
