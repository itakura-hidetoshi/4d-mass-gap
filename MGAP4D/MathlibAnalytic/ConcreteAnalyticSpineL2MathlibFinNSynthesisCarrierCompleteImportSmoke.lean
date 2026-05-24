import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibFinNSynthesisCarrierCompleteTerminal

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- Smoke-test adapter: importing the completed finite synthesis carrier terminal
is enough to recover the terminal readiness theorem. -/
def concreteL2MathlibFinNSynthesisCarrierCompleteImportSmokeAdapter : Prop :=
  concreteAnalyticSpineL2MathlibFinNSynthesisCarrierCompleteTerminalSurfaceReady

/-- Smoke-test theorem: the one-import terminal readiness alias is usable. -/
theorem concrete_l2_mathlib_fin_n_synthesis_carrier_complete_import_smoke_terminal_ready :
    concreteL2MathlibFinNSynthesisCarrierCompleteImportSmokeAdapter := by
  exact concrete_l2_mathlib_fin_n_synthesis_terminal_surface_ready

/-- Smoke-test theorem: the one-import linear-equivalence completion alias is usable. -/
theorem concrete_l2_mathlib_fin_n_synthesis_carrier_complete_import_smoke_linear_equiv_ready :
    concreteAnalyticSpineL2MathlibFinNSynthesisLinearEquivCompleteSurfaceReady := by
  exact concrete_l2_mathlib_fin_n_synthesis_terminal_linear_equiv_complete_ready

/-- Smoke-test theorem: the one-import range-local boundary alias is usable. -/
theorem concrete_l2_mathlib_fin_n_synthesis_carrier_complete_import_smoke_range_local_only :
    concreteL2MathlibFinNSynthesisCarrierCompleteTerminalSurface.boundaryRangeLocalOnly := by
  exact concrete_l2_mathlib_fin_n_synthesis_terminal_boundary_range_local_only

/-- Smoke-test theorem: the one-import hard-residual boundary alias is usable. -/
theorem concrete_l2_mathlib_fin_n_synthesis_carrier_complete_import_smoke_hard_boundary_held :
    concreteAnalyticSpineL2MathlibFinNSynthesisCarrierCompleteTerminalHardResidualBoundaryHeld := by
  exact concrete_l2_mathlib_fin_n_synthesis_terminal_hard_residual_boundary_held

/-- Completed finite synthesis carrier import-smoke surface. -/
structure ConcreteL2MathlibFinNSynthesisCarrierCompleteImportSmokeSurface where
  terminalReady : concreteAnalyticSpineL2MathlibFinNSynthesisCarrierCompleteTerminalSurfaceReady
  linearEquivCompleteReady : concreteAnalyticSpineL2MathlibFinNSynthesisLinearEquivCompleteSurfaceReady
  rangeLocalOnly : concreteL2MathlibFinNSynthesisCarrierCompleteTerminalSurface.boundaryRangeLocalOnly
  hardBoundaryHeld : concreteAnalyticSpineL2MathlibFinNSynthesisCarrierCompleteTerminalHardResidualBoundaryHeld

/-- Concrete completed finite synthesis carrier import-smoke surface. -/
def concreteL2MathlibFinNSynthesisCarrierCompleteImportSmokeSurface :
    ConcreteL2MathlibFinNSynthesisCarrierCompleteImportSmokeSurface :=
  { terminalReady := concrete_l2_mathlib_fin_n_synthesis_carrier_complete_import_smoke_terminal_ready
    linearEquivCompleteReady := concrete_l2_mathlib_fin_n_synthesis_carrier_complete_import_smoke_linear_equiv_ready
    rangeLocalOnly := concrete_l2_mathlib_fin_n_synthesis_carrier_complete_import_smoke_range_local_only
    hardBoundaryHeld := concrete_l2_mathlib_fin_n_synthesis_carrier_complete_import_smoke_hard_boundary_held }

/-- Readiness predicate for the completed finite synthesis carrier import-smoke surface. -/
def concreteAnalyticSpineL2MathlibFinNSynthesisCarrierCompleteImportSmokeSurfaceReady : Prop :=
  concreteL2MathlibFinNSynthesisCarrierCompleteImportSmokeAdapter ∧
  concreteL2MathlibFinNSynthesisCarrierCompleteTerminalSurface.boundaryRangeLocalOnly ∧
  concreteAnalyticSpineL2MathlibFinNSynthesisCarrierCompleteTerminalHardResidualBoundaryHeld

/-- Readiness theorem for the completed finite synthesis carrier import-smoke surface. -/
theorem concrete_analytic_spine_l2_mathlib_fin_n_synthesis_carrier_complete_import_smoke_surface_ready :
    concreteAnalyticSpineL2MathlibFinNSynthesisCarrierCompleteImportSmokeSurfaceReady := by
  unfold concreteAnalyticSpineL2MathlibFinNSynthesisCarrierCompleteImportSmokeSurfaceReady
  exact ⟨concrete_l2_mathlib_fin_n_synthesis_carrier_complete_import_smoke_terminal_ready,
    concrete_l2_mathlib_fin_n_synthesis_carrier_complete_import_smoke_range_local_only,
    concrete_l2_mathlib_fin_n_synthesis_carrier_complete_import_smoke_hard_boundary_held⟩

end

end MathlibAnalytic
end MGAP4D
