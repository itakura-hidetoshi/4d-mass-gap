import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormTruncationFiniteSupportGraph

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
Once the graph-norm convergence target is supplied, all other raw truncation
obligations are now discharged by the previous truncation layers.
-/
theorem concrete_l2_raw_truncation_to_domain_sequence_obligation_of_graph_norm_convergence
    (hconv : concreteL2RawTruncationGraphNormConvergenceTarget) :
    concreteL2RawTruncationToDomainSequenceObligation := by
  exact ⟨
    concrete_l2_raw_truncation_summability_target_ready,
    concrete_l2_raw_truncation_finite_support_target_ready,
    concrete_l2_raw_truncation_diagonal_domain_target_ready,
    concrete_l2_raw_truncation_finite_support_graph_target_ready,
    hconv⟩

/--
The graph-norm convergence target is exactly the remaining analytic target for
constructive truncation-to-domain-sequence density.
-/
def concreteL2RawTruncationRemainingGraphNormConvergenceOnlyTarget : Prop :=
  concreteL2RawTruncationGraphNormConvergenceTarget

/--
Remaining convergence target implies the full raw truncation obligation.
-/
theorem concrete_l2_raw_truncation_to_domain_sequence_obligation_of_remaining_convergence_only
    (h : concreteL2RawTruncationRemainingGraphNormConvergenceOnlyTarget) :
    concreteL2RawTruncationToDomainSequenceObligation := by
  exact concrete_l2_raw_truncation_to_domain_sequence_obligation_of_graph_norm_convergence h

/--
Remaining convergence target implies the global domain-sequence target.
-/
theorem concrete_l2_graph_norm_global_domain_sequence_target_of_remaining_convergence_only
    (h : concreteL2RawTruncationRemainingGraphNormConvergenceOnlyTarget) :
    concreteL2MathlibSpectralAuditR2GraphNormGlobalDomainSequenceTarget := by
  exact h

/--
Remaining convergence target implies the precise graph-norm finite-support
density target.
-/
theorem concrete_l2_graph_norm_precise_density_target_of_remaining_convergence_only
    (h : concreteL2RawTruncationRemainingGraphNormConvergenceOnlyTarget) :
    concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportDensityPreciseTarget := by
  exact concrete_l2_mathlib_spectral_audit_r2_graph_norm_precise_density_target_of_global_domain_sequence_target h

/-- Surface reducing the truncation proof to the single graph-norm convergence target. -/
structure ConcreteL2MathlibSpectralAuditR2GraphNormTruncationObligationBridgeSurface where
  truncationFiniteSupportGraphReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormTruncationFiniteSupportGraphSurfaceReady
  remainingTarget : Prop
  remainingImpliesFullTruncationObligation :
    remainingTarget → concreteL2RawTruncationToDomainSequenceObligation
  remainingImpliesGlobalDomainSequence :
    remainingTarget → concreteL2MathlibSpectralAuditR2GraphNormGlobalDomainSequenceTarget
  remainingImpliesPreciseDensity :
    remainingTarget → concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportDensityPreciseTarget
  boundaryNotGraphNormConvergenceTheorem : Prop
  boundaryNotFullGraphNormDensityTheorem : Prop
  boundaryNotGraphNormCoreTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete surface reducing the truncation proof to graph-norm convergence. -/
def concreteL2MathlibSpectralAuditR2GraphNormTruncationObligationBridgeSurface :
    ConcreteL2MathlibSpectralAuditR2GraphNormTruncationObligationBridgeSurface :=
  { truncationFiniteSupportGraphReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_truncation_finite_support_graph_surface_ready
    remainingTarget :=
      concreteL2RawTruncationRemainingGraphNormConvergenceOnlyTarget
    remainingImpliesFullTruncationObligation :=
      concrete_l2_raw_truncation_to_domain_sequence_obligation_of_remaining_convergence_only
    remainingImpliesGlobalDomainSequence :=
      concrete_l2_graph_norm_global_domain_sequence_target_of_remaining_convergence_only
    remainingImpliesPreciseDensity :=
      concrete_l2_graph_norm_precise_density_target_of_remaining_convergence_only
    boundaryNotGraphNormConvergenceTheorem := True
    boundaryNotFullGraphNormDensityTheorem := True
    boundaryNotGraphNormCoreTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotPositiveSpectralWeight := True }

/-- Readiness predicate for the truncation obligation bridge. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormTruncationObligationBridgeSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormTruncationFiniteSupportGraphSurfaceReady ∧
  (concreteL2RawTruncationRemainingGraphNormConvergenceOnlyTarget →
    concreteL2RawTruncationToDomainSequenceObligation) ∧
  (concreteL2RawTruncationRemainingGraphNormConvergenceOnlyTarget →
    concreteL2MathlibSpectralAuditR2GraphNormGlobalDomainSequenceTarget) ∧
  (concreteL2RawTruncationRemainingGraphNormConvergenceOnlyTarget →
    concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportDensityPreciseTarget)

/-- Readiness theorem for the truncation obligation bridge. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_truncation_obligation_bridge_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormTruncationObligationBridgeSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_truncation_finite_support_graph_surface_ready,
    concrete_l2_raw_truncation_to_domain_sequence_obligation_of_remaining_convergence_only,
    concrete_l2_graph_norm_global_domain_sequence_target_of_remaining_convergence_only,
    concrete_l2_graph_norm_precise_density_target_of_remaining_convergence_only⟩

end

end MathlibAnalytic
end MGAP4D