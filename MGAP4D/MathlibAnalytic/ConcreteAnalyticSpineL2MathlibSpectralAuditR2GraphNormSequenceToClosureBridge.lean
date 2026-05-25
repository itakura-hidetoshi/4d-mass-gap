import Mathlib.Topology.Sequences
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormDensitySequenceTarget

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
A graph-norm finite-support approximation sequence implies graph-norm closure
membership for the corresponding canonical diagonal graph pair.

This uses mathlib's `seqClosure_subset_closure` with the graph-norm topology
passed explicitly.  No global topology or pseudo-metric instance is installed.
-/
theorem concrete_l2_mathlib_spectral_audit_r2_graph_norm_sequence_to_closure_for_domain_point
    {x : ConcreteL2DiagonalDomainCarrier}
    (hxseq : concreteL2MathlibSpectralAuditR2GraphNormApproximationSequenceTarget x) :
    (x.1, concreteL2DiagonalActionL2 x) ∈
      concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportClosureTarget := by
  rcases hxseq with ⟨u, hu_mem, hu_tendsto⟩
  unfold concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportClosureTarget
  exact (@seqClosure_subset_closure ConcreteL2GraphPairSpace concreteL2GraphNormTopology
    ConcreteL2FiniteSupportCoreGraphCarrier)
    ⟨u, hu_mem, hu_tendsto⟩

/--
The global graph-norm sequence target discharges the sequence-to-closure
obligation.
-/
theorem concrete_l2_mathlib_spectral_audit_r2_graph_norm_sequence_to_closure_obligation_ready :
    concreteL2MathlibSpectralAuditR2GraphNormSequenceToClosureObligation := by
  intro hseq x
  exact concrete_l2_mathlib_spectral_audit_r2_graph_norm_sequence_to_closure_for_domain_point
    (hseq x)

/--
Consequently, the global graph-norm sequence target implies the domain
obligation.
-/
theorem concrete_l2_mathlib_spectral_audit_r2_graph_norm_domain_obligation_of_sequence_target
    (hseq : concreteL2MathlibSpectralAuditR2GraphNormDensitySequenceTarget) :
    concreteL2MathlibSpectralAuditR2GraphNormDensityDomainObligation := by
  exact concrete_l2_mathlib_spectral_audit_r2_graph_norm_sequence_to_closure_obligation_ready hseq

/--
Consequently, the global graph-norm sequence target implies the precise density
target.
-/
theorem concrete_l2_mathlib_spectral_audit_r2_graph_norm_precise_density_target_of_sequence_target
    (hseq : concreteL2MathlibSpectralAuditR2GraphNormDensitySequenceTarget) :
    concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportDensityPreciseTarget := by
  exact concrete_l2_mathlib_spectral_audit_r2_graph_norm_density_precise_target_of_domain_obligation
    (concrete_l2_mathlib_spectral_audit_r2_graph_norm_domain_obligation_of_sequence_target hseq)

/-- Surface for the graph-norm sequence-to-closure bridge. -/
structure ConcreteL2MathlibSpectralAuditR2GraphNormSequenceToClosureBridgeSurface where
  sequenceTargetReady :
    concreteL2MathlibSpectralAuditR2GraphNormSequenceToClosureObligation
  sequenceTargetImpliesDomainObligation :
    concreteL2MathlibSpectralAuditR2GraphNormDensitySequenceTarget →
      concreteL2MathlibSpectralAuditR2GraphNormDensityDomainObligation
  sequenceTargetImpliesPreciseDensityTarget :
    concreteL2MathlibSpectralAuditR2GraphNormDensitySequenceTarget →
      concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportDensityPreciseTarget
  boundaryNotGraphNormDensityTheorem : Prop
  boundaryNotGraphNormCoreTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete surface for the graph-norm sequence-to-closure bridge. -/
def concreteL2MathlibSpectralAuditR2GraphNormSequenceToClosureBridgeSurface :
    ConcreteL2MathlibSpectralAuditR2GraphNormSequenceToClosureBridgeSurface :=
  { sequenceTargetReady :=
      concrete_l2_mathlib_spectral_audit_r2_graph_norm_sequence_to_closure_obligation_ready
    sequenceTargetImpliesDomainObligation :=
      concrete_l2_mathlib_spectral_audit_r2_graph_norm_domain_obligation_of_sequence_target
    sequenceTargetImpliesPreciseDensityTarget :=
      concrete_l2_mathlib_spectral_audit_r2_graph_norm_precise_density_target_of_sequence_target
    boundaryNotGraphNormDensityTheorem := True
    boundaryNotGraphNormCoreTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotPositiveSpectralWeight := True }

/-- Readiness predicate for the graph-norm sequence-to-closure bridge. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormSequenceToClosureBridgeSurfaceReady : Prop :=
  concreteL2MathlibSpectralAuditR2GraphNormSequenceToClosureObligation ∧
  (concreteL2MathlibSpectralAuditR2GraphNormDensitySequenceTarget →
    concreteL2MathlibSpectralAuditR2GraphNormDensityDomainObligation) ∧
  (concreteL2MathlibSpectralAuditR2GraphNormDensitySequenceTarget →
    concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportDensityPreciseTarget)

/-- Readiness theorem for the graph-norm sequence-to-closure bridge. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_sequence_to_closure_bridge_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormSequenceToClosureBridgeSurfaceReady := by
  exact ⟨
    concrete_l2_mathlib_spectral_audit_r2_graph_norm_sequence_to_closure_obligation_ready,
    concrete_l2_mathlib_spectral_audit_r2_graph_norm_domain_obligation_of_sequence_target,
    concrete_l2_mathlib_spectral_audit_r2_graph_norm_precise_density_target_of_sequence_target⟩

end

end MathlibAnalytic
end MGAP4D