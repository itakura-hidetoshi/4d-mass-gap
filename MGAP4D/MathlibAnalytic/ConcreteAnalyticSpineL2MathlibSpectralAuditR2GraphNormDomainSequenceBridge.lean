import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormFiniteSupportWitnessSequence

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
Canonical graph-pair sequence induced by a sequence of diagonal-domain points.
-/
def concreteL2MathlibSpectralAuditR2GraphNormCanonicalGraphSequence
    (v : ℕ → ConcreteL2DiagonalDomainCarrier) : ℕ → ConcreteL2GraphPairSpace :=
  fun n => ((v n).1, concreteL2DiagonalActionL2 (v n))

/--
A domain-sequence approximation target for one diagonal-domain point.

This is the structured version of the graph-pair sequence target: it asks for a
sequence of diagonal-domain points whose canonical graph pairs are finite-support
core graph points and converge to the target canonical graph pair in the named
graph-norm topology.
-/
def concreteL2MathlibSpectralAuditR2GraphNormDomainSequenceTarget
    (x : ConcreteL2DiagonalDomainCarrier) : Prop :=
  ∃ v : ℕ → ConcreteL2DiagonalDomainCarrier,
    (∀ n : ℕ,
      ((v n).1, concreteL2DiagonalActionL2 (v n)) ∈
        ConcreteL2FiniteSupportCoreGraphCarrier) ∧
      Filter.Tendsto
        (concreteL2MathlibSpectralAuditR2GraphNormCanonicalGraphSequence v)
        Filter.atTop
        (@nhds ConcreteL2GraphPairSpace concreteL2GraphNormTopology
          (x.1, concreteL2DiagonalActionL2 x))

/--
A domain-sequence approximation gives the already-established graph-pair
approximation sequence target.
-/
theorem concrete_l2_mathlib_spectral_audit_r2_graph_norm_approximation_sequence_target_of_domain_sequence
    {x : ConcreteL2DiagonalDomainCarrier}
    (hx : concreteL2MathlibSpectralAuditR2GraphNormDomainSequenceTarget x) :
    concreteL2MathlibSpectralAuditR2GraphNormApproximationSequenceTarget x := by
  rcases hx with ⟨v, hv_mem, hv_tendsto⟩
  exact ⟨
    concreteL2MathlibSpectralAuditR2GraphNormCanonicalGraphSequence v,
    hv_mem,
    hv_tendsto⟩

/--
Global domain-sequence target for the future graph-norm finite-support density
proof.
-/
def concreteL2MathlibSpectralAuditR2GraphNormGlobalDomainSequenceTarget : Prop :=
  ∀ x : ConcreteL2DiagonalDomainCarrier,
    concreteL2MathlibSpectralAuditR2GraphNormDomainSequenceTarget x

/--
The global domain-sequence target implies the graph-pair sequence target.
-/
theorem concrete_l2_mathlib_spectral_audit_r2_graph_norm_sequence_target_of_global_domain_sequence_target
    (h : concreteL2MathlibSpectralAuditR2GraphNormGlobalDomainSequenceTarget) :
    concreteL2MathlibSpectralAuditR2GraphNormDensitySequenceTarget := by
  intro x
  exact concrete_l2_mathlib_spectral_audit_r2_graph_norm_approximation_sequence_target_of_domain_sequence
    (h x)

/--
The global domain-sequence target implies the precise graph-norm density target.
-/
theorem concrete_l2_mathlib_spectral_audit_r2_graph_norm_precise_density_target_of_global_domain_sequence_target
    (h : concreteL2MathlibSpectralAuditR2GraphNormGlobalDomainSequenceTarget) :
    concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportDensityPreciseTarget := by
  exact concrete_l2_mathlib_spectral_audit_r2_graph_norm_precise_density_target_of_sequence_target
    (concrete_l2_mathlib_spectral_audit_r2_graph_norm_sequence_target_of_global_domain_sequence_target h)

/-- Surface for the structured domain-sequence bridge. -/
structure ConcreteL2MathlibSpectralAuditR2GraphNormDomainSequenceBridgeSurface where
  finiteSupportWitnessSequenceReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormFiniteSupportWitnessSequenceSurfaceReady
  domainSequenceTarget : Prop
  globalDomainSequenceImpliesSequenceTarget :
    concreteL2MathlibSpectralAuditR2GraphNormGlobalDomainSequenceTarget →
      concreteL2MathlibSpectralAuditR2GraphNormDensitySequenceTarget
  globalDomainSequenceImpliesPreciseDensity :
    concreteL2MathlibSpectralAuditR2GraphNormGlobalDomainSequenceTarget →
      concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportDensityPreciseTarget
  boundaryNotGlobalDomainSequenceTheorem : Prop
  boundaryNotFullGraphNormDensityTheorem : Prop
  boundaryNotGraphNormCoreTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete surface for the structured domain-sequence bridge. -/
def concreteL2MathlibSpectralAuditR2GraphNormDomainSequenceBridgeSurface :
    ConcreteL2MathlibSpectralAuditR2GraphNormDomainSequenceBridgeSurface :=
  { finiteSupportWitnessSequenceReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_finite_support_witness_sequence_surface_ready
    domainSequenceTarget :=
      concreteL2MathlibSpectralAuditR2GraphNormGlobalDomainSequenceTarget
    globalDomainSequenceImpliesSequenceTarget :=
      concrete_l2_mathlib_spectral_audit_r2_graph_norm_sequence_target_of_global_domain_sequence_target
    globalDomainSequenceImpliesPreciseDensity :=
      concrete_l2_mathlib_spectral_audit_r2_graph_norm_precise_density_target_of_global_domain_sequence_target
    boundaryNotGlobalDomainSequenceTheorem := True
    boundaryNotFullGraphNormDensityTheorem := True
    boundaryNotGraphNormCoreTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotPositiveSpectralWeight := True }

/-- Readiness predicate for the structured domain-sequence bridge. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormDomainSequenceBridgeSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormFiniteSupportWitnessSequenceSurfaceReady ∧
  (concreteL2MathlibSpectralAuditR2GraphNormGlobalDomainSequenceTarget →
    concreteL2MathlibSpectralAuditR2GraphNormDensitySequenceTarget) ∧
  (concreteL2MathlibSpectralAuditR2GraphNormGlobalDomainSequenceTarget →
    concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportDensityPreciseTarget)

/-- Readiness theorem for the structured domain-sequence bridge. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_domain_sequence_bridge_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormDomainSequenceBridgeSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_finite_support_witness_sequence_surface_ready,
    concrete_l2_mathlib_spectral_audit_r2_graph_norm_sequence_target_of_global_domain_sequence_target,
    concrete_l2_mathlib_spectral_audit_r2_graph_norm_precise_density_target_of_global_domain_sequence_target⟩

end

end MathlibAnalytic
end MGAP4D