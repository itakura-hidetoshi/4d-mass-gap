import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormTruncationObligationBridge

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/-- The `N`th promoted raw truncation of a diagonal-domain point. -/
def concreteL2RawTruncationDomainPoint
    (x : ConcreteL2DiagonalDomainCarrier) (N : ℕ) :
    ConcreteL2DiagonalDomainCarrier :=
  ⟨(⟨concreteL2RawTruncation x.1 N,
      concrete_l2_raw_truncation_summable_sq x.1 N⟩ : ConcreteL2RealSequence),
    concrete_l2_raw_truncation_mem_diagonal_domain x.1 N⟩

/-- The concrete truncation domain sequence attached to a diagonal-domain point. -/
def concreteL2RawTruncationDomainSequence
    (x : ConcreteL2DiagonalDomainCarrier) : ℕ → ConcreteL2DiagonalDomainCarrier :=
  fun N => concreteL2RawTruncationDomainPoint x N

/-- Each promoted raw truncation has a finite-support canonical graph pair. -/
theorem concrete_l2_raw_truncation_domain_sequence_mem_finite_support_graph
    (x : ConcreteL2DiagonalDomainCarrier) (N : ℕ) :
    (((concreteL2RawTruncationDomainSequence x N).1,
        concreteL2DiagonalActionL2 (concreteL2RawTruncationDomainSequence x N)) ∈
      ConcreteL2FiniteSupportCoreGraphCarrier) := by
  unfold concreteL2RawTruncationDomainSequence
  unfold concreteL2RawTruncationDomainPoint
  exact concrete_l2_raw_truncation_mem_finite_support_core_graph
    x N
    (concrete_l2_raw_truncation_summable_sq x.1 N)
    (concrete_l2_raw_truncation_mem_diagonal_domain x.1 N)

/--
Explicit truncation convergence target: the canonical graph sequence induced by
raw truncations converges to the target canonical graph pair in the named
graph-norm topology.
-/
def concreteL2RawTruncationCanonicalGraphConvergenceTarget : Prop :=
  ∀ x : ConcreteL2DiagonalDomainCarrier,
    Filter.Tendsto
      (concreteL2MathlibSpectralAuditR2GraphNormCanonicalGraphSequence
        (concreteL2RawTruncationDomainSequence x))
      Filter.atTop
      (@nhds ConcreteL2GraphPairSpace concreteL2GraphNormTopology
        (x.1, concreteL2DiagonalActionL2 x))

/--
The explicit canonical graph convergence target implies the graph-norm domain
sequence target.
-/
theorem concrete_l2_raw_truncation_domain_sequence_target_of_canonical_graph_convergence
    (hconv : concreteL2RawTruncationCanonicalGraphConvergenceTarget) :
    concreteL2RawTruncationGraphNormConvergenceTarget := by
  intro x
  refine ⟨concreteL2RawTruncationDomainSequence x, ?_, ?_⟩
  · intro N
    exact concrete_l2_raw_truncation_domain_sequence_mem_finite_support_graph x N
  · exact hconv x

/--
The explicit canonical graph convergence target implies the full remaining
convergence-only frontier.
-/
theorem concrete_l2_remaining_convergence_only_of_canonical_graph_convergence
    (hconv : concreteL2RawTruncationCanonicalGraphConvergenceTarget) :
    concreteL2RawTruncationRemainingGraphNormConvergenceOnlyTarget := by
  exact concrete_l2_raw_truncation_domain_sequence_target_of_canonical_graph_convergence hconv

/-- Surface for the concrete truncation domain-sequence constructor. -/
structure ConcreteL2MathlibSpectralAuditR2GraphNormTruncationDomainSequenceConstructorSurface where
  truncationObligationBridgeReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormTruncationObligationBridgeSurfaceReady
  truncationDomainSequence :
    ConcreteL2DiagonalDomainCarrier → ℕ → ConcreteL2DiagonalDomainCarrier
  truncationDomainSequenceFiniteSupportGraph :
    ∀ x : ConcreteL2DiagonalDomainCarrier,
    ∀ N : ℕ,
      (((truncationDomainSequence x N).1,
        concreteL2DiagonalActionL2 (truncationDomainSequence x N)) ∈
          ConcreteL2FiniteSupportCoreGraphCarrier)
  canonicalGraphConvergenceTarget : Prop
  canonicalGraphConvergenceImpliesRemaining :
    canonicalGraphConvergenceTarget →
      concreteL2RawTruncationRemainingGraphNormConvergenceOnlyTarget
  boundaryNotCanonicalGraphConvergenceTheorem : Prop
  boundaryNotFullGraphNormDensityTheorem : Prop
  boundaryNotGraphNormCoreTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete surface for the truncation domain-sequence constructor. -/
def concreteL2MathlibSpectralAuditR2GraphNormTruncationDomainSequenceConstructorSurface :
    ConcreteL2MathlibSpectralAuditR2GraphNormTruncationDomainSequenceConstructorSurface :=
  { truncationObligationBridgeReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_truncation_obligation_bridge_surface_ready
    truncationDomainSequence :=
      concreteL2RawTruncationDomainSequence
    truncationDomainSequenceFiniteSupportGraph :=
      concrete_l2_raw_truncation_domain_sequence_mem_finite_support_graph
    canonicalGraphConvergenceTarget :=
      concreteL2RawTruncationCanonicalGraphConvergenceTarget
    canonicalGraphConvergenceImpliesRemaining :=
      concrete_l2_remaining_convergence_only_of_canonical_graph_convergence
    boundaryNotCanonicalGraphConvergenceTheorem := True
    boundaryNotFullGraphNormDensityTheorem := True
    boundaryNotGraphNormCoreTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotPositiveSpectralWeight := True }

/-- Readiness predicate for the truncation domain-sequence constructor. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormTruncationDomainSequenceConstructorSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormTruncationObligationBridgeSurfaceReady ∧
  (concreteL2RawTruncationCanonicalGraphConvergenceTarget →
    concreteL2RawTruncationRemainingGraphNormConvergenceOnlyTarget)

/-- Readiness theorem for the truncation domain-sequence constructor. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_truncation_domain_sequence_constructor_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormTruncationDomainSequenceConstructorSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_truncation_obligation_bridge_surface_ready,
    concrete_l2_remaining_convergence_only_of_canonical_graph_convergence⟩

end

end MathlibAnalytic
end MGAP4D