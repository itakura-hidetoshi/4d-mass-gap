import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormSequenceToClosureBridge

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
The canonical zero diagonal graph pair is a finite-support core graph point.

The existing finite-support witness is stated for `(0,0)`.  This lemma transports
that witness across the already-established equality between `(0,0)` and the
canonical graph pair `(x, A x)` at the zero domain point.
-/
theorem concrete_l2_mathlib_spectral_audit_r2_zero_canonical_graph_mem_finite_support_core :
    (concreteL2DiagonalDomainZero.1,
      concreteL2DiagonalActionL2 concreteL2DiagonalDomainZero) ∈
      ConcreteL2FiniteSupportCoreGraphCarrier := by
  exact concrete_l2_diagonal_zero_graph_l2_pair_eq ▸
    concrete_l2_finite_support_core_zero_graph_mem

/--
The zero domain point has a concrete finite-support approximation sequence in
the graph-norm topology: the constant zero canonical graph sequence.
-/
theorem concrete_l2_mathlib_spectral_audit_r2_graph_norm_zero_approximation_sequence_target :
    concreteL2MathlibSpectralAuditR2GraphNormApproximationSequenceTarget
      concreteL2DiagonalDomainZero := by
  letI : TopologicalSpace ConcreteL2GraphPairSpace := concreteL2GraphNormTopology
  refine ⟨
    fun _ : ℕ =>
      (concreteL2DiagonalDomainZero.1,
        concreteL2DiagonalActionL2 concreteL2DiagonalDomainZero),
    ?_, ?_⟩
  · intro _n
    exact concrete_l2_mathlib_spectral_audit_r2_zero_canonical_graph_mem_finite_support_core
  · exact tendsto_const_nhds

/--
The zero domain point satisfies the domain-parametric graph-norm density
obligation.
-/
theorem concrete_l2_mathlib_spectral_audit_r2_graph_norm_zero_domain_obligation_point :
    (concreteL2DiagonalDomainZero.1,
      concreteL2DiagonalActionL2 concreteL2DiagonalDomainZero) ∈
      concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportClosureTarget := by
  exact concrete_l2_mathlib_spectral_audit_r2_graph_norm_sequence_to_closure_for_domain_point
    concrete_l2_mathlib_spectral_audit_r2_graph_norm_zero_approximation_sequence_target

/-- Surface for the zero graph-norm approximation sequence. -/
structure ConcreteL2MathlibSpectralAuditR2GraphNormZeroSequenceApproximationSurface where
  sequenceToClosureBridgeReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormSequenceToClosureBridgeSurfaceReady
  zeroCanonicalGraphMemFiniteSupportCore :
    (concreteL2DiagonalDomainZero.1,
      concreteL2DiagonalActionL2 concreteL2DiagonalDomainZero) ∈
      ConcreteL2FiniteSupportCoreGraphCarrier
  zeroApproximationSequenceTarget :
    concreteL2MathlibSpectralAuditR2GraphNormApproximationSequenceTarget
      concreteL2DiagonalDomainZero
  zeroDomainClosureMembership :
    (concreteL2DiagonalDomainZero.1,
      concreteL2DiagonalActionL2 concreteL2DiagonalDomainZero) ∈
      concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportClosureTarget
  boundaryNotFullGraphNormDensityTheorem : Prop
  boundaryNotGraphNormCoreTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete surface for the zero graph-norm approximation sequence. -/
def concreteL2MathlibSpectralAuditR2GraphNormZeroSequenceApproximationSurface :
    ConcreteL2MathlibSpectralAuditR2GraphNormZeroSequenceApproximationSurface :=
  { sequenceToClosureBridgeReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_sequence_to_closure_bridge_surface_ready
    zeroCanonicalGraphMemFiniteSupportCore :=
      concrete_l2_mathlib_spectral_audit_r2_zero_canonical_graph_mem_finite_support_core
    zeroApproximationSequenceTarget :=
      concrete_l2_mathlib_spectral_audit_r2_graph_norm_zero_approximation_sequence_target
    zeroDomainClosureMembership :=
      concrete_l2_mathlib_spectral_audit_r2_graph_norm_zero_domain_obligation_point
    boundaryNotFullGraphNormDensityTheorem := True
    boundaryNotGraphNormCoreTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotPositiveSpectralWeight := True }

/-- Readiness predicate for the zero graph-norm approximation sequence. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormZeroSequenceApproximationSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormSequenceToClosureBridgeSurfaceReady ∧
  ((concreteL2DiagonalDomainZero.1,
    concreteL2DiagonalActionL2 concreteL2DiagonalDomainZero) ∈
      ConcreteL2FiniteSupportCoreGraphCarrier) ∧
  concreteL2MathlibSpectralAuditR2GraphNormApproximationSequenceTarget
    concreteL2DiagonalDomainZero ∧
  ((concreteL2DiagonalDomainZero.1,
    concreteL2DiagonalActionL2 concreteL2DiagonalDomainZero) ∈
      concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportClosureTarget)

/-- Readiness theorem for the zero graph-norm approximation sequence. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_zero_sequence_approximation_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormZeroSequenceApproximationSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_sequence_to_closure_bridge_surface_ready,
    concrete_l2_mathlib_spectral_audit_r2_zero_canonical_graph_mem_finite_support_core,
    concrete_l2_mathlib_spectral_audit_r2_graph_norm_zero_approximation_sequence_target,
    concrete_l2_mathlib_spectral_audit_r2_graph_norm_zero_domain_obligation_point⟩

end

end MathlibAnalytic
end MGAP4D