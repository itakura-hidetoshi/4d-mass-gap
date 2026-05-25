import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormZeroSequenceApproximation

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
Any canonical diagonal graph pair that is already in the finite-support core
admits a graph-norm finite-support approximation sequence: the constant sequence
at that graph pair.

This is the general constant-sequence layer behind the zero witness.  It does
not assert that every diagonal-domain point is finite-support; that remains the
future approximation theorem.
-/
theorem concrete_l2_mathlib_spectral_audit_r2_graph_norm_constant_sequence_target_of_finite_support_core
    {x : ConcreteL2DiagonalDomainCarrier}
    (hx : (x.1, concreteL2DiagonalActionL2 x) ∈ ConcreteL2FiniteSupportCoreGraphCarrier) :
    concreteL2MathlibSpectralAuditR2GraphNormApproximationSequenceTarget x := by
  letI : TopologicalSpace ConcreteL2GraphPairSpace := concreteL2GraphNormTopology
  refine ⟨
    fun _ : ℕ => (x.1, concreteL2DiagonalActionL2 x),
    ?_, ?_⟩
  · intro _n
    exact hx
  · exact tendsto_const_nhds

/--
Any canonical diagonal graph pair already in the finite-support core belongs to
the graph-norm closure target.
-/
theorem concrete_l2_mathlib_spectral_audit_r2_graph_norm_closure_membership_of_finite_support_core
    {x : ConcreteL2DiagonalDomainCarrier}
    (hx : (x.1, concreteL2DiagonalActionL2 x) ∈ ConcreteL2FiniteSupportCoreGraphCarrier) :
    (x.1, concreteL2DiagonalActionL2 x) ∈
      concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportClosureTarget := by
  exact concrete_l2_mathlib_spectral_audit_r2_graph_norm_sequence_to_closure_for_domain_point
    (concrete_l2_mathlib_spectral_audit_r2_graph_norm_constant_sequence_target_of_finite_support_core hx)

/--
Finite-support canonical graph pairs satisfy the domain-parametric graph-norm
density obligation pointwise.
-/
def concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportPointwiseDomainObligation : Prop :=
  ∀ x : ConcreteL2DiagonalDomainCarrier,
    (x.1, concreteL2DiagonalActionL2 x) ∈ ConcreteL2FiniteSupportCoreGraphCarrier →
      (x.1, concreteL2DiagonalActionL2 x) ∈
        concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportClosureTarget

/-- The finite-support pointwise domain obligation is ready. -/
theorem concrete_l2_mathlib_spectral_audit_r2_graph_norm_finite_support_pointwise_domain_obligation_ready :
    concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportPointwiseDomainObligation := by
  intro x hx
  exact concrete_l2_mathlib_spectral_audit_r2_graph_norm_closure_membership_of_finite_support_core hx

/-- Surface for the finite-support constant-sequence graph-norm layer. -/
structure ConcreteL2MathlibSpectralAuditR2GraphNormFiniteSupportConstantSequenceSurface where
  zeroSequenceApproximationReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormZeroSequenceApproximationSurfaceReady
  finiteSupportPointwiseObligation :
    concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportPointwiseDomainObligation
  zeroCaseRecovered :
    concreteL2MathlibSpectralAuditR2GraphNormApproximationSequenceTarget
      concreteL2DiagonalDomainZero
  boundaryNotArbitraryApproximationSequenceExistence : Prop
  boundaryNotFullGraphNormDensityTheorem : Prop
  boundaryNotGraphNormCoreTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete surface for the finite-support constant-sequence graph-norm layer. -/
def concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportConstantSequenceSurface :
    ConcreteL2MathlibSpectralAuditR2GraphNormFiniteSupportConstantSequenceSurface :=
  { zeroSequenceApproximationReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_zero_sequence_approximation_surface_ready
    finiteSupportPointwiseObligation :=
      concrete_l2_mathlib_spectral_audit_r2_graph_norm_finite_support_pointwise_domain_obligation_ready
    zeroCaseRecovered :=
      concrete_l2_mathlib_spectral_audit_r2_graph_norm_zero_approximation_sequence_target
    boundaryNotArbitraryApproximationSequenceExistence := True
    boundaryNotFullGraphNormDensityTheorem := True
    boundaryNotGraphNormCoreTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotPositiveSpectralWeight := True }

/-- Readiness predicate for the finite-support constant-sequence graph-norm layer. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormFiniteSupportConstantSequenceSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormZeroSequenceApproximationSurfaceReady ∧
  concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportPointwiseDomainObligation ∧
  concreteL2MathlibSpectralAuditR2GraphNormApproximationSequenceTarget
    concreteL2DiagonalDomainZero

/-- Readiness theorem for the finite-support constant-sequence graph-norm layer. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_finite_support_constant_sequence_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormFiniteSupportConstantSequenceSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_zero_sequence_approximation_surface_ready,
    concrete_l2_mathlib_spectral_audit_r2_graph_norm_finite_support_pointwise_domain_obligation_ready,
    concrete_l2_mathlib_spectral_audit_r2_graph_norm_zero_approximation_sequence_target⟩

end

end MathlibAnalytic
end MGAP4D