import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormFiniteSupportConstantSequence

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
Every finite-support core graph point has a diagonal-domain witness whose
canonical graph pair admits the graph-norm finite-support approximation sequence.

This packages the already-proved facts:
1. finite-support core graph points are diagonal graph points;
2. finite-support canonical graph pairs admit constant graph-norm approximation
   sequences.
-/
theorem concrete_l2_mathlib_spectral_audit_r2_finite_support_graph_point_has_approximating_domain_witness
    {p : ConcreteL2GraphPairSpace}
    (hp : p ∈ ConcreteL2FiniteSupportCoreGraphCarrier) :
    ∃ x : ConcreteL2DiagonalDomainCarrier,
      p = (x.1, concreteL2DiagonalActionL2 x) ∧
        concreteL2MathlibSpectralAuditR2GraphNormApproximationSequenceTarget x := by
  have hpdiag : p ∈ ConcreteL2DiagonalGraphL2Carrier :=
    concrete_l2_finite_support_core_graph_subset_diagonal_graph_l2 hp
  rcases hpdiag with ⟨x, hpx⟩
  refine ⟨x, hpx, ?_⟩
  exact concrete_l2_mathlib_spectral_audit_r2_graph_norm_constant_sequence_target_of_finite_support_core
    (hpx ▸ hp)

/--
Every finite-support core graph point has a diagonal-domain witness whose
canonical graph pair belongs to the graph-norm closure target.
-/
theorem concrete_l2_mathlib_spectral_audit_r2_finite_support_graph_point_has_closure_domain_witness
    {p : ConcreteL2GraphPairSpace}
    (hp : p ∈ ConcreteL2FiniteSupportCoreGraphCarrier) :
    ∃ x : ConcreteL2DiagonalDomainCarrier,
      p = (x.1, concreteL2DiagonalActionL2 x) ∧
        (x.1, concreteL2DiagonalActionL2 x) ∈
          concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportClosureTarget := by
  rcases concrete_l2_mathlib_spectral_audit_r2_finite_support_graph_point_has_approximating_domain_witness hp with
    ⟨x, hpx, hxseq⟩
  exact ⟨x, hpx,
    concrete_l2_mathlib_spectral_audit_r2_graph_norm_sequence_to_closure_for_domain_point hxseq⟩

/--
Witness package for finite-support graph points in the graph-norm sequence lane.
-/
def concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportWitnessSequencePackage : Prop :=
  ∀ {p : ConcreteL2GraphPairSpace},
    p ∈ ConcreteL2FiniteSupportCoreGraphCarrier →
      ∃ x : ConcreteL2DiagonalDomainCarrier,
        p = (x.1, concreteL2DiagonalActionL2 x) ∧
          concreteL2MathlibSpectralAuditR2GraphNormApproximationSequenceTarget x

/-- The finite-support witness sequence package is ready. -/
theorem concrete_l2_mathlib_spectral_audit_r2_graph_norm_finite_support_witness_sequence_package_ready :
    concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportWitnessSequencePackage := by
  intro p hp
  exact concrete_l2_mathlib_spectral_audit_r2_finite_support_graph_point_has_approximating_domain_witness hp

/-- Surface for the finite-support witness sequence layer. -/
structure ConcreteL2MathlibSpectralAuditR2GraphNormFiniteSupportWitnessSequenceSurface where
  finiteSupportConstantSequenceReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormFiniteSupportConstantSequenceSurfaceReady
  finiteSupportWitnessSequencePackage :
    concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportWitnessSequencePackage
  boundaryNotArbitraryApproximationSequenceExistence : Prop
  boundaryNotFullGraphNormDensityTheorem : Prop
  boundaryNotGraphNormCoreTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete surface for the finite-support witness sequence layer. -/
def concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportWitnessSequenceSurface :
    ConcreteL2MathlibSpectralAuditR2GraphNormFiniteSupportWitnessSequenceSurface :=
  { finiteSupportConstantSequenceReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_finite_support_constant_sequence_surface_ready
    finiteSupportWitnessSequencePackage :=
      concrete_l2_mathlib_spectral_audit_r2_graph_norm_finite_support_witness_sequence_package_ready
    boundaryNotArbitraryApproximationSequenceExistence := True
    boundaryNotFullGraphNormDensityTheorem := True
    boundaryNotGraphNormCoreTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotPositiveSpectralWeight := True }

/-- Readiness predicate for the finite-support witness sequence layer. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormFiniteSupportWitnessSequenceSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormFiniteSupportConstantSequenceSurfaceReady ∧
  concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportWitnessSequencePackage

/-- Readiness theorem for the finite-support witness sequence layer. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_finite_support_witness_sequence_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormFiniteSupportWitnessSequenceSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_finite_support_constant_sequence_surface_ready,
    concrete_l2_mathlib_spectral_audit_r2_graph_norm_finite_support_witness_sequence_package_ready⟩

end

end MathlibAnalytic
end MGAP4D