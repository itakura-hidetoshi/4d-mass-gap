import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormDensityDomainObligation

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
Graph-norm finite-support approximation sequence target for one diagonal-domain
point.

The topology is supplied explicitly through `@nhds ... concreteL2GraphNormTopology`.
Thus this target does not install a global topology or pseudo-metric instance.
-/
def concreteL2MathlibSpectralAuditR2GraphNormApproximationSequenceTarget
    (x : ConcreteL2DiagonalDomainCarrier) : Prop :=
  ∃ u : ℕ → ConcreteL2GraphPairSpace,
    (∀ n : ℕ, u n ∈ ConcreteL2FiniteSupportCoreGraphCarrier) ∧
      Filter.Tendsto u Filter.atTop
        (@nhds ConcreteL2GraphPairSpace concreteL2GraphNormTopology
          (x.1, concreteL2DiagonalActionL2 x))

/--
Global sequence approximation target for the graph-norm finite-support density
lane.

This is the constructive target that should eventually imply the domain
obligation: every canonical diagonal graph pair is the graph-norm limit of a
finite-support core graph sequence.
-/
def concreteL2MathlibSpectralAuditR2GraphNormDensitySequenceTarget : Prop :=
  ∀ x : ConcreteL2DiagonalDomainCarrier,
    concreteL2MathlibSpectralAuditR2GraphNormApproximationSequenceTarget x

/--
The next bridge obligation: sequence approximation should imply membership in
the graph-norm closure target.

This file records the exact implication target without yet using the mathlib
`Tendsto`-to-closure API.  The next layer can discharge this once the correct
closure lemma is fixed.
-/
def concreteL2MathlibSpectralAuditR2GraphNormSequenceToClosureObligation : Prop :=
  concreteL2MathlibSpectralAuditR2GraphNormDensitySequenceTarget →
    concreteL2MathlibSpectralAuditR2GraphNormDensityDomainObligation

/-- Surface for the graph-norm finite-support approximation sequence target. -/
structure ConcreteL2MathlibSpectralAuditR2GraphNormDensitySequenceTargetSurface where
  domainObligationReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormDensityDomainObligationSurfaceReady
  sequenceTarget : Prop
  sequenceToClosureObligation : Prop
  domainObligation : Prop
  preciseDensityTarget : Prop
  boundaryNotGraphNormDensityTheorem : Prop
  boundaryNotGraphNormCoreTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete surface for the graph-norm finite-support approximation sequence target. -/
def concreteL2MathlibSpectralAuditR2GraphNormDensitySequenceTargetSurface :
    ConcreteL2MathlibSpectralAuditR2GraphNormDensitySequenceTargetSurface :=
  { domainObligationReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_density_domain_obligation_surface_ready
    sequenceTarget :=
      concreteL2MathlibSpectralAuditR2GraphNormDensitySequenceTarget
    sequenceToClosureObligation :=
      concreteL2MathlibSpectralAuditR2GraphNormSequenceToClosureObligation
    domainObligation :=
      concreteL2MathlibSpectralAuditR2GraphNormDensityDomainObligation
    preciseDensityTarget :=
      concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportDensityPreciseTarget
    boundaryNotGraphNormDensityTheorem := True
    boundaryNotGraphNormCoreTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotPositiveSpectralWeight := True }

/-- Readiness predicate for the graph-norm finite-support approximation sequence target. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormDensitySequenceTargetSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormDensityDomainObligationSurfaceReady ∧
  concreteL2MathlibSpectralAuditR2GraphNormSequenceToClosureObligation ∧
  (concreteL2MathlibSpectralAuditR2GraphNormDensityDomainObligation →
    concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportDensityPreciseTarget)

/--
Readiness theorem for the graph-norm finite-support approximation sequence
target, conditional on the sequence-to-closure bridge obligation.
-/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_density_sequence_target_surface_ready
    (hseq : concreteL2MathlibSpectralAuditR2GraphNormSequenceToClosureObligation) :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormDensitySequenceTargetSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_density_domain_obligation_surface_ready,
    hseq,
    concrete_l2_mathlib_spectral_audit_r2_graph_norm_density_precise_target_of_domain_obligation⟩

end

end MathlibAnalytic
end MGAP4D