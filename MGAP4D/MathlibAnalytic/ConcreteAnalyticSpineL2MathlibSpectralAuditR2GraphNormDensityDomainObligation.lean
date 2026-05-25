import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormDensityPointwiseObligation

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
Domain-parametric form of the graph-norm finite-support density obligation.

Instead of quantifying over arbitrary graph-pair points and then unpacking
membership in the diagonal graph, this target fixes a diagonal-domain point `x`
and asks for the canonical graph pair `(x, A x)` to lie in the graph-norm closure
target.
-/
def concreteL2MathlibSpectralAuditR2GraphNormDensityDomainObligation : Prop :=
  ∀ x : ConcreteL2DiagonalDomainCarrier,
    (x.1, concreteL2DiagonalActionL2 x) ∈
      concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportClosureTarget

/-- The pointwise diagonal-graph obligation and the domain-parametric obligation are equivalent. -/
theorem concrete_l2_mathlib_spectral_audit_r2_graph_norm_density_pointwise_iff_domain_obligation :
    concreteL2MathlibSpectralAuditR2GraphNormDensityPointwiseObligation ↔
      concreteL2MathlibSpectralAuditR2GraphNormDensityDomainObligation := by
  constructor
  · intro h x
    exact h (x.1, concreteL2DiagonalActionL2 x) ⟨x, rfl⟩
  · intro h p hp
    rcases hp with ⟨x, rfl⟩
    exact h x

/-- If the domain-parametric obligation is supplied, then the pointwise obligation is closed. -/
theorem concrete_l2_mathlib_spectral_audit_r2_graph_norm_density_pointwise_of_domain_obligation
    (h : concreteL2MathlibSpectralAuditR2GraphNormDensityDomainObligation) :
    concreteL2MathlibSpectralAuditR2GraphNormDensityPointwiseObligation := by
  exact (concrete_l2_mathlib_spectral_audit_r2_graph_norm_density_pointwise_iff_domain_obligation).mpr h

/-- If the domain-parametric obligation is supplied, then the precise density target is closed. -/
theorem concrete_l2_mathlib_spectral_audit_r2_graph_norm_density_precise_target_of_domain_obligation
    (h : concreteL2MathlibSpectralAuditR2GraphNormDensityDomainObligation) :
    concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportDensityPreciseTarget := by
  exact concrete_l2_mathlib_spectral_audit_r2_graph_norm_density_precise_target_of_pointwise_obligation
    (concrete_l2_mathlib_spectral_audit_r2_graph_norm_density_pointwise_of_domain_obligation h)

/-- Surface for the domain-parametric graph-norm density obligation. -/
structure ConcreteL2MathlibSpectralAuditR2GraphNormDensityDomainObligationSurface where
  pointwiseObligationReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormDensityPointwiseObligationSurfaceReady
  domainObligation : Prop
  pointwiseIffDomain :
    concreteL2MathlibSpectralAuditR2GraphNormDensityPointwiseObligation ↔
      concreteL2MathlibSpectralAuditR2GraphNormDensityDomainObligation
  domainImpliesPreciseTarget :
    concreteL2MathlibSpectralAuditR2GraphNormDensityDomainObligation →
      concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportDensityPreciseTarget
  boundaryNotGraphNormDensityTheorem : Prop
  boundaryNotGraphNormCoreTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete surface for the domain-parametric graph-norm density obligation. -/
def concreteL2MathlibSpectralAuditR2GraphNormDensityDomainObligationSurface :
    ConcreteL2MathlibSpectralAuditR2GraphNormDensityDomainObligationSurface :=
  { pointwiseObligationReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_density_pointwise_obligation_surface_ready
    domainObligation :=
      concreteL2MathlibSpectralAuditR2GraphNormDensityDomainObligation
    pointwiseIffDomain :=
      concrete_l2_mathlib_spectral_audit_r2_graph_norm_density_pointwise_iff_domain_obligation
    domainImpliesPreciseTarget :=
      concrete_l2_mathlib_spectral_audit_r2_graph_norm_density_precise_target_of_domain_obligation
    boundaryNotGraphNormDensityTheorem := True
    boundaryNotGraphNormCoreTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotPositiveSpectralWeight := True }

/-- Readiness predicate for the domain-parametric graph-norm density obligation. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormDensityDomainObligationSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormDensityPointwiseObligationSurfaceReady ∧
  (concreteL2MathlibSpectralAuditR2GraphNormDensityPointwiseObligation ↔
    concreteL2MathlibSpectralAuditR2GraphNormDensityDomainObligation) ∧
  (concreteL2MathlibSpectralAuditR2GraphNormDensityDomainObligation →
    concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportDensityPreciseTarget)

/-- Readiness theorem for the domain-parametric graph-norm density obligation. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_density_domain_obligation_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormDensityDomainObligationSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_density_pointwise_obligation_surface_ready,
    concrete_l2_mathlib_spectral_audit_r2_graph_norm_density_pointwise_iff_domain_obligation,
    concrete_l2_mathlib_spectral_audit_r2_graph_norm_density_precise_target_of_domain_obligation⟩

end

end MathlibAnalytic
end MGAP4D