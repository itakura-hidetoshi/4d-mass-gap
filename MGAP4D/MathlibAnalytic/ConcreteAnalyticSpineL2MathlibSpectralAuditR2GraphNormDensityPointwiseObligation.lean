import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormClosureZeroWitness

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
Pointwise form of the graph-norm finite-support density target.

The precise target is a subset statement.  This pointwise form is the form needed
for the next proof layer: fix an arbitrary diagonal graph point and prove that it
belongs to the graph-norm closure target.
-/
def concreteL2MathlibSpectralAuditR2GraphNormDensityPointwiseObligation : Prop :=
  ∀ p : ConcreteL2GraphPairSpace,
    p ∈ ConcreteL2DiagonalGraphL2Carrier →
      p ∈ concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportClosureTarget

/-- The subset-form density target and the pointwise obligation are equivalent. -/
theorem concrete_l2_mathlib_spectral_audit_r2_graph_norm_density_precise_target_iff_pointwise_obligation :
    concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportDensityPreciseTarget ↔
      concreteL2MathlibSpectralAuditR2GraphNormDensityPointwiseObligation := by
  constructor
  · intro h p hp
    exact h hp
  · intro h p hp
    exact h p hp

/-- If the pointwise obligation is supplied, then the precise graph-norm density target is closed. -/
theorem concrete_l2_mathlib_spectral_audit_r2_graph_norm_density_precise_target_of_pointwise_obligation
    (h : concreteL2MathlibSpectralAuditR2GraphNormDensityPointwiseObligation) :
    concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportDensityPreciseTarget := by
  exact (concrete_l2_mathlib_spectral_audit_r2_graph_norm_density_precise_target_iff_pointwise_obligation).mpr h

/-- Surface for the pointwise graph-norm density obligation. -/
structure ConcreteL2MathlibSpectralAuditR2GraphNormDensityPointwiseObligationSurface where
  closureZeroWitnessReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormClosureZeroWitnessSurfaceReady
  pointwiseObligation : Prop
  preciseTargetIffPointwise :
    concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportDensityPreciseTarget ↔
      concreteL2MathlibSpectralAuditR2GraphNormDensityPointwiseObligation
  zeroWitness :
    (concreteL2RealZero, concreteL2RealZero) ∈
      (ConcreteL2DiagonalGraphL2Carrier ∩
        concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportClosureTarget)
  boundaryNotGraphNormDensityTheorem : Prop
  boundaryNotGraphNormCoreTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete surface for the pointwise graph-norm density obligation. -/
def concreteL2MathlibSpectralAuditR2GraphNormDensityPointwiseObligationSurface :
    ConcreteL2MathlibSpectralAuditR2GraphNormDensityPointwiseObligationSurface :=
  { closureZeroWitnessReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_closure_zero_witness_surface_ready
    pointwiseObligation :=
      concreteL2MathlibSpectralAuditR2GraphNormDensityPointwiseObligation
    preciseTargetIffPointwise :=
      concrete_l2_mathlib_spectral_audit_r2_graph_norm_density_precise_target_iff_pointwise_obligation
    zeroWitness :=
      concrete_l2_mathlib_spectral_audit_r2_zero_graph_mem_diagonal_inter_graph_norm_closure
    boundaryNotGraphNormDensityTheorem := True
    boundaryNotGraphNormCoreTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotPositiveSpectralWeight := True }

/-- Readiness predicate for the pointwise graph-norm density obligation. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormDensityPointwiseObligationSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormClosureZeroWitnessSurfaceReady ∧
  (concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportDensityPreciseTarget ↔
    concreteL2MathlibSpectralAuditR2GraphNormDensityPointwiseObligation) ∧
  ((concreteL2RealZero, concreteL2RealZero) ∈
    (ConcreteL2DiagonalGraphL2Carrier ∩
      concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportClosureTarget))

/-- Readiness theorem for the pointwise graph-norm density obligation. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_density_pointwise_obligation_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormDensityPointwiseObligationSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_closure_zero_witness_surface_ready,
    concrete_l2_mathlib_spectral_audit_r2_graph_norm_density_precise_target_iff_pointwise_obligation,
    concrete_l2_mathlib_spectral_audit_r2_zero_graph_mem_diagonal_inter_graph_norm_closure⟩

end

end MathlibAnalytic
end MGAP4D