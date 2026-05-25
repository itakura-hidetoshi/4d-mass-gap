import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormDensityTargetRefinement

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
The finite-support core graph carrier is contained in its graph-norm-topological
closure target.

This is the first genuine closure lemma in the graph-norm density lane.  It uses
mathlib's `subset_closure` with the named graph-norm topology supplied
explicitly, so no global topology or pseudo-metric instance is installed.
-/
theorem concrete_l2_mathlib_spectral_audit_r2_finite_support_core_graph_subset_graph_norm_closure_target :
    ConcreteL2FiniteSupportCoreGraphCarrier ⊆
      concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportClosureTarget := by
  unfold concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportClosureTarget
  exact @subset_closure ConcreteL2GraphPairSpace concreteL2GraphNormTopology
    ConcreteL2FiniteSupportCoreGraphCarrier

/-- Package for the finite-support-core inclusion into the graph-norm closure. -/
def concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportSubsetClosurePackage : Prop :=
  ConcreteL2FiniteSupportCoreGraphCarrier ⊆
    concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportClosureTarget

/-- The finite-support-core inclusion into the graph-norm closure is ready. -/
theorem concrete_l2_mathlib_spectral_audit_r2_graph_norm_finite_support_subset_closure_package_ready :
    concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportSubsetClosurePackage := by
  exact concrete_l2_mathlib_spectral_audit_r2_finite_support_core_graph_subset_graph_norm_closure_target

/-- Surface for the finite-support-core subset-of-closure layer. -/
structure ConcreteL2MathlibSpectralAuditR2GraphNormFiniteSupportSubsetClosureSurface where
  densityTargetRefinementReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormDensityTargetRefinementSurfaceReady
  finiteSupportSubsetClosure :
    concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportSubsetClosurePackage
  preciseDensityTarget : Prop
  boundaryNotGraphNormDensityTheorem : Prop
  boundaryNotGraphNormCoreTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete surface for the finite-support-core subset-of-closure layer. -/
def concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportSubsetClosureSurface :
    ConcreteL2MathlibSpectralAuditR2GraphNormFiniteSupportSubsetClosureSurface :=
  { densityTargetRefinementReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_density_target_refinement_surface_ready
    finiteSupportSubsetClosure :=
      concrete_l2_mathlib_spectral_audit_r2_graph_norm_finite_support_subset_closure_package_ready
    preciseDensityTarget :=
      concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportDensityPreciseTarget
    boundaryNotGraphNormDensityTheorem := True
    boundaryNotGraphNormCoreTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotPositiveSpectralWeight := True }

/-- Readiness predicate for the finite-support-core subset-of-closure layer. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormFiniteSupportSubsetClosureSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormDensityTargetRefinementSurfaceReady ∧
  concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportSubsetClosurePackage ∧
  concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportDensityPreciseTarget =
    (ConcreteL2DiagonalGraphL2Carrier ⊆
      concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportClosureTarget)

/-- Readiness theorem for the finite-support-core subset-of-closure layer. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_finite_support_subset_closure_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormFiniteSupportSubsetClosureSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_density_target_refinement_surface_ready,
    concrete_l2_mathlib_spectral_audit_r2_graph_norm_finite_support_subset_closure_package_ready,
    rfl⟩

end

end MathlibAnalytic
end MGAP4D