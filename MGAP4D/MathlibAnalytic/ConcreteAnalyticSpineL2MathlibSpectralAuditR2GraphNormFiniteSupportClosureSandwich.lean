import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormFiniteSupportSubsetClosure

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
The finite-support core graph carrier lies simultaneously inside the diagonal
`l2` graph carrier and inside the graph-norm-topological closure target.

This is the finite-support approximation sandwich needed before attempting the
full diagonal-graph density theorem: finite-support graph points are valid
diagonal graph points, and they are already in the target graph-norm closure.
-/
theorem concrete_l2_mathlib_spectral_audit_r2_finite_support_core_graph_subset_diagonal_inter_graph_norm_closure :
    ConcreteL2FiniteSupportCoreGraphCarrier ⊆
      (ConcreteL2DiagonalGraphL2Carrier ∩
        concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportClosureTarget) := by
  intro p hp
  exact And.intro
    (concrete_l2_finite_support_core_graph_subset_diagonal_graph_l2 hp)
    (concrete_l2_mathlib_spectral_audit_r2_finite_support_core_graph_subset_graph_norm_closure_target hp)

/-- Package for the finite-support graph closure sandwich. -/
def concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportClosureSandwichPackage : Prop :=
  ConcreteL2FiniteSupportCoreGraphCarrier ⊆
    (ConcreteL2DiagonalGraphL2Carrier ∩
      concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportClosureTarget)

/-- The finite-support graph closure sandwich package is ready. -/
theorem concrete_l2_mathlib_spectral_audit_r2_graph_norm_finite_support_closure_sandwich_package_ready :
    concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportClosureSandwichPackage := by
  exact concrete_l2_mathlib_spectral_audit_r2_finite_support_core_graph_subset_diagonal_inter_graph_norm_closure

/-- Surface for the finite-support graph closure sandwich. -/
structure ConcreteL2MathlibSpectralAuditR2GraphNormFiniteSupportClosureSandwichSurface where
  finiteSupportSubsetClosureReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormFiniteSupportSubsetClosureSurfaceReady
  finiteSupportSubsetDiagonal :
    ConcreteL2FiniteSupportCoreGraphCarrier ⊆ ConcreteL2DiagonalGraphL2Carrier
  finiteSupportSubsetGraphNormClosure :
    ConcreteL2FiniteSupportCoreGraphCarrier ⊆
      concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportClosureTarget
  finiteSupportClosureSandwich :
    concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportClosureSandwichPackage
  preciseDensityTarget : Prop
  boundaryNotGraphNormDensityTheorem : Prop
  boundaryNotGraphNormCoreTheorem : Prop
  boundaryNotClosedOperatorTheorem : Prop
  boundaryNotSelfAdjointness : Prop
  boundaryNotPVMConstruction : Prop
  boundaryNotPositiveSpectralWeight : Prop

/-- Concrete surface for the finite-support graph closure sandwich. -/
def concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportClosureSandwichSurface :
    ConcreteL2MathlibSpectralAuditR2GraphNormFiniteSupportClosureSandwichSurface :=
  { finiteSupportSubsetClosureReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_finite_support_subset_closure_surface_ready
    finiteSupportSubsetDiagonal :=
      concrete_l2_finite_support_core_graph_subset_diagonal_graph_l2
    finiteSupportSubsetGraphNormClosure :=
      concrete_l2_mathlib_spectral_audit_r2_finite_support_core_graph_subset_graph_norm_closure_target
    finiteSupportClosureSandwich :=
      concrete_l2_mathlib_spectral_audit_r2_graph_norm_finite_support_closure_sandwich_package_ready
    preciseDensityTarget :=
      concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportDensityPreciseTarget
    boundaryNotGraphNormDensityTheorem := True
    boundaryNotGraphNormCoreTheorem := True
    boundaryNotClosedOperatorTheorem := True
    boundaryNotSelfAdjointness := True
    boundaryNotPVMConstruction := True
    boundaryNotPositiveSpectralWeight := True }

/-- Readiness predicate for the finite-support graph closure sandwich. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormFiniteSupportClosureSandwichSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormFiniteSupportSubsetClosureSurfaceReady ∧
  (ConcreteL2FiniteSupportCoreGraphCarrier ⊆ ConcreteL2DiagonalGraphL2Carrier) ∧
  concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportSubsetClosurePackage ∧
  concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportClosureSandwichPackage ∧
  concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportDensityPreciseTarget =
    (ConcreteL2DiagonalGraphL2Carrier ⊆
      concreteL2MathlibSpectralAuditR2GraphNormFiniteSupportClosureTarget)

/-- Readiness theorem for the finite-support graph closure sandwich. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_finite_support_closure_sandwich_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormFiniteSupportClosureSandwichSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_finite_support_subset_closure_surface_ready,
    concrete_l2_finite_support_core_graph_subset_diagonal_graph_l2,
    concrete_l2_mathlib_spectral_audit_r2_graph_norm_finite_support_subset_closure_package_ready,
    concrete_l2_mathlib_spectral_audit_r2_graph_norm_finite_support_closure_sandwich_package_ready,
    rfl⟩

end

end MathlibAnalytic
end MGAP4D