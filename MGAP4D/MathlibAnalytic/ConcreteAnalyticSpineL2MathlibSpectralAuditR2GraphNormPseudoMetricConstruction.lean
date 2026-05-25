import Mathlib.Topology.MetricSpace.Pseudo.Defs
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormPseudoMetricHandoff

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal lp

noncomputable section

/--
Explicit pseudo-metric-space structure induced by the graph-norm distance
candidate.

This is intentionally provided as a named definition, not as a global instance.
The purpose is to expose the exact mathlib structure while avoiding premature
instance search effects in downstream analytic lanes.
-/
def concreteL2GraphNormPseudoMetricSpace :
    PseudoMetricSpace ConcreteL2GraphPairSpace where
  dist := concreteL2GraphNormDistanceCandidate
  dist_self := concrete_l2_graph_norm_distance_candidate_self
  dist_comm := concrete_l2_graph_norm_distance_candidate_symm
  dist_triangle := concrete_l2_graph_norm_distance_candidate_triangle

/-- The induced pseudo-metric structure has the expected distance definition. -/
theorem concrete_l2_graph_norm_pseudo_metric_space_dist_eq
    (p q : ConcreteL2GraphPairSpace) :
    concreteL2GraphNormPseudoMetricSpace.dist p q =
      concreteL2GraphNormDistanceCandidate p q := by
  rfl

/-- Package: explicit graph-norm pseudo-metric-space construction. -/
def concreteL2MathlibSpectralAuditR2GraphNormPseudoMetricConstruction : Prop :=
  ∃ m : PseudoMetricSpace ConcreteL2GraphPairSpace,
    ∀ p q : ConcreteL2GraphPairSpace,
      m.dist p q = concreteL2GraphNormDistanceCandidate p q

/-- The explicit graph-norm pseudo-metric-space construction is ready. -/
theorem concrete_l2_mathlib_spectral_audit_r2_graph_norm_pseudo_metric_construction :
    concreteL2MathlibSpectralAuditR2GraphNormPseudoMetricConstruction := by
  refine ⟨concreteL2GraphNormPseudoMetricSpace, ?_⟩
  intro p q
  rfl

/-- Topology surface obtained from the named pseudo-metric structure. -/
def concreteL2GraphNormTopology : TopologicalSpace ConcreteL2GraphPairSpace :=
  concreteL2GraphNormPseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- The named graph-norm topology is the topology induced by the named pseudo-metric structure. -/
theorem concrete_l2_graph_norm_topology_eq :
    concreteL2GraphNormTopology =
      concreteL2GraphNormPseudoMetricSpace.toUniformSpace.toTopologicalSpace := by
  rfl

/-- Package: explicit graph-norm topology construction from the named pseudo-metric structure. -/
def concreteL2MathlibSpectralAuditR2GraphNormTopologyConstruction : Prop :=
  ∃ t : TopologicalSpace ConcreteL2GraphPairSpace,
    t = concreteL2GraphNormPseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- The explicit graph-norm topology construction package is ready. -/
theorem concrete_l2_mathlib_spectral_audit_r2_graph_norm_topology_construction :
    concreteL2MathlibSpectralAuditR2GraphNormTopologyConstruction := by
  exact ⟨concreteL2GraphNormTopology, rfl⟩

/-- Surface for the explicit graph-norm pseudo-metric/topology construction. -/
structure ConcreteL2MathlibSpectralAuditR2GraphNormPseudoMetricConstructionSurface where
  handoffReady :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormPseudoMetricHandoffSurfaceReady
  pseudoMetricConstruction : concreteL2MathlibSpectralAuditR2GraphNormPseudoMetricConstruction
  topologyConstruction : concreteL2MathlibSpectralAuditR2GraphNormTopologyConstruction
  dist_eq : ∀ p q : ConcreteL2GraphPairSpace,
    concreteL2GraphNormPseudoMetricSpace.dist p q =
      concreteL2GraphNormDistanceCandidate p q
  boundaryNotGlobalInstance : Prop
  boundaryNotDensity : Prop
  boundaryNotCore : Prop

/-- Concrete surface for the explicit graph-norm pseudo-metric/topology construction. -/
def concreteL2MathlibSpectralAuditR2GraphNormPseudoMetricConstructionSurface :
    ConcreteL2MathlibSpectralAuditR2GraphNormPseudoMetricConstructionSurface :=
  { handoffReady :=
      concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_pseudo_metric_handoff_surface_ready
    pseudoMetricConstruction :=
      concrete_l2_mathlib_spectral_audit_r2_graph_norm_pseudo_metric_construction
    topologyConstruction :=
      concrete_l2_mathlib_spectral_audit_r2_graph_norm_topology_construction
    dist_eq := concrete_l2_graph_norm_pseudo_metric_space_dist_eq
    boundaryNotGlobalInstance := True
    boundaryNotDensity := True
    boundaryNotCore := True }

/-- Readiness predicate for the explicit graph-norm pseudo-metric/topology construction. -/
def concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormPseudoMetricConstructionSurfaceReady : Prop :=
  concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormPseudoMetricHandoffSurfaceReady ∧
  concreteL2MathlibSpectralAuditR2GraphNormPseudoMetricConstruction ∧
  concreteL2MathlibSpectralAuditR2GraphNormTopologyConstruction

/-- Readiness theorem for the explicit graph-norm pseudo-metric/topology construction. -/
theorem concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_pseudo_metric_construction_surface_ready :
    concreteAnalyticSpineL2MathlibSpectralAuditR2GraphNormPseudoMetricConstructionSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_mathlib_spectral_audit_r2_graph_norm_pseudo_metric_handoff_surface_ready,
    concrete_l2_mathlib_spectral_audit_r2_graph_norm_pseudo_metric_construction,
    concrete_l2_mathlib_spectral_audit_r2_graph_norm_topology_construction⟩

end

end MathlibAnalytic
end MGAP4D