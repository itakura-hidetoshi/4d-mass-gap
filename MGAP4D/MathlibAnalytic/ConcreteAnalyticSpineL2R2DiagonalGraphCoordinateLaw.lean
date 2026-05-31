import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DirectClosedGraphWitness

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal

noncomputable section

/-- Coordinate law for a point of the concrete R2 diagonal graph.

If `p = (x, A x)` is in the diagonal graph, then each output coordinate is the
corresponding diagonal weight times the input coordinate. -/
theorem concrete_l2_r2_diagonal_graph_coordinate_law
    {p : ConcreteL2GraphPairSpace}
    (hp : p ∈ ConcreteL2DiagonalGraphL2Carrier) (n : ℕ) :
    p.2.1 n = concreteL2DiagonalWeight n * p.1.1 n := by
  rcases hp with ⟨x, rfl⟩
  rfl

/-- Every diagonal graph point satisfies the pointwise diagonal relation. -/
theorem concrete_l2_r2_diagonal_graph_pointwise_relation_of_mem
    {p : ConcreteL2GraphPairSpace}
    (hp : p ∈ ConcreteL2DiagonalGraphL2Carrier) :
    concreteL2R2DiagonalGraphPointwiseRelation p := by
  intro n
  exact concrete_l2_r2_diagonal_graph_coordinate_law hp n

/-- Coordinate-law readiness for the direct closed-graph program.

The pointwise relation and reconstruction theorems now live in the lower
`DirectClosedGraphWitness` layer, so this file only adds the forward coordinate
law from graph membership. -/
def concreteAnalyticSpineL2R2DiagonalGraphCoordinateLawReady : Prop :=
  (∀ {p : ConcreteL2GraphPairSpace},
    p ∈ ConcreteL2DiagonalGraphL2Carrier →
      concreteL2R2DiagonalGraphPointwiseRelation p) ∧
  concreteL2R2LimitActionSquareSummabilityReady ∧
  concreteL2R2ReconstructedDomainWitnessReady ∧
  concreteL2R2ReconstructedGraphMembershipReady ∧
  concreteAnalyticSpineL2R2DirectClosedGraphWitnessSurfaceReady

/-- The coordinate-law layer is ready. -/
theorem concrete_analytic_spine_l2_r2_diagonal_graph_coordinate_law_ready :
    concreteAnalyticSpineL2R2DiagonalGraphCoordinateLawReady := by
  exact ⟨
    fun hp => concrete_l2_r2_diagonal_graph_pointwise_relation_of_mem hp,
    concrete_l2_r2_limit_action_square_summability_ready,
    concrete_l2_r2_reconstructed_domain_witness_ready,
    concrete_l2_r2_reconstructed_graph_membership_ready,
    concrete_analytic_spine_l2_r2_direct_closed_graph_witness_surface_ready⟩

end

end MathlibAnalytic
end MGAP4D
