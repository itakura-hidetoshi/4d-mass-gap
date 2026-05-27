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

/-- Pointwise diagonal relation induced by a graph point. -/
def concreteL2R2DiagonalGraphPointwiseRelation
    (p : ConcreteL2GraphPairSpace) : Prop :=
  ∀ n : ℕ, p.2.1 n = concreteL2DiagonalWeight n * p.1.1 n

/-- Every diagonal graph point satisfies the pointwise diagonal relation. -/
theorem concrete_l2_r2_diagonal_graph_pointwise_relation_of_mem
    {p : ConcreteL2GraphPairSpace}
    (hp : p ∈ ConcreteL2DiagonalGraphL2Carrier) :
    concreteL2R2DiagonalGraphPointwiseRelation p := by
  intro n
  exact concrete_l2_r2_diagonal_graph_coordinate_law hp n

/-- The pointwise relation plus square-summability of the second coordinate
reconstructs the diagonal-domain witness for the first coordinate.

This is the key algebraic step in the direct closed-graph proof: if `y_n = w_n x_n`
and `y ∈ l2`, then `x` lies in the weighted diagonal domain. -/
theorem concrete_l2_r2_reconstruct_domain_from_pointwise_relation
    {p : ConcreteL2GraphPairSpace}
    (hrel : concreteL2R2DiagonalGraphPointwiseRelation p) :
    ConcreteL2DiagonalDomain p.1 := by
  unfold ConcreteL2DiagonalDomain
  have hseq :
      (fun n : ℕ => (concreteL2DiagonalWeight n)^2 * (p.1.1 n)^2) =
        (fun n : ℕ => (p.2.1 n)^2) := by
    funext n
    rw [hrel n]
    ring
  rw [hseq]
  exact p.2.2

/-- The pointwise relation reconstructs graph membership. -/
theorem concrete_l2_r2_diagonal_graph_mem_of_pointwise_relation
    {p : ConcreteL2GraphPairSpace}
    (hrel : concreteL2R2DiagonalGraphPointwiseRelation p) :
    p ∈ ConcreteL2DiagonalGraphL2Carrier := by
  let x : ConcreteL2DiagonalDomainCarrier :=
    ⟨p.1, concrete_l2_r2_reconstruct_domain_from_pointwise_relation hrel⟩
  refine ⟨x, ?_⟩
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    funext n
    exact (hrel n).symm

/-- Coordinate-law readiness for the direct closed-graph program. -/
def concreteAnalyticSpineL2R2DiagonalGraphCoordinateLawReady : Prop :=
  (∀ {p : ConcreteL2GraphPairSpace},
    p ∈ ConcreteL2DiagonalGraphL2Carrier →
      concreteL2R2DiagonalGraphPointwiseRelation p) ∧
  (∀ {p : ConcreteL2GraphPairSpace},
    concreteL2R2DiagonalGraphPointwiseRelation p →
      ConcreteL2DiagonalDomain p.1) ∧
  (∀ {p : ConcreteL2GraphPairSpace},
    concreteL2R2DiagonalGraphPointwiseRelation p →
      p ∈ ConcreteL2DiagonalGraphL2Carrier) ∧
  concreteAnalyticSpineL2R2DirectClosedGraphWitnessSurfaceReady

/-- The coordinate-law layer is ready. -/
theorem concrete_analytic_spine_l2_r2_diagonal_graph_coordinate_law_ready :
    concreteAnalyticSpineL2R2DiagonalGraphCoordinateLawReady := by
  exact ⟨
    fun hp => concrete_l2_r2_diagonal_graph_pointwise_relation_of_mem hp,
    fun hrel => concrete_l2_r2_reconstruct_domain_from_pointwise_relation hrel,
    fun hrel => concrete_l2_r2_diagonal_graph_mem_of_pointwise_relation hrel,
    concrete_analytic_spine_l2_r2_direct_closed_graph_witness_surface_ready⟩

end

end MathlibAnalytic
end MGAP4D
