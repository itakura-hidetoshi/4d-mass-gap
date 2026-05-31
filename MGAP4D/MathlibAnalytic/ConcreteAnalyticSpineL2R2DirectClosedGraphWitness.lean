import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2DiagonalGraphNorm
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2DiagonalGraphLinearClosure
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2ClosureSubsetDiagonalCriterion

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal

noncomputable section

/-- Direct closed-graph witness predicate for the original R2 diagonal graph.

This is the analytic core needed to break the remaining circularity.  It says
that every pair in the graph-norm closure of the original diagonal graph is again
in the original diagonal graph.  Once this is proved from coordinate convergence
and weighted-square summability, the original diagonal graph can be promoted to a
closed graph theorem without using diagonal-graph-equals-closure. -/
def concreteL2R2DirectClosedGraphWitness : Prop :=
  @closure ConcreteL2GraphPairSpace concreteL2GraphNormTopology
      ConcreteL2DiagonalGraphL2Carrier ⊆
    ConcreteL2DiagonalGraphL2Carrier

/-- Pointwise diagonal relation for a graph-pair candidate. -/
def concreteL2R2DiagonalGraphPointwiseRelation
    (p : ConcreteL2GraphPairSpace) : Prop :=
  ∀ n : ℕ, p.2.1 n = concreteL2DiagonalWeight n * p.1.1 n

/-- The pointwise relation plus square-summability of the second coordinate
reconstructs the diagonal-domain witness for the first coordinate.

This is the algebraic summability step in the direct closed-graph proof: if
`y_n = w_n x_n` and `y ∈ ℓ²`, then the weighted action sequence is square
summable, hence `x` lies in the diagonal domain. -/
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

/-- The pointwise relation reconstructs membership in the original diagonal graph. -/
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

/-- Closedness promotion theorem for the direct witness.

This is the purely topological step: if `closure S ⊆ S`, then `S` is closed.
The proof avoids any extra API dependency by deriving `closure S = S` from
`subset_closure` and then transporting `isClosed_closure` across that equality. -/
theorem concrete_l2_r2_original_diagonal_graph_closed_of_direct_witness
    (hDirect : concreteL2R2DirectClosedGraphWitness) :
    concreteL2R2OriginalDiagonalGraphClosedTheorem := by
  unfold concreteL2R2DirectClosedGraphWitness at hDirect
  unfold concreteL2R2OriginalDiagonalGraphClosedTheorem
  have hEq :
      @closure ConcreteL2GraphPairSpace concreteL2GraphNormTopology
          ConcreteL2DiagonalGraphL2Carrier =
        ConcreteL2DiagonalGraphL2Carrier := by
    exact Set.Subset.antisymm hDirect
      (@subset_closure ConcreteL2GraphPairSpace concreteL2GraphNormTopology
        ConcreteL2DiagonalGraphL2Carrier)
  simpa [hEq] using
    (@isClosed_closure ConcreteL2GraphPairSpace concreteL2GraphNormTopology
      ConcreteL2DiagonalGraphL2Carrier)

/-- Closedness promotion obligation for the direct witness.

This is now proved, not just recorded as a boundary: once the analytic direct
witness is supplied, the original diagonal graph is closed. -/
def concreteL2R2DirectClosedGraphWitnessToClosednessObligation : Prop :=
  concreteL2R2DirectClosedGraphWitness →
    concreteL2R2OriginalDiagonalGraphClosedTheorem

/-- The direct-witness-to-closedness promotion theorem is ready. -/
theorem concrete_l2_r2_direct_closed_graph_witness_to_closedness_obligation_ready :
    concreteL2R2DirectClosedGraphWitnessToClosednessObligation := by
  intro hDirect
  exact concrete_l2_r2_original_diagonal_graph_closed_of_direct_witness hDirect

/-- Remaining obligation: closure membership must imply the pointwise diagonal
coordinate relation.  This is the true limit-passage target for the next layer. -/
def concreteL2R2ClosureMembershipToCoordinateLimitObligation : Prop :=
  @closure ConcreteL2GraphPairSpace concreteL2GraphNormTopology
      ConcreteL2DiagonalGraphL2Carrier ⊆
    {p : ConcreteL2GraphPairSpace | concreteL2R2DiagonalGraphPointwiseRelation p}

/-- Remaining obligation: the diagonal weight relation must be stable under the
chosen graph-norm limit passage. -/
def concreteL2R2DiagonalWeightRelationClosedUnderLimitObligation : Prop :=
  concreteL2R2ClosureMembershipToCoordinateLimitObligation

/-- Proved summability reconstruction step once the pointwise relation is known. -/
def concreteL2R2LimitActionSquareSummabilityReady : Prop :=
  ∀ {p : ConcreteL2GraphPairSpace},
    concreteL2R2DiagonalGraphPointwiseRelation p →
      ConcreteL2DiagonalDomain p.1

/-- The summability reconstruction step is ready. -/
theorem concrete_l2_r2_limit_action_square_summability_ready :
    concreteL2R2LimitActionSquareSummabilityReady := by
  intro p hrel
  exact concrete_l2_r2_reconstruct_domain_from_pointwise_relation hrel

/-- Proved domain reconstruction step once the pointwise relation is known. -/
def concreteL2R2ReconstructedDomainWitnessReady : Prop :=
  ∀ {p : ConcreteL2GraphPairSpace},
    concreteL2R2DiagonalGraphPointwiseRelation p →
      ConcreteL2DiagonalDomain p.1

/-- The domain reconstruction step is ready. -/
theorem concrete_l2_r2_reconstructed_domain_witness_ready :
    concreteL2R2ReconstructedDomainWitnessReady := by
  intro p hrel
  exact concrete_l2_r2_reconstruct_domain_from_pointwise_relation hrel

/-- Proved graph-membership reconstruction step once the pointwise relation is known. -/
def concreteL2R2ReconstructedGraphMembershipReady : Prop :=
  ∀ {p : ConcreteL2GraphPairSpace},
    concreteL2R2DiagonalGraphPointwiseRelation p →
      p ∈ ConcreteL2DiagonalGraphL2Carrier

/-- The graph-membership reconstruction step is ready. -/
theorem concrete_l2_r2_reconstructed_graph_membership_ready :
    concreteL2R2ReconstructedGraphMembershipReady := by
  intro p hrel
  exact concrete_l2_r2_diagonal_graph_mem_of_pointwise_relation hrel

/-- The remaining analytic decomposition required for the direct closed graph
witness.

The first two fields are still genuine limit-passage obligations.  The last
three fields are now proved reconstruction steps from the pointwise diagonal
relation. -/
structure ConcreteL2R2DirectClosedGraphAnalyticWitness where
  closureMembershipToCoordinateLimit : Prop
  diagonalWeightRelationClosedUnderLimit : Prop
  limitActionSquareSummability : Prop
  reconstructedDomainWitness : Prop
  reconstructedGraphMembership : Prop

/-- Current direct closed-graph analytic witness surface. -/
def concreteL2R2DirectClosedGraphAnalyticWitnessSurface :
    ConcreteL2R2DirectClosedGraphAnalyticWitness :=
  { closureMembershipToCoordinateLimit :=
      concreteL2R2ClosureMembershipToCoordinateLimitObligation
    diagonalWeightRelationClosedUnderLimit :=
      concreteL2R2DiagonalWeightRelationClosedUnderLimitObligation
    limitActionSquareSummability :=
      concreteL2R2LimitActionSquareSummabilityReady
    reconstructedDomainWitness :=
      concreteL2R2ReconstructedDomainWitnessReady
    reconstructedGraphMembership :=
      concreteL2R2ReconstructedGraphMembershipReady }

/-- Readiness predicate for the direct closed-graph witness layer.

This is not yet the direct witness itself.  It registers the two remaining limit
obligations by name and proves the three reconstruction steps needed after the
pointwise relation is obtained. -/
def concreteAnalyticSpineL2R2DirectClosedGraphWitnessSurfaceReady : Prop :=
  concreteAnalyticSpineL2DiagonalGraphNormSurfaceReady ∧
  concreteAnalyticSpineL2R2DiagonalGraphLinearClosureSurfaceReady ∧
  concreteAnalyticSpineL2R2ClosureSubsetDiagonalCriterionReady ∧
  concreteL2R2DirectClosedGraphWitnessToClosednessObligation ∧
  concreteL2R2LimitActionSquareSummabilityReady ∧
  concreteL2R2ReconstructedDomainWitnessReady ∧
  concreteL2R2ReconstructedGraphMembershipReady

/-- The direct closed-graph witness surface is ready as a decomposed proof plan. -/
theorem concrete_analytic_spine_l2_r2_direct_closed_graph_witness_surface_ready :
    concreteAnalyticSpineL2R2DirectClosedGraphWitnessSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_diagonal_graph_norm_surface_ready,
    concrete_analytic_spine_l2_r2_diagonal_graph_linear_closure_surface_ready,
    concrete_analytic_spine_l2_r2_closure_subset_diagonal_criterion_ready,
    concrete_l2_r2_direct_closed_graph_witness_to_closedness_obligation_ready,
    concrete_l2_r2_limit_action_square_summability_ready,
    concrete_l2_r2_reconstructed_domain_witness_ready,
    concrete_l2_r2_reconstructed_graph_membership_ready⟩

end

end MathlibAnalytic
end MGAP4D
