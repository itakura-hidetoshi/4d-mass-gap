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

/-- The remaining analytic decomposition required for the direct closed graph
witness.

The intended proof path is: graph-norm closure gives first-coordinate and
second-coordinate convergence; coordinatewise continuity of the diagonal weight
relation gives `y_n = w_n x_n`; square summability of `y` gives `x ∈ Dom(A)` and
therefore `(x,y) ∈ graph(A)`. -/
structure ConcreteL2R2DirectClosedGraphAnalyticWitness where
  closureMembershipToCoordinateLimit : Prop
  diagonalWeightRelationClosedUnderLimit : Prop
  limitActionSquareSummability : Prop
  reconstructedDomainWitness : Prop
  reconstructedGraphMembership : Prop

/-- Current direct closed-graph analytic witness surface.

The fields remain separated so the next patches can replace each marker with a
genuine lemma without changing the public theorem shape. -/
def concreteL2R2DirectClosedGraphAnalyticWitnessSurface :
    ConcreteL2R2DirectClosedGraphAnalyticWitness :=
  { closureMembershipToCoordinateLimit := True
    diagonalWeightRelationClosedUnderLimit := True
    limitActionSquareSummability := True
    reconstructedDomainWitness := True
    reconstructedGraphMembership := True }

/-- Readiness predicate for the direct closed-graph witness layer.

This is not yet the direct witness itself.  It registers the analytic subgoals
needed to prove it and includes the now-proved closedness-promotion theorem. -/
def concreteAnalyticSpineL2R2DirectClosedGraphWitnessSurfaceReady : Prop :=
  concreteAnalyticSpineL2DiagonalGraphNormSurfaceReady ∧
  concreteAnalyticSpineL2R2DiagonalGraphLinearClosureSurfaceReady ∧
  concreteAnalyticSpineL2R2ClosureSubsetDiagonalCriterionReady ∧
  concreteL2R2DirectClosedGraphWitnessToClosednessObligation ∧
  True ∧ True ∧ True ∧ True ∧ True

/-- The direct closed-graph witness surface is ready as a decomposed proof plan. -/
theorem concrete_analytic_spine_l2_r2_direct_closed_graph_witness_surface_ready :
    concreteAnalyticSpineL2R2DirectClosedGraphWitnessSurfaceReady := by
  exact ⟨
    concrete_analytic_spine_l2_diagonal_graph_norm_surface_ready,
    concrete_analytic_spine_l2_r2_diagonal_graph_linear_closure_surface_ready,
    concrete_analytic_spine_l2_r2_closure_subset_diagonal_criterion_ready,
    concrete_l2_r2_direct_closed_graph_witness_to_closedness_obligation_ready,
    trivial,
    trivial,
    trivial,
    trivial,
    trivial⟩

end

end MathlibAnalytic
end MGAP4D
