import MGAP4D.MathlibAnalytic.R4HilbertMathlibLinearPMapSelfAdjointClosed
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
# Graph identity for self-adjoint `LinearPMap`s

This file continues the concrete unbounded-operator route.

For a densely defined `LinearPMap`, pinned mathlib identifies the graph of the
adjoint operator with the adjoint submodule of the graph.  For a self-adjoint
operator, this gives a graph-level self-adjointness identity.

This is still not a spectral-measure theorem and it does not assert a spectral
gap.  It records another actual mathlib consequence for the R4 operator type.
-/

namespace LinearPMapSelfAdjointGraph

open scoped LinearPMap

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable {A : E →ₗ.[𝕜] E}

/-- Actual invocation of the pinned mathlib graph theorem for the adjoint of a
`LinearPMap`, using self-adjointness to supply domain density. -/
theorem selfAdjoint_linearPMap_adjointGraph_eq_graphAdjoint_invoked
    (hA : IsSelfAdjoint A) :
    A†.graph = A.graph.adjoint :=
  LinearPMap.adjoint_graph_eq_graph_adjoint hA.dense_domain

/-- For a self-adjoint `LinearPMap`, the graph equals its graph-adjoint
submodule. -/
theorem selfAdjoint_linearPMap_graph_eq_graphAdjoint
    (hA : IsSelfAdjoint A) :
    A.graph = A.graph.adjoint := by
  have hgraph : A†.graph = A.graph.adjoint :=
    selfAdjoint_linearPMap_adjointGraph_eq_graphAdjoint_invoked hA
  rw [LinearPMap.isSelfAdjoint_def.mp hA] at hgraph
  exact hgraph

/-- Dense domain, closedness, and graph self-adjointness can be carried together. -/
theorem selfAdjoint_linearPMap_dense_closed_graph
    (hA : IsSelfAdjoint A) :
    Dense (A.domain : Set E) ∧ A.IsClosed ∧ A.graph = A.graph.adjoint :=
  ⟨LinearPMapSelfAdjointConsequences.selfAdjoint_linearPMap_denseDomain hA,
    LinearPMapSelfAdjointClosed.selfAdjoint_linearPMap_isClosed hA,
    selfAdjoint_linearPMap_graph_eq_graphAdjoint hA⟩

/-- Graph self-adjointness is still an operator-theoretic identity, not a spectral-gap assertion. -/
def selfAdjointLinearPMapGraphButNoGapAssertion : Prop := True

theorem selfAdjointLinearPMapGraphButNoGapAssertion_holds :
    selfAdjointLinearPMapGraphButNoGapAssertion :=
  trivial

end LinearPMapSelfAdjointGraph

end

end MathlibAnalytic
end MGAP4D
