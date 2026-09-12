import MGAP4D.MathlibAnalytic.R4HilbertMathlibLinearPMapSelfAdjointGraph
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
# Recovering a self-adjoint `LinearPMap` from the adjoint graph

This file continues the concrete unbounded-operator route.

For a densely defined `LinearPMap`, pinned mathlib converts the adjoint of the
graph back to the adjoint operator.  For a self-adjoint operator, this recovers
the original operator from the adjoint graph.

This is still not a spectral-measure theorem and it does not assert a spectral
gap.  It records another actual mathlib consequence for the R4 operator type.
-/

namespace LinearPMapSelfAdjointGraphToPMap

open scoped LinearPMap

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable {A : E →ₗ.[𝕜] E}

/-- Actual invocation of the pinned mathlib theorem converting the adjoint graph
back into the adjoint `LinearPMap`, using self-adjointness to supply domain
density. -/
theorem selfAdjoint_linearPMap_graphAdjoint_toLinearPMap_eq_adjoint_invoked
    (hA : IsSelfAdjoint A) :
    A.graph.adjoint.toLinearPMap = A† :=
  LinearPMap.graph_adjoint_toLinearPMap_eq_adjoint hA.dense_domain

/-- For a self-adjoint `LinearPMap`, the adjoint graph recovers the original
operator. -/
theorem selfAdjoint_linearPMap_graphAdjoint_toLinearPMap_eq_self
    (hA : IsSelfAdjoint A) :
    A.graph.adjoint.toLinearPMap = A :=
  calc
    A.graph.adjoint.toLinearPMap = A† :=
      selfAdjoint_linearPMap_graphAdjoint_toLinearPMap_eq_adjoint_invoked hA
    _ = A := LinearPMap.isSelfAdjoint_def.mp hA

/-- Dense domain, closedness, graph self-adjointness, and graph-to-operator
recovery can be carried together. -/
theorem selfAdjoint_linearPMap_dense_closed_graph_toPMap
    (hA : IsSelfAdjoint A) :
    Dense (A.domain : Set E) ∧
      A.IsClosed ∧
      A.graph = A.graph.adjoint ∧
      A.graph.adjoint.toLinearPMap = A :=
  ⟨LinearPMapSelfAdjointConsequences.selfAdjoint_linearPMap_denseDomain hA,
    LinearPMapSelfAdjointClosed.selfAdjoint_linearPMap_isClosed hA,
    LinearPMapSelfAdjointGraph.selfAdjoint_linearPMap_graph_eq_graphAdjoint hA,
    selfAdjoint_linearPMap_graphAdjoint_toLinearPMap_eq_self hA⟩

/-- Graph-to-operator recovery is still an operator-theoretic identity, not a
spectral-gap assertion. -/
def selfAdjointLinearPMapGraphToPMapButNoGapAssertion : Prop := True

theorem selfAdjointLinearPMapGraphToPMapButNoGapAssertion_holds :
    selfAdjointLinearPMapGraphToPMapButNoGapAssertion :=
  trivial

end LinearPMapSelfAdjointGraphToPMap

end

end MathlibAnalytic
end MGAP4D
