import MGAP4D.MathlibAnalytic.R4HilbertMathlibLinearPMapSelfAdjointGraphToPMap
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
# Formal-adjoint identity for self-adjoint `LinearPMap`s

This file continues the concrete unbounded-operator route.

For a densely defined `LinearPMap`, pinned mathlib proves that the adjoint is a
formal adjoint.  For a self-adjoint operator, this gives a formal-adjoint
identity for the operator itself.

This is still not a spectral-measure theorem and it does not assert a spectral
gap.  It records another actual mathlib consequence for the R4 operator type.
-/

namespace LinearPMapSelfAdjointFormalAdjoint

open scoped LinearPMap

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable {A : E →ₗ.[𝕜] E}

/-- Actual invocation of the pinned mathlib theorem that the adjoint is a formal
adjoint, using self-adjointness to supply domain density. -/
theorem selfAdjoint_linearPMap_adjoint_isFormalAdjoint_invoked
    (hA : IsSelfAdjoint A) :
    A†.IsFormalAdjoint A :=
  LinearPMap.adjoint_isFormalAdjoint hA.dense_domain

/-- For a self-adjoint `LinearPMap`, the operator is its own formal adjoint. -/
theorem selfAdjoint_linearPMap_isFormalAdjoint_self
    (hA : IsSelfAdjoint A) :
    A.IsFormalAdjoint A := by
  have hformal : A†.IsFormalAdjoint A :=
    selfAdjoint_linearPMap_adjoint_isFormalAdjoint_invoked hA
  rw [LinearPMap.isSelfAdjoint_def.mp hA] at hformal
  exact hformal

/-- Dense domain, closedness, graph identities, and formal-adjoint symmetry can
be carried together. -/
theorem selfAdjoint_linearPMap_operator_package
    (hA : IsSelfAdjoint A) :
    Dense (A.domain : Set E) ∧
      A.IsClosed ∧
      A.graph = A.graph.adjoint ∧
      A.graph.adjoint.toLinearPMap = A ∧
      A.IsFormalAdjoint A :=
  ⟨LinearPMapSelfAdjointConsequences.selfAdjoint_linearPMap_denseDomain hA,
    LinearPMapSelfAdjointClosed.selfAdjoint_linearPMap_isClosed hA,
    LinearPMapSelfAdjointGraph.selfAdjoint_linearPMap_graph_eq_graphAdjoint hA,
    LinearPMapSelfAdjointGraphToPMap.selfAdjoint_linearPMap_graphAdjoint_toLinearPMap_eq_self hA,
    selfAdjoint_linearPMap_isFormalAdjoint_self hA⟩

/-- Formal-adjoint symmetry is still an operator-theoretic identity, not a
spectral-gap assertion. -/
def selfAdjointLinearPMapFormalAdjointButNoGapAssertion : Prop := True

theorem selfAdjointLinearPMapFormalAdjointButNoGapAssertion_holds :
    selfAdjointLinearPMapFormalAdjointButNoGapAssertion :=
  trivial

end LinearPMapSelfAdjointFormalAdjoint

end

end MathlibAnalytic
end MGAP4D
