import MGAP4D.MathlibAnalytic.R4HilbertMathlibLinearPMapSelfAdjointConsequences
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
# Closedness of self-adjoint `LinearPMap`s

This file continues the concrete `LinearPMap` route.

After invoking the dense-domain theorem for self-adjoint partially defined
linear maps, we now invoke the pinned mathlib theorem that every self-adjoint
`LinearPMap` is closed.

This is still not a spectral-measure theorem and it does not assert a spectral
gap.  It records another actual mathlib consequence available for the R4
operator type.
-/

namespace LinearPMapSelfAdjointClosed

open scoped LinearPMap

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable {A : E →ₗ.[𝕜] E}

/-- Actual invocation of the pinned mathlib theorem that a self-adjoint
`LinearPMap` is closed. -/
theorem selfAdjoint_linearPMap_isClosed_invoked
    (hA : IsSelfAdjoint A) :
    A.IsClosed :=
  hA.isClosed

/-- Project-local alias for the same mathlib closedness consequence. -/
theorem selfAdjoint_linearPMap_isClosed
    (hA : IsSelfAdjoint A) :
    A.IsClosed :=
  selfAdjoint_linearPMap_isClosed_invoked hA

/-- Dense domain is still available together with closedness. -/
theorem selfAdjoint_linearPMap_denseDomain_and_closed
    (hA : IsSelfAdjoint A) :
    Dense (A.domain : Set E) ∧ A.IsClosed :=
  ⟨LinearPMapSelfAdjointConsequences.selfAdjoint_linearPMap_denseDomain hA,
    selfAdjoint_linearPMap_isClosed hA⟩

/-- Closedness is an operator-theoretic prerequisite, not a spectral-gap statement. -/
def selfAdjointLinearPMapClosedButNoGapAssertion : Prop := True

theorem selfAdjointLinearPMapClosedButNoGapAssertion_holds :
    selfAdjointLinearPMapClosedButNoGapAssertion :=
  trivial

end LinearPMapSelfAdjointClosed

end

end MathlibAnalytic
end MGAP4D
