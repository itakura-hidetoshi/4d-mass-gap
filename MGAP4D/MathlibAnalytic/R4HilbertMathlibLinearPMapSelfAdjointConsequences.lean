import MGAP4D.MathlibAnalytic.R4HilbertMathlibSpectralTheoremActualBoundary
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
# Actual mathlib consequences of self-adjoint `LinearPMap`s

This file does not add another spectral-theorem readiness layer.

After the finite-dimensional spectral-theorem boundary, the next concrete step
is to use the mathlib API that actually applies to the R4 operator type:
self-adjoint partially defined linear maps.

The pinned mathlib API proves that every self-adjoint `LinearPMap` has dense
domain.  This is a genuine consequence of the R4-side operator type and is one
of the prerequisites any future unbounded spectral theorem interface would need.
-/

namespace LinearPMapSelfAdjointConsequences

open scoped LinearPMap

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable {A : E →ₗ.[𝕜] E}

/-- Actual invocation of the pinned mathlib theorem that a self-adjoint
`LinearPMap` has dense domain. -/
theorem selfAdjoint_linearPMap_denseDomain_invoked
    (hA : IsSelfAdjoint A) :
    Dense (A.domain : Set E) :=
  hA.dense_domain

/-- Project-local alias for the same mathlib dense-domain consequence. -/
theorem selfAdjoint_linearPMap_denseDomain
    (hA : IsSelfAdjoint A) :
    Dense (A.domain : Set E) :=
  selfAdjoint_linearPMap_denseDomain_invoked hA

/-- The available R4-compatible mathlib consequence is domain density, not a
spectral-measure theorem. -/
def selfAdjointLinearPMapSpectralTheoremStillNeedsAdditionalInput : Prop := True

theorem selfAdjointLinearPMapSpectralTheoremStillNeedsAdditionalInput_holds :
    selfAdjointLinearPMapSpectralTheoremStillNeedsAdditionalInput :=
  trivial

end LinearPMapSelfAdjointConsequences

end

end MathlibAnalytic
end MGAP4D
