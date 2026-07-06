import MGAP4D.MathlibAnalytic.R4HilbertMathlibLinearPMapSelfAdjointFormalAdjoint
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
# Larger `LinearPMap` adjoint toolkit

This file batches several concrete pinned-mathlib adjoint APIs instead of
adding one theorem at a time.

It records three groups of available facts for the current unbounded-operator
route:

* formal-adjoint symmetry and maximality;
* adjoint evaluation and uniqueness on dense domains;
* the bridge from bounded `ContinuousLinearMap` adjoints to `LinearPMap`
  adjoints on dense submodules.

These are still not spectral-measure theorems and they do not assert a spectral
gap.  They are the currently available mathlib operator APIs that sit between
self-adjoint `LinearPMap`s and any future spectral-theorem interface.
-/

namespace LinearPMapAdjointToolkit

open scoped LinearPMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

section FormalAdjoint

variable [CompleteSpace E]
variable {A : E →ₗ.[𝕜] E}

/-- Formal-adjoint symmetry, invoked through the pinned mathlib theorem
`LinearPMap.IsFormalAdjoint.symm`. -/
theorem selfAdjoint_linearPMap_formalAdjoint_symm_invoked
    (hA : IsSelfAdjoint A) :
    A.IsFormalAdjoint A :=
  (LinearPMapSelfAdjointFormalAdjoint.selfAdjoint_linearPMap_isFormalAdjoint_self hA).symm

/-- Formal-adjoint maximality, invoked through the pinned mathlib theorem
`LinearPMap.IsFormalAdjoint.le_adjoint`. -/
theorem selfAdjoint_linearPMap_self_le_adjoint_invoked
    (hA : IsSelfAdjoint A) :
    A ≤ A† :=
  (LinearPMapSelfAdjointFormalAdjoint.selfAdjoint_linearPMap_isFormalAdjoint_self hA).le_adjoint
    hA.dense_domain

/-- The reverse inclusion follows from self-adjointness itself. -/
theorem selfAdjoint_linearPMap_adjoint_le_self
    (hA : IsSelfAdjoint A) :
    A† ≤ A := by
  rw [LinearPMap.isSelfAdjoint_def.mp hA]

/-- Self-adjointness can be repackaged as mutual inclusion together with
formal-adjoint symmetry. -/
theorem selfAdjoint_linearPMap_formalAdjoint_inclusion_package
    (hA : IsSelfAdjoint A) :
    A.IsFormalAdjoint A ∧ A ≤ A† ∧ A† ≤ A :=
  ⟨selfAdjoint_linearPMap_formalAdjoint_symm_invoked hA,
    selfAdjoint_linearPMap_self_le_adjoint_invoked hA,
    selfAdjoint_linearPMap_adjoint_le_self hA⟩

end FormalAdjoint

section AdjointEvaluation

variable [CompleteSpace E]
variable {T : E →ₗ.[𝕜] F}
variable (hT : Dense (T.domain : Set E))

/-- Actual invocation of the dense-domain formula for applying the adjoint. -/
theorem linearPMap_adjoint_apply_of_dense_invoked
    (y : T†.domain) :
    T† y = LinearPMap.adjointAux hT y :=
  LinearPMap.adjoint_apply_of_dense hT y

/-- Actual invocation of the inner-product formula for `adjointAux`. -/
theorem linearPMap_adjointAux_inner_invoked
    (y : T†.domain) (x : T.domain) :
    inner 𝕜 (LinearPMap.adjointAux hT y) x = inner 𝕜 (y : F) (T x) :=
  LinearPMap.adjointAux_inner hT y x

/-- Actual invocation of uniqueness for `adjointAux`. -/
theorem linearPMap_adjointAux_unique_invoked
    (y : T†.domain) {x₀ : E}
    (hx₀ : ∀ x : T.domain, inner 𝕜 x₀ x = inner 𝕜 (y : F) (T x)) :
    LinearPMap.adjointAux hT y = x₀ :=
  LinearPMap.adjointAux_unique hT y hx₀

/-- Actual invocation of the equality criterion for applying the adjoint. -/
theorem linearPMap_adjoint_apply_eq_invoked
    (hT' : Dense (T.domain : Set E))
    (y : T†.domain) {x₀ : E}
    (hx₀ : ∀ x : T.domain, inner 𝕜 x₀ x = inner 𝕜 (y : F) (T x)) :
    T† y = x₀ :=
  LinearPMap.adjoint_apply_eq hT' y hx₀

end AdjointEvaluation

section ContinuousLinearMapBridge

variable [CompleteSpace E] [CompleteSpace F]
variable (A : E →L[𝕜] F) {p : Submodule 𝕜 E}

/-- Actual invocation of the bridge from bounded adjoints to `LinearPMap`
adjoints on a dense submodule. -/
theorem continuousLinearMap_toPMap_adjoint_bridge_invoked
    (hp : Dense (p : Set E)) :
    (A.toPMap p).adjoint = A.adjoint.toPMap ⊤ :=
  A.toPMap_adjoint_eq_adjoint_toPMap_of_dense hp

end ContinuousLinearMapBridge

/-- The batched toolkit still records operator-level adjoint infrastructure, not
a spectral-gap assertion. -/
def linearPMapAdjointToolkitButNoGapAssertion : Prop := True

theorem linearPMapAdjointToolkitButNoGapAssertion_holds :
    linearPMapAdjointToolkitButNoGapAssertion :=
  trivial

end LinearPMapAdjointToolkit

end

end MathlibAnalytic
end MGAP4D
