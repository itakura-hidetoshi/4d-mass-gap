import Mathlib.Analysis.InnerProductSpace.Spectrum
import MGAP4D.MathlibAnalytic.R4HilbertMathlibSpectralTheoremInvocationHandoff
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-!
# Actual mathlib spectral-theorem boundary

This file deliberately stops adding new R4 "readiness" or "handoff" layers.

The pinned mathlib version provides an actual diagonalization/spectral-theorem
statement for finite-dimensional self-adjoint `LinearMap`s, exposed through
`LinearMap.IsSymmetric.diagonalization_apply_self_apply`.

The current R4 Hamiltonian object carried by the preceding files is instead a
self-adjoint `LinearPMap`.  The pinned mathlib `LinearPMap` API contains adjoint,
self-adjointness, dense-domain, and closedness infrastructure, but not a direct
spectral-measure theorem for unbounded self-adjoint `LinearPMap`s.

Accordingly, this file does two precise things:

* it actually invokes the existing mathlib finite-dimensional spectral theorem;
* it records the present boundary: applying that theorem to the R4 object still
  requires an additional bridge from the R4 `LinearPMap` object to a mathlib
  theorem input that exists in the pinned dependency set.
-/

namespace MathlibSpectralTheoremActualBoundary

open Module End WithLp

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {T : E →ₗ[𝕜] E}

/-- Actual invocation of the pinned mathlib finite-dimensional spectral theorem.

This is not another readiness layer: the proof term is exactly the existing
mathlib theorem `LinearMap.IsSymmetric.diagonalization_apply_self_apply`, used
through dot notation. -/
theorem finiteDimensional_spectralTheorem_invoked
    (hT : T.IsSymmetric) (v : E) (μ : Eigenvalues T) :
    hT.diagonalization (T v) μ = (μ : 𝕜) • hT.diagonalization v μ :=
  hT.diagonalization_apply_self_apply v μ

/-- Alias exposing the same actual mathlib theorem under a project-local name. -/
theorem finiteDimensional_spectralTheorem_diagonal_action
    (hT : T.IsSymmetric) :
    ∀ (v : E) (μ : Eigenvalues T),
      hT.diagonalization (T v) μ = (μ : 𝕜) • hT.diagonalization v μ :=
  fun v μ => finiteDimensional_spectralTheorem_invoked hT v μ

/-- The current pinned-mathlib boundary for the R4 route.

The actual theorem invoked above is finite-dimensional and formulated for
`LinearMap.IsSymmetric`.  The R4 object accumulated by the preceding formal
files is a self-adjoint `LinearPMap`.  Bridging those two types, or supplying a
pinned-mathlib theorem for unbounded self-adjoint `LinearPMap`s, is the next
mathematical interface problem. -/
def r4LinearPMapToActualSpectralTheoremBridgeNeeded : Prop := True

theorem r4LinearPMapToActualSpectralTheoremBridgeNeeded_holds :
    r4LinearPMapToActualSpectralTheoremBridgeNeeded :=
  trivial

end MathlibSpectralTheoremActualBoundary

end

end MathlibAnalytic
end MGAP4D
