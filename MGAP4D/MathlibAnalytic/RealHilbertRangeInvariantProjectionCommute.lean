import MGAP4D.MathlibAnalytic.RealHilbertCommutingProjectionSweepTensorization
import Mathlib.Analysis.InnerProductSpace.Semisimple
import Mathlib.LinearAlgebra.Projection
import Mathlib.Tactic

/-!
# Commutation from range invariance for real Hilbert projections

For a symmetric continuous linear endomorphism `P` and a symmetric idempotent
continuous linear endomorphism `Q`, it is enough to show that the range of
`Q` is invariant under `P`.

Symmetry of `P` then makes the orthogonal complement of `range Q` invariant.
Symmetry of `Q` identifies that orthogonal complement with `ker Q`.
At the pinned Mathlib revision the relevant invariant-subspace commutation
criterion is stated for linear endomorphisms as
`LinearMap.IsIdempotentElem.commute_iff`, so the final algebraic step is
performed explicitly on `P.toLinearMap` and `Q.toLinearMap`.

This is the Hilbert-geometric receiver used by the beta-zero product-Haar
conditional-expectation argument: the measure-theoretic part only has to prove
range invariance.
-/

namespace MGAP4D.MathlibAnalytic

open scoped InnerProductSpace InnerProduct

noncomputable section

/-- A symmetric operator `P` commutes with a symmetric idempotent `Q` once
`range Q` is invariant under `P`.

Idempotence of `P` is not needed for this Hilbert-geometric implication. -/
theorem realHilbertProjection_commute_of_range_invariant
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (P Q : E →L[ℝ] E)
    (hPSymm : ∀ x y : E, inner ℝ (P x) y = inner ℝ x (P y))
    (hQIdem : Q.comp Q = Q)
    (hQSymm : ∀ x y : E, inner ℝ (Q x) y = inner ℝ x (Q y))
    (hRange :
      ∀ x : E,
        x ∈ Q.toLinearMap.range →
          P x ∈ Q.toLinearMap.range)
    (x : E) :
    P (Q x) = Q (P x) := by
  have hQIdemElem : IsIdempotentElem Q.toLinearMap := by
    change Q.toLinearMap * Q.toLinearMap = Q.toLinearMap
    apply LinearMap.ext
    intro y
    rw [Module.End.mul_apply]
    have hy := congrArg (fun T : E →L[ℝ] E => T y) hQIdem
    simpa only [ContinuousLinearMap.comp_apply] using hy

  have hPSymmLinear : P.toLinearMap.IsSymmetric :=
    hPSymm
  have hQSymmLinear : Q.toLinearMap.IsSymmetric :=
    hQSymm

  have hRangeInv :
      Q.toLinearMap.range ∈ Module.End.invtSubmodule P.toLinearMap := by
    intro y hy
    exact hRange y hy

  have hOrthInv :
      Q.toLinearMap.rangeᗮ ∈ Module.End.invtSubmodule P.toLinearMap :=
    hPSymmLinear.orthogonalComplement_mem_invtSubmodule hRangeInv

  have hQOrth :
      Q.toLinearMap.rangeᗮ = Q.toLinearMap.ker :=
    hQSymmLinear.orthogonal_range

  have hKerInv :
      Q.toLinearMap.ker ∈ Module.End.invtSubmodule P.toLinearMap := by
    rw [← hQOrth]
    exact hOrthInv

  have hComm : Commute Q.toLinearMap P.toLinearMap :=
    (LinearMap.IsIdempotentElem.commute_iff hQIdemElem).2
      ⟨hRangeInv, hKerInv⟩

  have hx :=
    congrArg (fun T : E →ₗ[ℝ] E => T x) hComm.eq
  simpa only [Module.End.mul_apply] using hx.symm

/-- Family form: pairwise range invariance plus symmetric projection geometry
gives the pointwise commutation hypothesis expected by finite projection
tensorization. -/
theorem realHilbertProjectionFamily_commute_of_range_invariant
    {E C : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (P : C → E →L[ℝ] E)
    (hIdem : ∀ c : C, (P c).comp (P c) = P c)
    (hSymm : ∀ (c : C) (x y : E),
      inner ℝ (P c x) y = inner ℝ x (P c y))
    (hRange :
      ∀ (c d : C) (x : E),
        x ∈ (P d).toLinearMap.range →
          P c x ∈ (P d).toLinearMap.range)
    (c d : C)
    (x : E) :
    P c (P d x) = P d (P c x) := by
  exact
    realHilbertProjection_commute_of_range_invariant
      (P c) (P d)
      (hSymm c)
      (hIdem d) (hSymm d)
      (hRange c d) x

end

end MGAP4D.MathlibAnalytic
