import MGAP4D.MathlibAnalytic.RealHilbertCommutingProjectionSweepTensorization
import Mathlib.Analysis.InnerProductSpace.Semisimple
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
import Mathlib.Tactic

/-!
# Commutation from range invariance for real Hilbert projections

For symmetric idempotent continuous linear endomorphisms `P,Q`, it is enough
to show that the range of `Q` is invariant under `P`.  Symmetry of `P`
then makes the orthogonal complement of `range Q` invariant; symmetry of
`Q` identifies that orthogonal complement with `ker Q`; Mathlib's
idempotent commutation criterion then gives `PQ = QP`.

This is the Hilbert-geometric receiver used by the beta-zero product-Haar
conditional-expectation argument: the measure-theoretic part only has to prove
range invariance.
-/

namespace MGAP4D.MathlibAnalytic

open scoped InnerProductSpace InnerProduct

noncomputable section

/-- Two symmetric idempotents commute once the range of the second is invariant
under the first. -/
theorem realHilbertProjection_commute_of_range_invariant
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (P Q : E →L[ℝ] E)
    (hPIdem : P.comp P = P)
    (hPSymm : ∀ x y : E, inner ℝ (P x) y = inner ℝ x (P y))
    (hQIdem : Q.comp Q = Q)
    (hQSymm : ∀ x y : E, inner ℝ (Q x) y = inner ℝ x (Q y))
    (hRange : ∀ x : E, x ∈ Q.range → P x ∈ Q.range)
    (x : E) :
    P (Q x) = Q (P x) := by
  have hQIdemElem : IsIdempotentElem Q := by
    show Q * Q = Q
    rw [ContinuousLinearMap.mul_def]
    exact hQIdem
  have hRangeInv : Q.range ∈ Module.End.invtSubmodule P := by
    intro y hy
    exact hRange y hy
  have hPSymmLinear : P.toLinearMap.IsSymmetric := by
    exact hPSymm
  have hQSymmLinear : Q.toLinearMap.IsSymmetric := by
    exact hQSymm
  have hOrthInv : Q.rangeᗮ ∈ Module.End.invtSubmodule P :=
    hPSymmLinear.orthogonalComplement_mem_invtSubmodule hRangeInv
  have hQOrth : Q.rangeᗮ = Q.ker := by
    simpa using hQSymmLinear.orthogonal_range
  have hKerInv : Q.ker ∈ Module.End.invtSubmodule P := by
    rw [← hQOrth]
    exact hOrthInv
  have hComm : Commute Q P :=
    (hQIdemElem.commute_iff).2 ⟨hRangeInv, hKerInv⟩
  have hEq : Q * P = P * Q := hComm.eq
  have hx := congrArg (fun T : E →L[ℝ] E => T x) hEq
  change Q (P x) = P (Q x) at hx
  exact hx.symm

/-- Family form: pairwise range invariance plus projection geometry gives the
pointwise commutation hypothesis expected by finite projection tensorization. -/
theorem realHilbertProjectionFamily_commute_of_range_invariant
    {E C : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (P : C → E →L[ℝ] E)
    (hIdem : ∀ c : C, (P c).comp (P c) = P c)
    (hSymm : ∀ (c : C) (x y : E),
      inner ℝ (P c x) y = inner ℝ x (P c y))
    (hRange : ∀ (c d : C) (x : E), x ∈ (P d).range → P c x ∈ (P d).range)
    (c d : C)
    (x : E) :
    P c (P d x) = P d (P c x) := by
  exact
    realHilbertProjection_commute_of_range_invariant
      (P c) (P d)
      (hIdem c) (hSymm c)
      (hIdem d) (hSymm d)
      (hRange c d) x

end

end MGAP4D.MathlibAnalytic
