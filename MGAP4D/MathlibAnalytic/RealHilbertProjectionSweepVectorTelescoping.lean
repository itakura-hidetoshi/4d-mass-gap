import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenEightColorHeatBathProjectionSweepL2
import Mathlib.Tactic

/-!
# Exact vector telescoping for ordered projection sweeps

The existing projection-sweep API provides exact squared-norm loss, but the
current positive-beta response assembly also needs the vector identity behind
that Pythagorean bookkeeping.

For an ordered family of continuous linear maps P and a list of labels cs,
define the successive residual-vector sum recursively by

  R([], x) = 0,
  R(c :: cs, x) = (x - P c x) + R(cs, P c x).

No idempotence, self-adjointness, or inner-product assumption is needed for the
algebraic telescoping identity

  R(cs, x) = x - sweep(P, cs, x).

We also record append composition and the exact split at an occurrence

  canonicalList = pre ++ d :: suffix,

so that a preserved canonical-prefix witness can expose the residual vector at
the d-stage without any reindexing or cardinality argument.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Ordered sweep over an appended list is the suffix sweep applied after the
prefix sweep. -/
theorem realHilbertProjectionSweep_append
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (P : C → E →L[ℝ] E)
    (pre suffix : List C)
    (x : E) :
    realHilbertProjectionSweep P (pre ++ suffix) x =
      realHilbertProjectionSweep P suffix
        (realHilbertProjectionSweep P pre x) := by
  induction pre generalizing x with
  | nil =>
      simp [realHilbertProjectionSweep]
  | cons c pre ih =>
      simp [realHilbertProjectionSweep, ih]

/-- Recursive sum of the actual vector residuals encountered along an ordered
sweep.  The head residual is evaluated at the current stage vector and the tail
is evaluated after applying the head map. -/
def realHilbertProjectionSweepResidualVectorSum
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (P : C → E →L[ℝ] E) :
    List C → E → E
  | [], _ => 0
  | c :: cs, x =>
      (x - P c x) +
        realHilbertProjectionSweepResidualVectorSum P cs (P c x)

/-- Residual-vector sums themselves compose exactly over list append. -/
theorem realHilbertProjectionSweepResidualVectorSum_append
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (P : C → E →L[ℝ] E)
    (pre suffix : List C)
    (x : E) :
    realHilbertProjectionSweepResidualVectorSum P (pre ++ suffix) x =
      realHilbertProjectionSweepResidualVectorSum P pre x +
        realHilbertProjectionSweepResidualVectorSum P suffix
          (realHilbertProjectionSweep P pre x) := by
  induction pre generalizing x with
  | nil =>
      simp [
        realHilbertProjectionSweepResidualVectorSum,
        realHilbertProjectionSweep]
  | cons c pre ih =>
      simp only [
        List.cons_append,
        realHilbertProjectionSweepResidualVectorSum,
        realHilbertProjectionSweep,
        ContinuousLinearMap.comp_apply]
      rw [ih]
      abel

/-- Exact vector telescoping: the sum of all successive projection residuals is
the initial vector minus the final swept vector. -/
theorem realHilbertProjectionSweepResidualVectorSum_eq_sub_sweep
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (P : C → E →L[ℝ] E)
    (cs : List C)
    (x : E) :
    realHilbertProjectionSweepResidualVectorSum P cs x =
      x - realHilbertProjectionSweep P cs x := by
  induction cs generalizing x with
  | nil =>
      simp [
        realHilbertProjectionSweepResidualVectorSum,
        realHilbertProjectionSweep]
  | cons c cs ih =>
      simp only [
        realHilbertProjectionSweepResidualVectorSum,
        realHilbertProjectionSweep,
        ContinuousLinearMap.comp_apply]
      rw [ih]
      abel

/-- Symmetric orientation of the exact vector telescoping identity. -/
theorem realHilbertProjectionSweep_sub_eq_residualVectorSum
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (P : C → E →L[ℝ] E)
    (cs : List C)
    (x : E) :
    x - realHilbertProjectionSweep P cs x =
      realHilbertProjectionSweepResidualVectorSum P cs x := by
  exact
    (realHilbertProjectionSweepResidualVectorSum_eq_sub_sweep
      P cs x).symm

/-- Exact exposure of the residual vector occurring immediately after a known
prefix.  This is the form consumed by canonical prefix/suffix witnesses. -/
theorem realHilbertProjectionSweepResidualVectorSum_append_cons
    {E C : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (P : C → E →L[ℝ] E)
    (pre suffix : List C)
    (d : C)
    (x : E) :
    realHilbertProjectionSweepResidualVectorSum P (pre ++ d :: suffix) x =
      realHilbertProjectionSweepResidualVectorSum P pre x +
        ((realHilbertProjectionSweep P pre x -
            P d (realHilbertProjectionSweep P pre x)) +
          realHilbertProjectionSweepResidualVectorSum P suffix
            (P d (realHilbertProjectionSweep P pre x))) := by
  rw [realHilbertProjectionSweepResidualVectorSum_append]
  rfl

end

end MathlibAnalytic
end MGAP4D
