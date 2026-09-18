import MGAP4D.MathlibAnalytic.FiniteDistanceShellGeometricSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A finite sum can be decomposed exactly into radius shells once every point
of the finite carrier lies below a common radius cutoff.

This is the finite-subset analogue of
`FiniteDistanceShellGeometricSum.sum_pow_distance_eq_shell_sum`. -/
theorem finiteRealSum_eq_sum_radiusShells
    {alpha : Type*} [DecidableEq alpha]
    (s : Finset alpha)
    (radius : alpha -> Nat)
    (cutoff : Nat)
    (f : alpha -> Real)
    (hRadius : forall x, x ∈ s -> radius x < cutoff) :
    Finset.sum s f =
      Finset.sum (Finset.range cutoff) (fun r =>
        Finset.sum (s.filter (fun y => radius y = r)) f) := by
  classical
  calc
    Finset.sum s f =
        Finset.sum s (fun x =>
          Finset.sum (Finset.range cutoff) (fun r =>
            if radius x = r then f x else 0)) := by
      apply Finset.sum_congr rfl
      intro x hx
      symm
      rw [Finset.sum_eq_single (radius x)]
      · simp
      · intro r hr hne
        simp [Ne.symm hne]
      · intro hnot
        exact (hnot (Finset.mem_range.mpr (hRadius x hx))).elim
    _ =
        Finset.sum (Finset.range cutoff) (fun r =>
          Finset.sum s (fun x =>
            if radius x = r then f x else 0)) := by
      rw [Finset.sum_comm]
    _ =
        Finset.sum (Finset.range cutoff) (fun r =>
          Finset.sum (s.filter (fun y => radius y = r)) f) := by
      apply Finset.sum_congr rfl
      intro r _hr
      rw [<- Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _hx
      by_cases hxr : radius x = r <;> simp [hxr]

/-- If every finite radius shell is bounded by a nonnegative summable profile,
then the complete finite carrier sum is bounded by the infinite profile mass. -/
theorem finiteRealSum_le_tsum_of_radiusShellBound
    {alpha : Type*} [DecidableEq alpha]
    (s : Finset alpha)
    (radius : alpha -> Nat)
    (cutoff : Nat)
    (f : alpha -> Real)
    (shell : Nat -> Real)
    (hRadius : forall x, x ∈ s -> radius x < cutoff)
    (hShellNonneg : forall r, 0 <= shell r)
    (hShellSummable : Summable shell)
    (hShellBound :
      forall r, r < cutoff ->
        Finset.sum (s.filter (fun y => radius y = r)) f <= shell r) :
    Finset.sum s f <= ∑' r : Nat, shell r := by
  rw [finiteRealSum_eq_sum_radiusShells s radius cutoff f hRadius]
  calc
    Finset.sum (Finset.range cutoff) (fun r =>
      Finset.sum (s.filter (fun y => radius y = r)) f) <=
        Finset.sum (Finset.range cutoff) shell := by
      apply Finset.sum_le_sum
      intro r hr
      exact hShellBound r (Finset.mem_range.mp hr)
    _ <= ∑' r : Nat, shell r :=
      hShellSummable.sum_le_tsum
        (Finset.range cutoff)
        (fun r _hr => hShellNonneg r)

/-- Pointwise radial decay together with a volume-independent shell-cardinality
profile yields a volume-independent bound by the corresponding infinite shell
series. Geometry enters only through the shell-cardinality profile. -/
theorem finiteRealSum_le_tsum_of_pointwiseDecay_shellCardinality
    {alpha : Type*} [DecidableEq alpha]
    (s : Finset alpha)
    (radius : alpha -> Nat)
    (cutoff : Nat)
    (f : alpha -> Real)
    (C q : Real)
    (shellCardMajorant : Nat -> Real)
    (hRadius : forall x, x ∈ s -> radius x < cutoff)
    (hC : 0 <= C)
    (hq : 0 <= q)
    (hShellCardMajorantNonneg : forall r, 0 <= shellCardMajorant r)
    (hPointwise :
      forall x, x ∈ s ->
        f x <= C * q ^ radius x)
    (hShellCard :
      forall r, r < cutoff ->
        (((s.filter (fun y => radius y = r)).card : Nat) : Real) <=
          shellCardMajorant r)
    (hSummable :
      Summable (fun r : Nat =>
        shellCardMajorant r * (C * q ^ r))) :
    Finset.sum s f <=
      ∑' r : Nat, shellCardMajorant r * (C * q ^ r) := by
  refine
    finiteRealSum_le_tsum_of_radiusShellBound
      s radius cutoff f
      (fun r => shellCardMajorant r * (C * q ^ r))
      hRadius
      (fun r =>
        mul_nonneg
          (hShellCardMajorantNonneg r)
          (mul_nonneg hC (pow_nonneg hq r)))
      hSummable
      ?_
  intro r hr
  calc
    Finset.sum (s.filter (fun y => radius y = r)) f <=
        Finset.sum (s.filter (fun y => radius y = r))
          (fun _x => C * q ^ r) := by
      apply Finset.sum_le_sum
      intro x hx
      have hxs : x ∈ s := (Finset.mem_filter.mp hx).1
      have hxRadius : radius x = r := (Finset.mem_filter.mp hx).2
      simpa [hxRadius] using hPointwise x hxs
    _ =
        (((s.filter (fun y => radius y = r)).card : Nat) : Real) *
          (C * q ^ r) := by
      simp [nsmul_eq_mul]
    _ <=
        shellCardMajorant r * (C * q ^ r) := by
      exact
        mul_le_mul_of_nonneg_right
          (hShellCard r hr)
          (mul_nonneg hC (pow_nonneg hq r))

end

end MathlibAnalytic
end MGAP4D
