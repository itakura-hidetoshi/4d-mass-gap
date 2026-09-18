import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A finite sum can be decomposed exactly into radius shells once every point
of the finite carrier lies below a common radius cutoff. -/
theorem finiteRealSum_eq_sum_radiusShells
    {alpha : Type*} [DecidableEq alpha]
    (s : Finset alpha)
    (radius : alpha -> Nat)
    (cutoff : Nat)
    (f : alpha -> Real)
    (hRadius : forall x, x ∈ s -> radius x < cutoff) :
    (∑ x ∈ s, f x) =
      ∑ r ∈ Finset.range cutoff,
        ∑ x ∈ s.filter (fun y => radius y = r), f x := by
  classical
  calc
    (∑ x ∈ s, f x) =
        ∑ x ∈ s,
          ∑ r ∈ Finset.range cutoff,
            if radius x = r then f x else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      have hrange : radius x ∈ Finset.range cutoff :=
        Finset.mem_range.mpr (hRadius x hx)
      have hsingle :
          (∑ r ∈ Finset.range cutoff,
            if radius x = r then f x else 0) = f x := by
        simpa using
          (Finset.sum_eq_single
            (s := Finset.range cutoff)
            (f := fun r => if radius x = r then f x else 0)
            (radius x)
            (by
              intro b hb hne
              simp [Ne.symm hne])
            (by
              intro hnot
              exact (hnot hrange).elim))
      exact hsingle.symm
    _ =
        ∑ r ∈ Finset.range cutoff,
          ∑ x ∈ s,
            if radius x = r then f x else 0 := by
      rw [Finset.sum_comm]
    _ =
        ∑ r ∈ Finset.range cutoff,
          ∑ x ∈ s.filter (fun y => radius y = r), f x := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.sum_filter]

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
        (∑ x ∈ s.filter (fun y => radius y = r), f x) <= shell r) :
    (∑ x ∈ s, f x) <= ∑' r : Nat, shell r := by
  rw [finiteRealSum_eq_sum_radiusShells s radius cutoff f hRadius]
  calc
    (∑ r ∈ Finset.range cutoff,
      ∑ x ∈ s.filter (fun y => radius y = r), f x) <=
        ∑ r ∈ Finset.range cutoff, shell r := by
      apply Finset.sum_le_sum
      intro r hr
      exact hShellBound r (Finset.mem_range.mp hr)
    _ <= ∑' r : Nat, shell r :=
      sum_le_tsum
        (Finset.range cutoff)
        (fun r hr => hShellNonneg r)
        hShellSummable

/-- Pointwise radial decay together with a volume-independent shell-cardinality
profile yields a volume-independent bound by the corresponding infinite shell
series.  Geometry enters only through the shell-cardinality profile. -/
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
    (∑ x ∈ s, f x) <=
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
    (∑ x ∈ s.filter (fun y => radius y = r), f x) <=
        ∑ x ∈ s.filter (fun y => radius y = r),
          C * q ^ r := by
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
