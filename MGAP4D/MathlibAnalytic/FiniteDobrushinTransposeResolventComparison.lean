import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonDobrushinIterateKernel
import Mathlib.Tactic

/-!
# Finite transpose-Dobrushin resolvent comparison

This file isolates the finite algebra needed for the two-sided covariance route.
For a finite nonnegative influence kernel `D`, suppose a profile `w` is
subinvariant for the transpose action,

`w(s) ≤ v(s) + ∑ t, D(t,s) w(t)`.

With the canonical recursive influence iterates

`K_{d+1}(t,s) = ∑ m, D(t,m) K_d(m,s)`,

the residual weighted by `K_d` advances by exactly one degree.  Iterating this
gives the finite Neumann comparison

`w(s) ≤ ∑_{k<d} ∑_i K_k(i,s) v(i) + ∑_i K_d(i,s) w(i)`.

Under the usual row-sum majorant `c`, the residual is bounded by
`c^d * ∑_i w(i)` for nonnegative `w`.

Only finite sums occur here.  No infinite Neumann series, covariance decay,
continuum clustering, or physical mass-gap statement is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- One residual step for a transpose-Dobrushin subinvariant profile.  The
orientation is chosen so that the existing recursive iterate kernel advances
without introducing a separate transpose-kernel definition. -/
theorem finiteInfluenceIterateKernel_weighted_subinvariant_step
    {α : Type*}
    [Fintype α]
    [DecidableEq α]
    (influence : α → α → ℝ)
    (hInfluence : ∀ target source : α, 0 ≤ influence target source)
    (v w : α → ℝ)
    (hSub : ∀ source : α,
      w source ≤ v source + ∑ target : α, influence target source * w target)
    (d : ℕ)
    (source : α) :
    (∑ initial : α,
        finiteInfluenceIterateKernel influence d initial source * w initial) ≤
      (∑ initial : α,
        finiteInfluenceIterateKernel influence d initial source * v initial) +
      ∑ initial : α,
        finiteInfluenceIterateKernel influence (d + 1) initial source * w initial := by
  calc
    (∑ initial : α,
        finiteInfluenceIterateKernel influence d initial source * w initial) ≤
      ∑ initial : α,
        finiteInfluenceIterateKernel influence d initial source *
          (v initial + ∑ target : α, influence target initial * w target) := by
      apply Finset.sum_le_sum
      intro initial _
      exact
        mul_le_mul_of_nonneg_left
          (hSub initial)
          (finiteInfluenceIterateKernel_nonneg influence hInfluence d initial source)
    _ =
      (∑ initial : α,
          finiteInfluenceIterateKernel influence d initial source * v initial) +
        ∑ initial : α,
          finiteInfluenceIterateKernel influence d initial source *
            (∑ target : α, influence target initial * w target) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
    _ =
      (∑ initial : α,
          finiteInfluenceIterateKernel influence d initial source * v initial) +
        ∑ target : α,
          finiteInfluenceIterateKernel influence (d + 1) target source * w target := by
      congr 1
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro target _
      calc
        (∑ initial : α,
            finiteInfluenceIterateKernel influence d initial source *
              (influence target initial * w target)) =
          ∑ initial : α,
            (influence target initial *
              finiteInfluenceIterateKernel influence d initial source) * w target := by
            apply Finset.sum_congr rfl
            intro initial _
            ring
        _ =
          (∑ initial : α,
              influence target initial *
                finiteInfluenceIterateKernel influence d initial source) * w target := by
            rw [Finset.sum_mul]
        _ = finiteInfluenceIterateKernel influence (d + 1) target source * w target := by
            rfl

/-- Finite Neumann comparison for a transpose-Dobrushin subinvariant profile. -/
theorem finiteInfluenceIterateKernel_subinvariant_le_partial_resolvent_add_residual
    {α : Type*}
    [Fintype α]
    [DecidableEq α]
    (influence : α → α → ℝ)
    (hInfluence : ∀ target source : α, 0 ≤ influence target source)
    (v w : α → ℝ)
    (hSub : ∀ source : α,
      w source ≤ v source + ∑ target : α, influence target source * w target)
    (d : ℕ)
    (source : α) :
    w source ≤
      (Finset.range d).sum
        (fun k => ∑ initial : α,
          finiteInfluenceIterateKernel influence k initial source * v initial) +
      ∑ initial : α,
        finiteInfluenceIterateKernel influence d initial source * w initial := by
  induction d with
  | zero =>
      simp [finiteInfluenceIterateKernel]
  | succ d ih =>
      have hStep :=
        finiteInfluenceIterateKernel_weighted_subinvariant_step
          influence hInfluence v w hSub d source
      calc
        w source ≤
          (Finset.range d).sum
              (fun k => ∑ initial : α,
                finiteInfluenceIterateKernel influence k initial source * v initial) +
            ∑ initial : α,
              finiteInfluenceIterateKernel influence d initial source * w initial := ih
        _ ≤
          (Finset.range d).sum
              (fun k => ∑ initial : α,
                finiteInfluenceIterateKernel influence k initial source * v initial) +
            ((∑ initial : α,
                finiteInfluenceIterateKernel influence d initial source * v initial) +
              ∑ initial : α,
                finiteInfluenceIterateKernel influence (d + 1) initial source * w initial) := by
          exact add_le_add_left hStep _
        _ =
          (Finset.range (d + 1)).sum
              (fun k => ∑ initial : α,
                finiteInfluenceIterateKernel influence k initial source * v initial) +
            ∑ initial : α,
              finiteInfluenceIterateKernel influence (d + 1) initial source * w initial := by
          rw [Finset.sum_range_succ]
          ring

/-- A row-sum majorant controls every weighted residual by `c^d` times the
`ℓ¹` mass of a nonnegative profile. -/
theorem finiteInfluenceIterateKernel_weighted_residual_le_pow_mul_sum
    {α : Type*}
    [Fintype α]
    [DecidableEq α]
    (influence : α → α → ℝ)
    (hInfluence : ∀ target source : α, 0 ≤ influence target source)
    (c : ℝ)
    (hc : 0 ≤ c)
    (hrow : ∀ target : α, ∑ source : α, influence target source ≤ c)
    (w : α → ℝ)
    (hw : ∀ initial : α, 0 ≤ w initial)
    (d : ℕ)
    (source : α) :
    (∑ initial : α,
        finiteInfluenceIterateKernel influence d initial source * w initial) ≤
      c ^ d * ∑ initial : α, w initial := by
  calc
    (∑ initial : α,
        finiteInfluenceIterateKernel influence d initial source * w initial) ≤
      ∑ initial : α, c ^ d * w initial := by
        apply Finset.sum_le_sum
        intro initial _
        exact
          mul_le_mul_of_nonneg_right
            (finiteInfluenceIterateKernel_le_pow
              influence hInfluence c hc hrow d initial source)
            (hw initial)
    _ = c ^ d * ∑ initial : α, w initial := by
      rw [Finset.mul_sum]

/-- Finite Neumann comparison with the residual replaced by the coefficient
power bound. -/
theorem finiteInfluenceIterateKernel_subinvariant_le_partial_resolvent_add_pow_residual
    {α : Type*}
    [Fintype α]
    [DecidableEq α]
    (influence : α → α → ℝ)
    (hInfluence : ∀ target source : α, 0 ≤ influence target source)
    (c : ℝ)
    (hc : 0 ≤ c)
    (hrow : ∀ target : α, ∑ source : α, influence target source ≤ c)
    (v w : α → ℝ)
    (hw : ∀ initial : α, 0 ≤ w initial)
    (hSub : ∀ source : α,
      w source ≤ v source + ∑ target : α, influence target source * w target)
    (d : ℕ)
    (source : α) :
    w source ≤
      (Finset.range d).sum
        (fun k => ∑ initial : α,
          finiteInfluenceIterateKernel influence k initial source * v initial) +
      c ^ d * ∑ initial : α, w initial := by
  exact
    (finiteInfluenceIterateKernel_subinvariant_le_partial_resolvent_add_residual
      influence hInfluence v w hSub d source).trans
      (add_le_add_left
        (finiteInfluenceIterateKernel_weighted_residual_le_pow_mul_sum
          influence hInfluence c hc hrow w hw d source)
        _)

end

end MathlibAnalytic
end MGAP4D
