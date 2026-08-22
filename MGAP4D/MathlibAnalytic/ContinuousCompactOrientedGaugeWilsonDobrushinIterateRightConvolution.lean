import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonDobrushinIterateKernel
import Mathlib.Tactic

/-!
# Right-convolution laws for finite current influence iterates

The current finite influence iterate kernel is defined by left convolution:

`K_{d+1}(target, source) = ∑ mid, C(target, mid) * K_d(mid, source)`.

The finite heat-bath schedule kernel produced by the current Feller/variation
closure grows in the opposite, terminal direction: an update at `target`
appends the coefficient `C(target, source)` to a previously propagated
variation ending at `target`.

This file proves the matching right-convolution identity

`K_{d+1}(initial, source) = ∑ mid, K_d(initial, mid) * C(mid, source)`

for the same finite kernel.  It also packages the finite truncated Neumann
kernel and its terminal recursion.  These are purely finite algebraic facts and
are the orientation bridge needed before comparing a prescribed heat-bath
schedule with unrestricted influence walks.

No covariance representation, infinite Neumann series, continuum clustering,
positive physical mass, OS Hamiltonian gap, or uniform continuum Dobrushin
threshold is asserted here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The recursively defined finite influence iterate also obeys terminal/right
convolution. -/
theorem finiteInfluenceIterateKernel_succ_right
    {α : Type*}
    [Fintype α]
    [DecidableEq α]
    (influence : α → α → ℝ) :
    ∀ d : ℕ, ∀ initial source : α,
      finiteInfluenceIterateKernel influence (d + 1) initial source =
        ∑ mid : α,
          finiteInfluenceIterateKernel influence d initial mid *
            influence mid source := by
  intro d
  induction d with
  | zero =>
      intro initial source
      simp only [finiteInfluenceIterateKernel]
      rw [Finset.sum_eq_single source]
      · rw [Finset.sum_eq_single initial]
        · simp
        · intro mid _ hmid
          have hne : initial ≠ mid := by
            exact fun h => hmid h.symm
          simp [hne]
        · intro hmem
          exact False.elim (hmem (Finset.mem_univ initial))
      · intro mid _ hmid
        have hne : mid ≠ source := hmid
        simp [hne]
      · intro hmem
        exact False.elim (hmem (Finset.mem_univ source))
  | succ d ih =>
      intro initial source
      change
        (∑ first : α,
          influence initial first *
            finiteInfluenceIterateKernel influence (d + 1) first source) =
          ∑ last : α,
            finiteInfluenceIterateKernel influence (d + 1) initial last *
              influence last source
      calc
        (∑ first : α,
            influence initial first *
              finiteInfluenceIterateKernel influence (d + 1) first source) =
            ∑ first : α,
              ∑ last : α,
                influence initial first *
                  finiteInfluenceIterateKernel influence d first last *
                    influence last source := by
          apply Finset.sum_congr rfl
          intro first _
          rw [ih first source, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro last _
          ring
        _ =
            ∑ last : α,
              ∑ first : α,
                influence initial first *
                  finiteInfluenceIterateKernel influence d first last *
                    influence last source := by
          rw [Finset.sum_comm]
        _ =
            ∑ last : α,
              (∑ first : α,
                influence initial first *
                  finiteInfluenceIterateKernel influence d first last) *
                    influence last source := by
          apply Finset.sum_congr rfl
          intro last _
          rw [Finset.sum_mul]
        _ =
            ∑ last : α,
              finiteInfluenceIterateKernel influence (d + 1) initial last *
                influence last source := by
          rfl

/-- Finite truncated Neumann kernel `I + C + ... + C^n`. -/
noncomputable def finiteInfluenceTruncatedKernel
    {α : Type*}
    [Fintype α]
    (influence : α → α → ℝ)
    (n : ℕ)
    (initial source : α) : ℝ :=
  ∑ d ∈ Finset.range (n + 1),
    finiteInfluenceIterateKernel influence d initial source

@[simp] theorem finiteInfluenceTruncatedKernel_zero
    {α : Type*}
    [Fintype α]
    [DecidableEq α]
    (influence : α → α → ℝ)
    (initial source : α) :
    finiteInfluenceTruncatedKernel influence 0 initial source =
      if initial = source then 1 else 0 := by
  classical
  simp [finiteInfluenceTruncatedKernel, finiteInfluenceIterateKernel]

/-- Adding one truncation degree appends exactly the next finite iterate. -/
theorem finiteInfluenceTruncatedKernel_succ
    {α : Type*}
    [Fintype α]
    (influence : α → α → ℝ)
    (n : ℕ)
    (initial source : α) :
    finiteInfluenceTruncatedKernel influence (n + 1) initial source =
      finiteInfluenceTruncatedKernel influence n initial source +
        finiteInfluenceIterateKernel influence (n + 1) initial source := by
  classical
  unfold finiteInfluenceTruncatedKernel
  rw [show n + 1 + 1 = (n + 1) + 1 by omega]
  rw [Finset.sum_range_succ]

/-- The truncated kernel has the terminal recursion matching a schedule update:
`R_{n+1} = I + R_n C`. -/
theorem finiteInfluenceTruncatedKernel_succ_right
    {α : Type*}
    [Fintype α]
    [DecidableEq α]
    (influence : α → α → ℝ)
    (n : ℕ)
    (initial source : α) :
    finiteInfluenceTruncatedKernel influence (n + 1) initial source =
      (if initial = source then 1 else 0) +
        ∑ mid : α,
          finiteInfluenceTruncatedKernel influence n initial mid *
            influence mid source := by
  classical
  unfold finiteInfluenceTruncatedKernel
  rw [show n + 1 + 1 = (n + 1) + 1 by omega]
  rw [Finset.sum_range_succ]
  simp only [finiteInfluenceIterateKernel_succ_right]
  calc
    (∑ x ∈ Finset.range (n + 1),
        finiteInfluenceIterateKernel influence x initial source) +
      ∑ x : α,
        finiteInfluenceIterateKernel influence n initial x *
          influence x source =
      (if initial = source then 1 else 0) +
        ∑ d ∈ Finset.range (n + 1),
          ∑ mid : α,
            finiteInfluenceIterateKernel influence d initial mid *
              influence mid source := by
        rw [Finset.sum_range_succ']
        have hzero :
            finiteInfluenceIterateKernel influence 0 initial source =
              (if initial = source then 1 else 0) := by
          by_cases h : initial = source <;>
            simp [finiteInfluenceIterateKernel, h]
        rw [hzero]
        have hpositive :
            (∑ x ∈ Finset.range n,
              finiteInfluenceIterateKernel influence (x + 1) initial source) =
              ∑ x ∈ Finset.range n,
                ∑ mid : α,
                  finiteInfluenceIterateKernel influence x initial mid *
                    influence mid source := by
          apply Finset.sum_congr rfl
          intro x _
          exact finiteInfluenceIterateKernel_succ_right influence x initial source
        rw [hpositive]
        rw [Finset.sum_range_succ]
        ring
    _ =
      (if initial = source then 1 else 0) +
        ∑ mid : α,
          (∑ d ∈ Finset.range (n + 1),
            finiteInfluenceIterateKernel influence d initial mid) *
              influence mid source := by
        congr 1
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro mid _
        rw [Finset.sum_mul]
    _ =
      (if initial = source then 1 else 0) +
        ∑ mid : α,
          finiteInfluenceTruncatedKernel influence n initial mid *
            influence mid source := by
        rfl

/-- Nonnegative influence makes every finite truncated kernel nonnegative. -/
theorem finiteInfluenceTruncatedKernel_nonneg
    {α : Type*}
    [Fintype α]
    [DecidableEq α]
    (influence : α → α → ℝ)
    (hInfluence : ∀ target source : α, 0 ≤ influence target source)
    (n : ℕ)
    (initial source : α) :
    0 ≤ finiteInfluenceTruncatedKernel influence n initial source := by
  classical
  unfold finiteInfluenceTruncatedKernel
  exact
    Finset.sum_nonneg fun d hd =>
      finiteInfluenceIterateKernel_nonneg influence hInfluence d initial source

end

end MathlibAnalytic
end MGAP4D
