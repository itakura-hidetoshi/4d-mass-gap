import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenCurrentInfluenceWalkKernelSupport
import Mathlib.Tactic

/-!
# Finite iterates of the current compact Dobrushin influence kernel

The same-root route now knows the exact physical support of finite influence
walks.  This file develops the complementary quantitative algebra for a finite
nonnegative influence matrix.

For a finite type `α`, define the recursive degree-`d` influence kernel by

* degree zero: the identity kernel;
* degree `d+1`: one influence step followed by the degree-`d` kernel.

If every influence row has sum at most `c`, with `c >= 0`, then every degree-`d`
row has sum at most `c^d`.  Nonnegativity then gives the pointwise bound
`K_d(i,j) <= c^d`.

The current compact-Haar Dobrushin matrix carrier supplies exactly these
hypotheses, so its finite iterates inherit coefficient-power bounds.  For the
actual periodic compact `SU(N)` carrier under the explicit finite-volume
threshold, the bound specializes to `(18 * q(beta))^d`.

This is finite-kernel algebra only.  It is not a covariance theorem, does not
sum an infinite Neumann series, does not assert the threshold along the
factorial continuum coupling sequence, and does not identify heat-bath update
time with physical OS Euclidean time.
-/

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Recursive finite iterate of an influence kernel on a finite type. -/
noncomputable def finiteInfluenceIterateKernel
    {α : Type*}
    [Fintype α]
    (influence : α → α → ℝ) : ℕ → α → α → ℝ
  | 0, target, source => by
      classical
      exact if target = source then 1 else 0
  | d + 1, target, source =>
      ∑ mid : α,
        influence target mid * finiteInfluenceIterateKernel influence d mid source

/-- Nonnegative influence entries give nonnegative entries in every finite
iterate. -/
theorem finiteInfluenceIterateKernel_nonneg
    {α : Type*}
    [Fintype α]
    [DecidableEq α]
    (influence : α → α → ℝ)
    (hInfluence : ∀ target source : α, 0 ≤ influence target source) :
    ∀ d : ℕ, ∀ target source : α,
      0 ≤ finiteInfluenceIterateKernel influence d target source := by
  intro d
  induction d with
  | zero =>
      intro target source
      simp [finiteInfluenceIterateKernel]
  | succ d ih =>
      intro target source
      change
        0 ≤ ∑ mid : α,
          influence target mid *
            finiteInfluenceIterateKernel influence d mid source
      exact
        Finset.sum_nonneg fun mid _ =>
          mul_nonneg (hInfluence target mid) (ih mid source)

/-- A uniform nonnegative row-sum majorant propagates multiplicatively through
finite influence iterates. -/
theorem finiteInfluenceIterateKernel_rowSum_le_pow
    {α : Type*}
    [Fintype α]
    [DecidableEq α]
    (influence : α → α → ℝ)
    (hInfluence : ∀ target source : α, 0 ≤ influence target source)
    (c : ℝ)
    (hc : 0 ≤ c)
    (hrow : ∀ target : α, ∑ source : α, influence target source ≤ c)
    (d : ℕ)
    (target : α) :
    (∑ source : α,
      finiteInfluenceIterateKernel influence d target source) ≤ c ^ d := by
  induction d generalizing target with
  | zero =>
      simp [finiteInfluenceIterateKernel]
  | succ d ih =>
      change
        (∑ source : α,
          ∑ mid : α,
            influence target mid *
              finiteInfluenceIterateKernel influence d mid source) ≤
          c ^ (d + 1)
      rw [Finset.sum_comm]
      calc
        (∑ mid : α,
            ∑ source : α,
              influence target mid *
                finiteInfluenceIterateKernel influence d mid source) =
            ∑ mid : α,
              influence target mid *
                (∑ source : α,
                  finiteInfluenceIterateKernel influence d mid source) := by
          apply Finset.sum_congr rfl
          intro mid _
          rw [Finset.mul_sum]
        _ ≤ ∑ mid : α, influence target mid * c ^ d := by
          apply Finset.sum_le_sum
          intro mid _
          exact
            mul_le_mul_of_nonneg_left
              (ih mid)
              (hInfluence target mid)
        _ = (∑ mid : α, influence target mid) * c ^ d := by
          rw [Finset.sum_mul]
        _ ≤ c * c ^ d := by
          exact
            mul_le_mul_of_nonneg_right
              (hrow target)
              (pow_nonneg hc d)
        _ = c ^ (d + 1) := by
          rw [pow_succ]
          ring

/-- The same row-sum hypothesis gives the pointwise coefficient-power bound. -/
theorem finiteInfluenceIterateKernel_le_pow
    {α : Type*}
    [Fintype α]
    [DecidableEq α]
    (influence : α → α → ℝ)
    (hInfluence : ∀ target source : α, 0 ≤ influence target source)
    (c : ℝ)
    (hc : 0 ≤ c)
    (hrow : ∀ target : α, ∑ source : α, influence target source ≤ c)
    (d : ℕ)
    (target source : α) :
    finiteInfluenceIterateKernel influence d target source ≤ c ^ d := by
  have hNonneg :=
    finiteInfluenceIterateKernel_nonneg influence hInfluence d
  have hSingle :
      finiteInfluenceIterateKernel influence d target source ≤
        ∑ other : α,
          finiteInfluenceIterateKernel influence d target other := by
    exact
      Finset.single_le_sum
        (fun other _ => hNonneg target other)
        (Finset.mem_univ source)
  exact
    hSingle.trans
      (finiteInfluenceIterateKernel_rowSum_le_pow
        influence hInfluence c hc hrow d target)

/-- Every current compact Dobrushin matrix has finite iterate row sums bounded
by the corresponding power of its strict coefficient. -/
theorem continuous_compact_oriented_dobrushin_influenceIterateKernel_rowSum_le_pow
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (d : ℕ)
    (target : C.base.geometry.Edge) :
    (∑ source : C.base.geometry.Edge,
      finiteInfluenceIterateKernel D.influence d target source) ≤
        D.coefficient ^ d := by
  classical
  exact
    finiteInfluenceIterateKernel_rowSum_le_pow
      D.influence D.influence_nonneg D.coefficient D.coefficient_nonneg
      D.rowSum_le_coefficient d target

/-- Every entry of every finite current compact Dobrushin iterate is bounded by
`coefficient^d`. -/
theorem continuous_compact_oriented_dobrushin_influenceIterateKernel_le_pow
    (C : ContinuousCompactOrientedGaugeWilsonSystem)
    (D : ContinuousCompactOrientedGaugeWilsonDobrushinMatrixData C)
    (d : ℕ)
    (target source : C.base.geometry.Edge) :
    finiteInfluenceIterateKernel D.influence d target source ≤
      D.coefficient ^ d := by
  classical
  exact
    finiteInfluenceIterateKernel_le_pow
      D.influence D.influence_nonneg D.coefficient D.coefficient_nonneg
      D.rowSum_le_coefficient d target source

private instance periodicHypercubicEvenSideLength_neZero_iterateKernel
    (H : ℕ) : NeZero (PeriodicHypercubicEvenSideLength H) :=
  ⟨by simp [PeriodicHypercubicEvenSideLength]⟩

/-- For the actual periodic compact `SU(N)` Dobrushin carrier, the finite
iterate bound is the explicit power `(18 * q(beta))^d`. -/
theorem periodicHypercubicEvenSpecialUnitary_sparseDobrushinMatrixData_influenceIterateKernel_le_pow
    (H N : ℕ)
    (hH : 0 < H)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (hBeta : 0 ≤ beta)
    (hThreshold :
      18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta < 1)
    (d : ℕ)
    (target source : PeriodicHypercubicEvenEdge H) :
    finiteInfluenceIterateKernel
        (periodicHypercubicSpecialUnitary_sparseDobrushinMatrixData_of_threshold
          (PeriodicHypercubicEvenSideLength H) N
          (by
            simp [PeriodicHypercubicEvenSideLength]
            omega)
          hN beta hBeta hThreshold).influence
        d target source ≤
      (18 * periodicHypercubicSpecialUnitaryActiveTVMajorant beta) ^ d := by
  classical
  let C :=
    periodicHypercubicSpecialUnitaryWilsonSystem
      (PeriodicHypercubicEvenSideLength H) N hN beta hBeta
  let D :=
    periodicHypercubicSpecialUnitary_sparseDobrushinMatrixData_of_threshold
      (PeriodicHypercubicEvenSideLength H) N
      (by
        simp [PeriodicHypercubicEvenSideLength]
        omega)
      hN beta hBeta hThreshold
  have hBound :=
    continuous_compact_oriented_dobrushin_influenceIterateKernel_le_pow
      C D d target source
  simpa [C, D,
    periodicHypercubicSpecialUnitary_sparseDobrushinMatrixData_of_threshold] using hBound

end

end MathlibAnalytic
end MGAP4D
