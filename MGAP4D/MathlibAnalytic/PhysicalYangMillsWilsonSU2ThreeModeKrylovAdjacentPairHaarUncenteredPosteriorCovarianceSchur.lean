import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarUncenteredLocalLinkwiseRayleigh
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Tactic

/-!
# P4-Q2: authentic Wilson posterior mode covariance and finite Schur control

The #5320 linkwise coefficient-L1 envelope preserves the exact posterior
projection losses of the uncentered physical right Krylov orbit. Here we
retain *signed* real-Hilbert cross-correlations before taking any absolute
values:

  K_e(i,j) = inner(V R_i - Q_e V R_i, V R_j - Q_e V R_j),
  K(i,j)   = sum_e K_e(i,j) = (G_right)(i,j).

Unlike estimates that discard inner-product cross terms, this is the
EXACT original Wilson pair-Haar residual Gram; the beta(n) posterior and
the beta(n+1) physical right orbit remain distinct.

A finite real symmetric Schur argument proves that a genuine row bound
  sum_j |K(i,j)| <= C, for all i,
implies
  a* G_right a <= C * sum_i a_i^2.

A second theorem accepts *certified* mode-pair covariance bounds
  |sum_e K_e(i,j)| <= rho(i,j),  sum_j rho(i,j) <= C
to discharge that exact input. The volume-uniform covariance row bound
is NOT claimed here: it remains a concrete original-Wilson locality task.
No Dobrushin replacement, new axiom, sorry/admit, or continuum gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

/-- Finite real symmetric Schur test, retaining the actual matrix entries
rather than a global cardinality-times-maximum bound. -/
private theorem realSymmetricMatrix_rayleigh_le_absRowL2
    {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ)
    (hSym : ∀ i j, A i j = A j i)
    (a : ι → ℝ) (C : ℝ)
    (hRow : ∀ i, (∑ j : ι, |A i j|) ≤ C) :
    star a ⬝ᵥ (Matrix.mulVec A a) ≤
      C * (∑ i : ι, (a i) ^ 2) := by
  classical
  have hScalar (i j : ι) :
      2 * (a i * (A i j * a j)) ≤
        |A i j| * ((a i) ^ 2 + (a j) ^ 2) := by
    have hAM : 2 * (|a i| * |a j|) ≤ (a i) ^ 2 + (a j) ^ 2 := by
      nlinarith [sq_nonneg (|a i| - |a j|),
        sq_abs (a i), sq_abs (a j)]
    have hAbs :
        a i * (A i j * a j) ≤
          |A i j| * (|a i| * |a j|) := by
      calc
        a i * (A i j * a j) ≤ |a i * (A i j * a j)| :=
          le_abs_self _
        _ = |A i j| * (|a i| * |a j|) := by
          simp only [abs_mul]
          ring
    calc
      2 * (a i * (A i j * a j)) ≤
          2 * (|A i j| * (|a i| * |a j|)) :=
        mul_le_mul_of_nonneg_left hAbs (by norm_num)
      _ = |A i j| * (2 * (|a i| * |a j|)) := by ring
      _ ≤ |A i j| * ((a i) ^ 2 + (a j) ^ 2) :=
        mul_le_mul_of_nonneg_left hAM (abs_nonneg _)
  have hDouble :
      (∑ i : ι, ∑ j : ι, 2 * (a i * (A i j * a j))) ≤
        ∑ i : ι, ∑ j : ι,
          |A i j| * ((a i) ^ 2 + (a j) ^ 2) := by
    apply Finset.sum_le_sum
    intro i _hi
    apply Finset.sum_le_sum
    intro j _hj
    exact hScalar i j
  have hSwap :
      (∑ i : ι, ∑ j : ι, |A i j| * (a j) ^ 2) =
      (∑ i : ι, ∑ j : ι, |A i j| * (a i) ^ 2) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro j _hj
    rw [hSym j i]
  have hDiagRows :
      (∑ i : ι, ∑ j : ι, |A i j| * (a i) ^ 2) =
      (∑ i : ι, (a i) ^ 2 * (∑ j : ι, |A i j|)) := by
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    ring
  have hExpand :
      (∑ i : ι, ∑ j : ι,
        |A i j| * ((a i) ^ 2 + (a j) ^ 2)) =
      2 * (∑ i : ι, (a i) ^ 2 * (∑ j : ι, |A i j|)) := by
    calc
      (∑ i : ι, ∑ j : ι,
        |A i j| * ((a i) ^ 2 + (a j) ^ 2)) =
          (∑ i : ι, ∑ j : ι, |A i j| * (a i) ^ 2) +
          (∑ i : ι, ∑ j : ι, |A i j| * (a j) ^ 2) := by
            simp only [mul_add, Finset.sum_add_distrib]
      _ = 2 * (∑ i : ι, ∑ j : ι, |A i j| * (a i) ^ 2) := by
        rw [hSwap]
        ring
      _ = 2 * (∑ i : ι, (a i) ^ 2 * (∑ j : ι, |A i j|)) := by
        rw [hDiagRows]
  have hRowBound :
      (∑ i : ι, (a i) ^ 2 * (∑ j : ι, |A i j|)) ≤
      C * (∑ i : ι, (a i) ^ 2) := by
    calc
      (∑ i : ι, (a i) ^ 2 * (∑ j : ι, |A i j|)) ≤
          ∑ i : ι, (a i) ^ 2 * C := by
            apply Finset.sum_le_sum
            intro i _hi
            exact mul_le_mul_of_nonneg_left (hRow i) (sq_nonneg _)
      _ = C * (∑ i : ι, (a i) ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        ring
  have hRay :
      star a ⬝ᵥ (Matrix.mulVec A a) =
        ∑ i : ι, ∑ j : ι, a i * (A i j * a j) := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
      Finset.mul_sum]
  have hDouble' :
      2 * (∑ i : ι, ∑ j : ι, a i * (A i j * a j)) ≤
        2 * (C * (∑ i : ι, (a i) ^ 2)) := by
    have hh :
        2 * (∑ i : ι, ∑ j : ι, a i * (A i j * a j)) =
          (∑ i : ι, ∑ j : ι, 2 * (a i * (A i j * a j))) := by
      simp only [Finset.mul_sum]
    rw [hh]
    exact hDouble.trans (by
      rw [hExpand]
      exact mul_le_mul_of_nonneg_left hRowBound (by norm_num))
  rw [hRay]
  linarith

local instance p4CovSchurTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4CovSchurCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4CovSchurSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4CovSchurMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4CovSchurBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4CovSchurLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The genuine uncentered physical right-Krylov posterior residual
vector, not merely its norm. -/
noncomputable def fineRightKrylovOriginalPosteriorLinkResidual
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ)
    (e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)))
    (j : Fin (r + 1)) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
      (halfExtent (n + 1)) 2 :=
  let H := halfExtent (n + 1)
  let v := normalizedPhysicalOneSlabPairHaarReceiver
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
    (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n (j : ℕ))
  v - pairHaarTransportedGroundStateSpatialLinkProjection
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) e v

/-- This signed original residual has the same norm as the genuine
linkwise residual introduced in #5320. -/
theorem fineRightKrylovOriginalPosteriorLinkResidual_norm_eq
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ)
    (e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)))
    (j : Fin (r + 1)) :
    ‖fineRightKrylovOriginalPosteriorLinkResidual
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r e j‖ =
      fineRightKrylovOriginalPosteriorLinkResidualNorm
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r e j := by
  rfl

/-- True, signed link-local posterior covariance of two actual right
Krylov inputs, retaining original Wilson half-density transport. -/
noncomputable def fineRightKrylovOriginalPosteriorLinkCovariance
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ)
    (e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)))
    (i j : Fin (r + 1)) : ℝ :=
  inner ℝ
    (fineRightKrylovOriginalPosteriorLinkResidual
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e i)
    (fineRightKrylovOriginalPosteriorLinkResidual
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e j)

/-- Summed covariance of the authentic right-Krylov posterior innovations.
Absolute values are NOT taken before summing links. -/
noncomputable def fineRightKrylovOriginalPosteriorModeCovariance
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (i j : Fin (r + 1)) : ℝ :=
  ∑ e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)),
    fineRightKrylovOriginalPosteriorLinkCovariance
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e i j

/-- These original-Wilson posterior mode covariances are symmetric. -/
theorem fineRightKrylovOriginalPosteriorModeCovariance_symm
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (i j : Fin (r + 1)) :
    fineRightKrylovOriginalPosteriorModeCovariance
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r i j =
    fineRightKrylovOriginalPosteriorModeCovariance
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r j i := by
  classical
  unfold fineRightKrylovOriginalPosteriorModeCovariance
  apply Finset.sum_congr rfl
  intro e _he
  unfold fineRightKrylovOriginalPosteriorLinkCovariance
  exact real_inner_comm _ _

/-- The exact UN-CENTERED physical right-Krylov residual Gram entry is
the sum of the original conditional-expectation link covariances. -/
theorem fineRightKrylovPairHaarResidualGram_entry_eq_originalPosteriorCovariance
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (i j : Fin (r + 1)) :
    (fineRightKrylovPairHaarResidualGram
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r) i j =
      fineRightKrylovOriginalPosteriorModeCovariance
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r i j := by
  classical
  simp only [fineRightKrylovPairHaarResidualGram,
    pairHaarSpatialLinkResidualGram, Matrix.sum_apply, Matrix.gram_apply,
    fineRightKrylovOriginalPosteriorModeCovariance,
    fineRightKrylovOriginalPosteriorLinkCovariance,
    fineRightKrylovOriginalPosteriorLinkResidual]

/-- The physical, signed mode-covariance Schur theorem: an independently
established row bound for the ORIGINAL Wilson posterior innovations
produces a coefficient-L2 Rayleigh bound for the genuine uncentered
right-Krylov Gram. No spatial-link cardinality appears by substitution. -/
theorem fineRightKrylovPairHaarResidualGram_rayleigh_le_originalCovarianceSchur
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ) (C : ℝ)
    (hCovRow : ∀ i : Fin (r + 1),
      (∑ j : Fin (r + 1),
        |fineRightKrylovOriginalPosteriorModeCovariance
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r i j|) ≤ C) :
    star a ⬝ᵥ (Matrix.mulVec
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a) ≤
      C * (∑ j : Fin (r + 1), (a j) ^ 2) := by
  classical
  let G := fineRightKrylovPairHaarResidualGram
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
  have hSym : ∀ i j : Fin (r + 1), G i j = G j i := by
    intro i j
    rw [show G i j =
      fineRightKrylovOriginalPosteriorModeCovariance
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r i j from
      fineRightKrylovPairHaarResidualGram_entry_eq_originalPosteriorCovariance
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r i j]
    rw [show G j i =
      fineRightKrylovOriginalPosteriorModeCovariance
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r j i from
      fineRightKrylovPairHaarResidualGram_entry_eq_originalPosteriorCovariance
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r j i]
    exact fineRightKrylovOriginalPosteriorModeCovariance_symm
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r i j
  have hRow : ∀ i : Fin (r + 1), (∑ j : Fin (r + 1), |G i j|) ≤ C := by
    intro i
    simpa only [G,
      fineRightKrylovPairHaarResidualGram_entry_eq_originalPosteriorCovariance] using
      hCovRow i
  exact realSymmetricMatrix_rayleigh_le_absRowL2 G hSym a C hRow

/-- A user may provide a *proved* covariance pair envelope rho:
it bounds signed sums of physical link correlations, NOT a surrogate
posterior or a postulated covariance decay. -/
theorem fineRightKrylovPairHaarResidualGram_rayleigh_le_certifiedCovarianceSchur
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ)
    (rho : Fin (r + 1) → Fin (r + 1) → ℝ) (C : ℝ)
    (hRho : ∀ i j : Fin (r + 1),
      |fineRightKrylovOriginalPosteriorModeCovariance
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r i j| ≤ rho i j)
    (hRow : ∀ i : Fin (r + 1), (∑ j : Fin (r + 1), rho i j) ≤ C) :
    star a ⬝ᵥ (Matrix.mulVec
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a) ≤
      C * (∑ j : Fin (r + 1), (a j) ^ 2) := by
  apply fineRightKrylovPairHaarResidualGram_rayleigh_le_originalCovarianceSchur
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r a C
  intro i
  calc
    (∑ j : Fin (r + 1),
      |fineRightKrylovOriginalPosteriorModeCovariance
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r i j|) ≤
      ∑ j : Fin (r + 1), rho i j := by
        apply Finset.sum_le_sum
        intro j _hj
        exact hRho i j
    _ ≤ C := hRow i

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
