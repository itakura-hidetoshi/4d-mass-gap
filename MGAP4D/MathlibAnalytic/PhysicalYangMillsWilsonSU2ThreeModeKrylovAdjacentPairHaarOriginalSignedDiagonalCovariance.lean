import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSignedDiagonalTrace
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# P4-Q2-E: authentic signed all-link covariance controlled by diagonal energy

PR #5339 identifies the trace of the exact original UN-CENTERED fine-right
Krylov Gram with the full sum of original posterior innovation norms.
PR #5321 retains the SIGNED all-link cross-covariance
  K(i,j) = sum_e inner(I_e(R_i), I_e(R_j)) = G_right(i,j).

For each authentic mode define its actual posterior diagonal
  D_i = sum_e ||I_e(R_i)||^2 = G_right(i,i).
Cauchy--Schwarz in the physical real Hilbert space AND over the actual
Wilson spatial links yields a non-fictitious signed covariance bound
  K(i,j)^2 <= D_i D_j.
The elementary arithmetic-mean bound
  2 |K(i,j)| <= D_i + D_j
then supplies a concrete row envelope for the existing #5321 Schur
test without inventing off-diagonal decay.

These are exact ORIGINAL Wilson posterior quantities, with fine
beta(n+1) orbit and frozen beta(n) receiver. They do NOT prove that
the row envelope or the diagonal trace is uniform in spatial volume.
No Dobrushin, surrogate law, new axiom, sorry or admit.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

local instance p4DiagCovTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4DiagCovCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4DiagCovSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4DiagCovMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4DiagCovBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4DiagCovLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Actual diagonal Wilson posterior-resampling loss of ONE of the
original uncentered fine-right Krylov modes, no global sup. -/
noncomputable def fineRightKrylovOriginalPosteriorModeDiagonalEnergy
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (j : Fin (r + 1)) : ℝ :=
  ∑ e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)),
    (fineRightKrylovOriginalPosteriorLinkResidualNorm
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e j) ^ 2

theorem fineRightKrylovOriginalPosteriorModeDiagonalEnergy_nonneg
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (j : Fin (r + 1)) :
    0 ≤ fineRightKrylovOriginalPosteriorModeDiagonalEnergy
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r j := by
  unfold fineRightKrylovOriginalPosteriorModeDiagonalEnergy
  exact Finset.sum_nonneg (fun e _he => sq_nonneg _)

/-- No surrogate covariance: each physical diagonal IS the exact
original uncentered signed-Wilson Krylov Gram diagonal entry. -/
theorem fineRightKrylovOriginalPosteriorModeDiagonalEnergy_eq_gram_diag
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (j : Fin (r + 1)) :
    fineRightKrylovOriginalPosteriorModeDiagonalEnergy
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r j =
    (fineRightKrylovPairHaarResidualGram
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r) j j := by
  classical
  calc
    fineRightKrylovOriginalPosteriorModeDiagonalEnergy
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r j =
      ∑ e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)),
        fineRightKrylovOriginalPosteriorLinkCovariance
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r e j j := by
        unfold fineRightKrylovOriginalPosteriorModeDiagonalEnergy
        apply Finset.sum_congr rfl
        intro e _he
        exact (fineRightKrylovOriginalPosteriorLinkCovariance_diag_eq_residualNorm_sq
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r e j).symm
    _ = (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) j j := by
      rw [fineRightKrylovPairHaarResidualGram_entry_eq_originalPosteriorCovariance]
      rfl

/-- The signed all-link mode cross-covariance obeys exact finite-link
Cauchy--Schwarz, BEFORE any replacement by a link-count maximum.
This is a quadratic bound and retains negative cross-correlations. -/
theorem fineRightKrylovOriginalPosteriorModeCovariance_sq_le_diagonalEnergy
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (i j : Fin (r + 1)) :
    (fineRightKrylovOriginalPosteriorModeCovariance
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r i j) ^ 2 ≤
    fineRightKrylovOriginalPosteriorModeDiagonalEnergy
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r i *
    fineRightKrylovOriginalPosteriorModeDiagonalEnergy
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r j := by
  classical
  let H := halfExtent (n + 1)
  let d : PeriodicHypercubicEvenSpatialSliceLink H →
      Fin (r + 1) → ℝ :=
    fun e k => fineRightKrylovOriginalPosteriorLinkResidualNorm
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e k
  let K := fineRightKrylovOriginalPosteriorModeCovariance
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r
  have hLink (e : PeriodicHypercubicEvenSpatialSliceLink H) :
      |fineRightKrylovOriginalPosteriorLinkCovariance
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r e i j| ≤ d e i * d e j := by
    let vi := fineRightKrylovOriginalPosteriorLinkResidual
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e i
    let vj := fineRightKrylovOriginalPosteriorLinkResidual
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e j
    have hCS := abs_real_inner_le_norm vi vj
    change |fineRightKrylovOriginalPosteriorLinkCovariance
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e i j| ≤ d e i * d e j at hCS
    exact hCS
  have hSum :
      |K i j| ≤ ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        d e i * d e j := by
    change |∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        fineRightKrylovOriginalPosteriorLinkCovariance
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r e i j| ≤
      ∑ e : PeriodicHypercubicEvenSpatialSliceLink H, d e i * d e j
    calc
      |∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        fineRightKrylovOriginalPosteriorLinkCovariance
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r e i j| ≤
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          |fineRightKrylovOriginalPosteriorLinkCovariance
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r e i j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          d e i * d e j := by
        apply Finset.sum_le_sum
        intro e _he
        exact hLink e
  have hCS :
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        d e i * d e j) ^ 2 ≤
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        (d e i) ^ 2) *
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        (d e j) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset (PeriodicHypercubicEvenSpatialSliceLink H))
      (fun e => d e i) (fun e => d e j)
  change (K i j) ^ 2 ≤
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      (d e i) ^ 2) *
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      (d e j) ^ 2)
  calc
    (K i j) ^ 2 = |K i j| ^ 2 := (sq_abs _).symm
    _ ≤ (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          d e i * d e j) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) hSum 2
    _ ≤ (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          (d e i) ^ 2) *
        (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          (d e j) ^ 2) := hCS

/-- Genuine signed posterior-mode cross covariance is controlled by
the ARITHMETIC MEAN of the two actual posterior diagonal energies.
No total-spatial-link cardinality occurs in this bound. -/
theorem fineRightKrylovOriginalPosteriorModeCovariance_two_abs_le_diagonal
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (i j : Fin (r + 1)) :
    2 * |fineRightKrylovOriginalPosteriorModeCovariance
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r i j| ≤
    fineRightKrylovOriginalPosteriorModeDiagonalEnergy
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r i +
    fineRightKrylovOriginalPosteriorModeDiagonalEnergy
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r j := by
  classical
  let H := halfExtent (n + 1)
  let d : PeriodicHypercubicEvenSpatialSliceLink H →
      Fin (r + 1) → ℝ :=
    fun e k => fineRightKrylovOriginalPosteriorLinkResidualNorm
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e k
  let K := fineRightKrylovOriginalPosteriorModeCovariance
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
  have hOne (e : PeriodicHypercubicEvenSpatialSliceLink H) :
      |fineRightKrylovOriginalPosteriorLinkCovariance
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r e i j| ≤ d e i * d e j := by
    let vi := fineRightKrylovOriginalPosteriorLinkResidual
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e i
    let vj := fineRightKrylovOriginalPosteriorLinkResidual
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e j
    have h := abs_real_inner_le_norm vi vj
    change |fineRightKrylovOriginalPosteriorLinkCovariance
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e i j| ≤ d e i * d e j at h
    exact h
  have hAbs :
      |K i j| ≤ ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        d e i * d e j := by
    change |∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        fineRightKrylovOriginalPosteriorLinkCovariance
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r e i j| ≤
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H, d e i * d e j
    calc
      |∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        fineRightKrylovOriginalPosteriorLinkCovariance
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r e i j| ≤
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          |fineRightKrylovOriginalPosteriorLinkCovariance
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r e i j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          d e i * d e j := by
        apply Finset.sum_le_sum
        intro e _he
        exact hOne e
  have hPoint (e : PeriodicHypercubicEvenSpatialSliceLink H) :
      2 * (d e i * d e j) ≤ (d e i) ^ 2 + (d e j) ^ 2 := by
    nlinarith [sq_nonneg (d e i - d e j)]
  have hSum :
      2 * (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        d e i * d e j) ≤
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        (d e i) ^ 2) +
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        (d e j) ^ 2) := by
    calc
      2 * (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          d e i * d e j) =
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          2 * (d e i * d e j) := by rw [Finset.mul_sum]
      _ ≤ ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          ((d e i) ^ 2 + (d e j) ^ 2) := by
        apply Finset.sum_le_sum
        intro e _he
        exact hPoint e
      _ = (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          (d e i) ^ 2) +
        (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          (d e j) ^ 2) := by rw [Finset.sum_add_distrib]
  change 2 * |K i j| ≤
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      (d e i) ^ 2) +
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      (d e j) ^ 2)
  calc
    2 * |K i j| ≤
      2 * (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        d e i * d e j) :=
      mul_le_mul_of_nonneg_left hAbs (by norm_num)
    _ ≤ _ := hSum

/-- Existing #5321 signed Schur row is bounded by a CONSTRUCTED
actual posterior diagonal envelope, with no arbitrary rho function. -/
theorem fineRightKrylovOriginalPosteriorModeCovariance_absRow_le_diagonal
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (i : Fin (r + 1)) :
    (∑ j : Fin (r + 1),
      |fineRightKrylovOriginalPosteriorModeCovariance
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r i j|) ≤
    ∑ j : Fin (r + 1),
      (fineRightKrylovOriginalPosteriorModeDiagonalEnergy
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r i +
       fineRightKrylovOriginalPosteriorModeDiagonalEnergy
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r j) / 2 := by
  apply Finset.sum_le_sum
  intro j _hj
  have hh :=
    fineRightKrylovOriginalPosteriorModeCovariance_two_abs_le_diagonal
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r i j
  linarith

/-- A CERTIFIED diagonal-energy row majorant is enough for the
original signed-Schur Gram Rayleigh result. No spatial-volume-uniform
diagonal row bound is asserted; the hypothesis is the exact frontier. -/
theorem fineRightKrylovPairHaarResidualGram_rayleigh_le_certifiedDiagonalSchur
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ) (C : ℝ)
    (hDiagRow : ∀ i : Fin (r + 1),
      (∑ j : Fin (r + 1),
        (fineRightKrylovOriginalPosteriorModeDiagonalEnergy
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r i +
         fineRightKrylovOriginalPosteriorModeDiagonalEnergy
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r j) / 2) ≤ C) :
    star a ⬝ᵥ (Matrix.mulVec
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a) ≤ C * (∑ j : Fin (r + 1), (a j) ^ 2) := by
  apply fineRightKrylovPairHaarResidualGram_rayleigh_le_originalCovarianceSchur
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r a C
  intro i
  exact (fineRightKrylovOriginalPosteriorModeCovariance_absRow_le_diagonal
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r i).trans (hDiagRow i)

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
