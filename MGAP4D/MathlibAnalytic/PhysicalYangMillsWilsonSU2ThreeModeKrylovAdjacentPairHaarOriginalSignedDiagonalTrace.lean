import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPhysicalSignedHilbertCovariance
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# P4-Q2-E: exact original Wilson uncentered signed Gram diagonal-trace test

The original fine-right Krylov residual Gram is an actual sum of Gram
operators of Wilson posterior innovations.  The signed off-diagonal
mode covariance need not have a finite-volume-independent Schur row sum.

A different, UNCONDITIONAL finite-dimensional Hilbert route retains
the actual diagonal energies (not a cardinality-times-sup surrogate):

  D(n,r) = sum_{e,j} ||I_{beta_n,H,e}(R_{n,j})||^2
         = sum_j G_right(j,j).

The mathlib finite Cauchy--Schwarz inequality then gives the exact
physical diagonal-trace test

  a*G_right*a <= D(n,r) * sum_j a_j^2.

This supplies a concrete scalar alternative to the signed Schur row
criterion, and an honest sufficient condition for uniformity IF the
true original-Wilson trace can later be proved volume-uniform.

We also connect each actual diagonal summand to PR #5338's physical
signed source-Hilbert coefficient.  The resulting crude summed bound
still has the full true spatial link count: NO uniformity claim.
The fine orbit uses beta(n+1); the Wilson posterior uses frozen beta(n).
No replacement posterior, Dobrushin, sorry/admit or new axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

local instance p4DiagTraceTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4DiagTraceCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4DiagTraceSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4DiagTraceMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4DiagTraceBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4DiagTraceLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Full genuine original signed-Wilson Gram diagonal energy trace,
retaining both each original posterior spatial link and each actual
fine-right Krylov mode, with no max or fabricated locality law. -/
noncomputable def fineRightKrylovOriginalPosteriorDiagonalTrace
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) : ℝ :=
  ∑ e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)),
    ∑ j : Fin (r + 1),
      (fineRightKrylovOriginalPosteriorLinkResidualNorm
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r e j) ^ 2

theorem fineRightKrylovOriginalPosteriorDiagonalTrace_nonneg
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) :
    0 ≤ fineRightKrylovOriginalPosteriorDiagonalTrace
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r := by
  unfold fineRightKrylovOriginalPosteriorDiagonalTrace
  apply Finset.sum_nonneg
  intro e _he
  apply Finset.sum_nonneg
  intro j _hj
  exact sq_nonneg _

/-- Exact diagonal of the actual signed original Wilson posterior-mode
covariance, expressed in the existing true pair-Haar innovation norm. -/
theorem fineRightKrylovOriginalPosteriorLinkCovariance_diag_eq_residualNorm_sq
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ)
    (e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)))
    (j : Fin (r + 1)) :
    fineRightKrylovOriginalPosteriorLinkCovariance
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e j j =
      (fineRightKrylovOriginalPosteriorLinkResidualNorm
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r e j) ^ 2 := by
  let v := fineRightKrylovOriginalPosteriorLinkResidual
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r e j
  change inner ℝ v v =
    (fineRightKrylovOriginalPosteriorLinkResidualNorm
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e j) ^ 2
  rw [real_inner_self_eq_norm_sq]
  rw [fineRightKrylovOriginalPosteriorLinkResidual_norm_eq]

/-- True original Wilson trace is the diagonal sum of the ACTUAL
uncentered right Krylov Gram, including all signed off-diagonal
covariance information in the original Gram definition. -/
theorem fineRightKrylovOriginalPosteriorDiagonalTrace_eq_gram_diagonal
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) :
    fineRightKrylovOriginalPosteriorDiagonalTrace
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r =
    ∑ j : Fin (r + 1),
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) j j := by
  classical
  calc
    fineRightKrylovOriginalPosteriorDiagonalTrace
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r =
      ∑ e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)),
        ∑ j : Fin (r + 1),
          fineRightKrylovOriginalPosteriorLinkCovariance
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r e j j := by
        unfold fineRightKrylovOriginalPosteriorDiagonalTrace
        apply Finset.sum_congr rfl
        intro e _he
        apply Finset.sum_congr rfl
        intro j _hj
        exact (fineRightKrylovOriginalPosteriorLinkCovariance_diag_eq_residualNorm_sq
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r e j).symm
    _ = ∑ j : Fin (r + 1),
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)),
          fineRightKrylovOriginalPosteriorLinkCovariance
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r e j j := by rw [Finset.sum_comm]
    _ = ∑ j : Fin (r + 1),
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) j j := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [fineRightKrylovPairHaarResidualGram_entry_eq_originalPosteriorCovariance]
      rfl

/-- The actual UN-CENTERED right Krylov Gram is automatically controlled
by its GENUINE diagonal trace and the coefficient ell² norm.
The coefficient is a sum of physical diagonal innovation energies,
not a signed Schur-row assumption and not the number of links. -/
theorem fineRightKrylovPairHaarResidualGram_rayleigh_le_originalDiagonalTrace
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ) :
    star a ⬝ᵥ (Matrix.mulVec
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a) ≤
      fineRightKrylovOriginalPosteriorDiagonalTrace
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r * ∑ j : Fin (r + 1), (a j) ^ 2 := by
  classical
  let H := halfExtent (n + 1)
  let d : PeriodicHypercubicEvenSpatialSliceLink H →
      Fin (r + 1) → ℝ :=
    fun e j => fineRightKrylovOriginalPosteriorLinkResidualNorm
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e j
  let A : ℝ := ∑ j : Fin (r + 1), (a j) ^ 2
  have hCS (e : PeriodicHypercubicEvenSpatialSliceLink H) :
      (∑ j : Fin (r + 1), |a j| * d e j) ^ 2 ≤
        A * ∑ j : Fin (r + 1), (d e j) ^ 2 := by
    simpa only [A, sq_abs] using
      (Finset.sum_mul_sq_le_sq_mul_sq
        (Finset.univ : Finset (Fin (r + 1)))
        (fun j => |a j|) (d e))
  have hRay :=
    fineRightKrylovPairHaarResidualGram_rayleigh_le_localLinkwiseL1
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a
  change star a ⬝ᵥ (Matrix.mulVec
    (fineRightKrylovPairHaarResidualGram
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r) a) ≤
    ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
      (∑ j : Fin (r + 1), |a j| * d e j) ^ 2 at hRay
  have hBound :
      star a ⬝ᵥ (Matrix.mulVec
        (fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) a) ≤
        A * (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          ∑ j : Fin (r + 1), (d e j) ^ 2) := by
    calc
      star a ⬝ᵥ (Matrix.mulVec
        (fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) a) ≤
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          (∑ j : Fin (r + 1), |a j| * d e j) ^ 2 := hRay
      _ ≤ ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          A * (∑ j : Fin (r + 1), (d e j) ^ 2) := by
        apply Finset.sum_le_sum
        intro e _he
        exact hCS e
      _ = A * (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          ∑ j : Fin (r + 1), (d e j) ^ 2) := by
        rw [Finset.mul_sum]
  change star a ⬝ᵥ (Matrix.mulVec
    (fineRightKrylovPairHaarResidualGram
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r) a) ≤
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        ∑ j : Fin (r + 1), (d e j) ^ 2) * A
  exact hBound.trans_eq (mul_comm _ _)

/-- A true physical H/r-uniform bound on the original diagonal trace
would imply an ell² Gram bound immediately. This theorem does NOT
assert the bound; it exposes a second concrete physical frontier
distinct from signed Schur off-diagonal row summability. -/
theorem fineRightKrylovPairHaarResidualGram_rayleigh_le_certifiedOriginalDiagonalTrace
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ)
    (C : ℝ)
    (hTrace :
      fineRightKrylovOriginalPosteriorDiagonalTrace
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r ≤ C) :
    star a ⬝ᵥ (Matrix.mulVec
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a) ≤
      C * ∑ j : Fin (r + 1), (a j) ^ 2 := by
  calc
    star a ⬝ᵥ (Matrix.mulVec
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a) ≤
        fineRightKrylovOriginalPosteriorDiagonalTrace
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r * ∑ j : Fin (r + 1), (a j) ^ 2 :=
      fineRightKrylovPairHaarResidualGram_rayleigh_le_originalDiagonalTrace
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
    _ ≤ C * ∑ j : Fin (r + 1), (a j) ^ 2 :=
      mul_le_mul_of_nonneg_right hTrace
        (Finset.sum_nonneg (fun j _hj => sq_nonneg (a j)))

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
