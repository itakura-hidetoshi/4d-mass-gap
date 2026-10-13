import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSignedFineFrozenModeCovarianceSchurEnvelope
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# P4-Q2-EZ: genuine original Wilson signed mode Gram Cauchy and diagonal trace

For the *actual* original frozen Wilson posterior, retain the true fine
signed physical right-Krylov mode residuals I_e(i) and the signed
link-summed covariance G(i,j) = sum_e inner(I_e(i), I_e(j)).

The diagonal is an EXACT sum of original physical residual squares.
Finite Cauchy--Schwarz on the actual link set then proves

    G(i,j)^2 <= G(i,i) * G(j,j).

This is unconditional in the coupling and keeps link signs until the
absolute-value estimate, not a hypothetical spatial independence bound.
Zero physical diagonal energy consequently forces the full corresponding
signed covariance row to vanish.

The previous EY true small-beta estimates control the actual diagonal
trace by 3072*(H+1)^3*beta(n)^2 * sum_i F_i^2. This has no explicit
extra factor r+1 outside the *actual* mode sum, but does NOT prove
H/r/n-uniform physical norm or signed cancellation, cross-scale
C1/C2/C3, or continuum H2/H3/H4. Dobrushin is not used.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 900000

private noncomputable instance p4Q2EZ_originalSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Exact diagonal of the TRUE original Wilson signed mode covariance:
the sum of the genuine link-residual Hilbert norm squares. -/
theorem p4Q2EZ_originalModeCovariance_diag_eq_linkResidualNormSq
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (i : Fin (r + 1)) :
    fineRightKrylovOriginalPosteriorModeCovariance
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r i i =
    ∑ e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)),
      ‖fineRightKrylovOriginalPosteriorLinkResidual
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r e i‖ ^ 2 := by
  classical
  unfold fineRightKrylovOriginalPosteriorModeCovariance
  apply Finset.sum_congr rfl
  intro e _he
  unfold fineRightKrylovOriginalPosteriorLinkCovariance
  exact real_inner_self_eq_norm_sq _

/-- The original-Wilson signed mode diagonal is nonnegative even though
off-diagonal physical covariances can have either sign. -/
theorem p4Q2EZ_originalModeCovariance_diag_nonneg
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (i : Fin (r + 1)) :
    0 ≤ fineRightKrylovOriginalPosteriorModeCovariance
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r i i := by
  classical
  rw [p4Q2EZ_originalModeCovariance_diag_eq_linkResidualNormSq]
  exact Finset.sum_nonneg (fun e _ => sq_nonneg _)

/-- Gram Cauchy--Schwarz for the EXACT original Wilson signed link sum.
There is no beta-smallness or spatial mixing assumption and no absolute
value taken inside the definition of the original covariance. -/
theorem p4Q2EZ_originalModeCovariance_sq_le_diag_mul
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (i j : Fin (r + 1)) :
    (fineRightKrylovOriginalPosteriorModeCovariance
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r i j) ^ 2 ≤
    fineRightKrylovOriginalPosteriorModeCovariance
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r i i *
    fineRightKrylovOriginalPosteriorModeCovariance
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r j j := by
  classical
  let H := halfExtent (n + 1)
  let v (e : PeriodicHypercubicEvenSpatialSliceLink H)
      (k : Fin (r + 1)) :=
    fineRightKrylovOriginalPosteriorLinkResidual
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e k
  let K (e : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
    inner ℝ (v e i) (v e j)
  have hAbs :
      |∑ e : PeriodicHypercubicEvenSpatialSliceLink H, K e| ≤
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          ‖v e i‖ * ‖v e j‖ := by
    calc
      |∑ e : PeriodicHypercubicEvenSpatialSliceLink H, K e| ≤
          ∑ e : PeriodicHypercubicEvenSpatialSliceLink H, |K e| :=
        Finset.abs_sum_le_sum_abs K Finset.univ
      _ ≤ ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          ‖v e i‖ * ‖v e j‖ := by
        apply Finset.sum_le_sum
        intro e _he
        exact abs_real_inner_le_norm (v e i) (v e j)
  have hSq :
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          ‖v e i‖ * ‖v e j‖) ^ 2 ≤
        (∑ e : PeriodicHypercubicEvenSpatialSliceLink H, ‖v e i‖ ^ 2) *
        (∑ e : PeriodicHypercubicEvenSpatialSliceLink H, ‖v e j‖ ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun e : PeriodicHypercubicEvenSpatialSliceLink H => ‖v e i‖)
      (fun e : PeriodicHypercubicEvenSpatialSliceLink H => ‖v e j‖)
  have hAbsSq :
      |∑ e : PeriodicHypercubicEvenSpatialSliceLink H, K e| ^ 2 ≤
        (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          ‖v e i‖ * ‖v e j‖) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) hAbs 2
  rw [p4Q2EZ_originalModeCovariance_diag_eq_linkResidualNormSq
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r i,
      p4Q2EZ_originalModeCovariance_diag_eq_linkResidualNormSq
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r j]
  change
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H, K e) ^ 2 ≤
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H, ‖v e i‖ ^ 2) *
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H, ‖v e j‖ ^ 2)
  calc
    (∑ e : PeriodicHypercubicEvenSpatialSliceLink H, K e) ^ 2 =
        |∑ e : PeriodicHypercubicEvenSpatialSliceLink H, K e| ^ 2 :=
      (sq_abs _).symm
    _ ≤ (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          ‖v e i‖ * ‖v e j‖) ^ 2 := hAbsSq
    _ ≤ (∑ e : PeriodicHypercubicEvenSpatialSliceLink H, ‖v e i‖ ^ 2) *
        (∑ e : PeriodicHypercubicEvenSpatialSliceLink H, ‖v e j‖ ^ 2) := hSq

/-- Genuine zero-energy modes decouple from every signed covariance
entry, without an additional probabilistic or physical hypothesis. -/
theorem p4Q2EZ_originalModeCovariance_zero_row_of_zero_diag
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (i : Fin (r + 1))
    (hZero : fineRightKrylovOriginalPosteriorModeCovariance
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r i i = 0)
    (j : Fin (r + 1)) :
    fineRightKrylovOriginalPosteriorModeCovariance
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r i j = 0 := by
  have hSq := p4Q2EZ_originalModeCovariance_sq_le_diag_mul
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r i j
  rw [hZero] at hSq
  simp only [zero_mul] at hSq
  nlinarith [sq_nonneg
    (fineRightKrylovOriginalPosteriorModeCovariance
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r i j)]

/-- The small-beta ORIGINAL Wilson diagonal energy retains the exact
physical signed source/vacuum factor and cubic volume; no rank loss. -/
theorem p4Q2EZ_originalModeCovariance_diag_le_smallBeta
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (i : Fin (r + 1))
    (hSmall : beta n ≤ (1 : ℝ) / 8) :
    fineRightKrylovOriginalPosteriorModeCovariance
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r i i ≤
    3072 * (halfExtent (n + 1) + 1 : ℝ) ^ 3 * (beta n) ^ 2 *
      (p4Q2EY_originalWilsonRightModeNormFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r i) ^ 2 := by
  let G := fineRightKrylovOriginalPosteriorModeCovariance
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r i i
  let F := p4Q2EY_originalWilsonRightModeNormFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r i
  have hEY := p4Q2EY_originalModeCovariance_abs_le_cubicSmallBeta
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r i i hSmall
  calc
    G ≤ |G| := le_abs_self _
    _ ≤ 1536 * (halfExtent (n + 1) + 1 : ℝ) ^ 3 *
          (beta n) ^ 2 * (F ^ 2 + F ^ 2) := hEY
    _ = 3072 * (halfExtent (n + 1) + 1 : ℝ) ^ 3 *
          (beta n) ^ 2 * F ^ 2 := by ring

/-- A rank-explicit TRUE modal trace (rather than naive covariance
Schur row multiplicity) with only the actual sum of physical mode norms.
Neither that sum nor the spatial volume is claimed uniformly bounded. -/
theorem p4Q2EZ_originalModeCovariance_trace_le_smallBeta
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (hSmall : beta n ≤ (1 : ℝ) / 8) :
    (∑ i : Fin (r + 1),
      fineRightKrylovOriginalPosteriorModeCovariance
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r i i) ≤
    3072 * (halfExtent (n + 1) + 1 : ℝ) ^ 3 * (beta n) ^ 2 *
      (∑ i : Fin (r + 1),
        (p4Q2EY_originalWilsonRightModeNormFactor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r i) ^ 2) := by
  classical
  let C : ℝ := 3072 * (halfExtent (n + 1) + 1 : ℝ) ^ 3 * (beta n) ^ 2
  let F (i : Fin (r + 1)) : ℝ :=
    p4Q2EY_originalWilsonRightModeNormFactor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r i
  calc
    (∑ i : Fin (r + 1),
        fineRightKrylovOriginalPosteriorModeCovariance
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r i i) ≤ ∑ i : Fin (r + 1), C * F i ^ 2 := by
      apply Finset.sum_le_sum
      intro i _hi
      exact p4Q2EZ_originalModeCovariance_diag_le_smallBeta
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r i hSmall
    _ = C * (∑ i : Fin (r + 1), F i ^ 2) := by
      rw [Finset.mul_sum]


/-- Sharpen EY's sum-of-squares covariance entry envelope to a
multiplicative *physical* mode-norm envelope by the authentic signed
Gram Cauchy--Schwarz inequality. The finite cubic volume remains. -/
theorem p4Q2EZ_originalModeCovariance_abs_le_geometricSmallBeta
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (i j : Fin (r + 1))
    (hSmall : beta n ≤ (1 : ℝ) / 8) :
    |fineRightKrylovOriginalPosteriorModeCovariance
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r i j| ≤
    3072 * (halfExtent (n + 1) + 1 : ℝ) ^ 3 * (beta n) ^ 2 *
      (p4Q2EY_originalWilsonRightModeNormFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r i) *
      (p4Q2EY_originalWilsonRightModeNormFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r j) := by
  let G (a b : Fin (r + 1)) : ℝ :=
    fineRightKrylovOriginalPosteriorModeCovariance
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a b
  let F (a : Fin (r + 1)) : ℝ :=
    p4Q2EY_originalWilsonRightModeNormFactor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  let C : ℝ :=
    3072 * (halfExtent (n + 1) + 1 : ℝ) ^ 3 * (beta n) ^ 2
  have hFi : 0 ≤ F i :=
    fineRightKrylovOriginalSignedSourceVacuumFactor_nonneg
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r (p4Q2EY_originalRightModeBasis r i)
  have hFj : 0 ≤ F j :=
    fineRightKrylovOriginalSignedSourceVacuumFactor_nonneg
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r (p4Q2EY_originalRightModeBasis r j)
  have hDiagI : G i i ≤ C * F i ^ 2 :=
    p4Q2EZ_originalModeCovariance_diag_le_smallBeta
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r i hSmall
  have hDiagJ : G j j ≤ C * F j ^ 2 :=
    p4Q2EZ_originalModeCovariance_diag_le_smallBeta
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r j hSmall
  have hDiagJNonneg : 0 ≤ G j j :=
    p4Q2EZ_originalModeCovariance_diag_nonneg
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r j
  have hProduct :
      G i i * G j j ≤ (C * F i ^ 2) * (C * F j ^ 2) :=
    mul_le_mul hDiagI hDiagJ hDiagJNonneg (by positivity)
  have hGram : (G i j) ^ 2 ≤ G i i * G j j :=
    p4Q2EZ_originalModeCovariance_sq_le_diag_mul
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r i j
  have hSquare : |G i j| ^ 2 ≤ (C * F i * F j) ^ 2 := by
    calc
      |G i j| ^ 2 = (G i j) ^ 2 := sq_abs _
      _ ≤ G i i * G j j := hGram
      _ ≤ (C * F i ^ 2) * (C * F j ^ 2) := hProduct
      _ = (C * F i * F j) ^ 2 := by ring
  exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp hSquare

/-- Genuine signed Schur row with the GEOMETRIC physical mode factors:
the explicit extra (r+1)*F_i^2 from EY's arithmetic-mean row estimate
is replaced by the actual l1 sum of the positive mode norm factors.
This still does not certify the sum or spatial volume uniformly. -/
theorem p4Q2EZ_originalSignedModeCovariance_absRow_le_geometricSmallBeta
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (i : Fin (r + 1))
    (hSmall : beta n ≤ (1 : ℝ) / 8) :
    (∑ j : Fin (r + 1),
      |fineRightKrylovOriginalPosteriorModeCovariance
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r i j|) ≤
    3072 * (halfExtent (n + 1) + 1 : ℝ) ^ 3 * (beta n) ^ 2 *
      (p4Q2EY_originalWilsonRightModeNormFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r i) *
      (∑ j : Fin (r + 1),
        p4Q2EY_originalWilsonRightModeNormFactor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r j) := by
  classical
  let C : ℝ := 3072 * (halfExtent (n + 1) + 1 : ℝ) ^ 3 * (beta n) ^ 2
  let F (j : Fin (r + 1)) : ℝ :=
    p4Q2EY_originalWilsonRightModeNormFactor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r j
  calc
    (∑ j : Fin (r + 1),
      |fineRightKrylovOriginalPosteriorModeCovariance
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r i j|) ≤
      ∑ j : Fin (r + 1), (C * F i) * F j := by
        apply Finset.sum_le_sum
        intro j _hj
        exact p4Q2EZ_originalModeCovariance_abs_le_geometricSmallBeta
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r i j hSmall
    _ = (C * F i) * (∑ j : Fin (r + 1), F j) := by
      rw [Finset.mul_sum]

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2EZ_originalModeCovariance_diag_eq_linkResidualNormSq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2EZ_originalModeCovariance_diag_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2EZ_originalModeCovariance_sq_le_diag_mul
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2EZ_originalModeCovariance_zero_row_of_zero_diag
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2EZ_originalModeCovariance_diag_le_smallBeta
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2EZ_originalModeCovariance_trace_le_smallBeta

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2EZ_originalModeCovariance_abs_le_geometricSmallBeta
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2EZ_originalSignedModeCovariance_absRow_le_geometricSmallBeta
