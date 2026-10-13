import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSignedFineFrozenPositiveBetaLinkwiseCovariance
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarUncenteredPosteriorCovarianceSchur
import Mathlib.Tactic

/-!
# P4-Q2-EY: exact original Wilson signed fine/frozen Krylov mode covariance

EX controls, for arbitrary genuine SIGNED fine-right coefficient inputs
a and b, the original frozen-beta Wilson posterior right-link residual
cross inner product BEFORE summing true spatial links.

Here use genuine standard unit coefficient vectors, not substitute mode
carriers, to specialize those estimates to the EXISTING original-Wilson
signed physical link covariance of PR #5321. The true signed mode-pair
covariance is the full original physical link sum, preserving signs
until the final triangle inequality.

Under the actual frozen beta(n) <= 1/8 we obtain finite-volume
bounds on the real signed K_e(i,j) and its full original mode covariance,
and a quantitative signed covariance Schur row upper envelope.
The precise volume factor is the genuine count 24*(H+1)^3
proved by EU, and mode/horizon multiplicity is NOT hidden.

These explicit naive physical norm/volume bounds are not H/r/n-uniform
or a substitute for genuine signed covariance decay/cancellation.
No independent pair-Haar resampling, Dobrushin, original AW/D12
relative comparison or Yang-Mills continuum mass gap is claimed.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 900000

private noncomputable instance p4Q2EY_originalSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Actual standard basis coefficient vector in the EXISTING
finite uncentered right-Krylov mode carrier Fin(r+1). -/
noncomputable def p4Q2EY_originalRightModeBasis
    (r : ℕ) (i : Fin (r + 1)) : Fin (r + 1) → ℝ :=
  fun j => if j = i then 1 else 0

/-- An original physical source/vacuum norm for one ACTUAL
fine-right Krylov mode, not a generic fitted covariance parameter. -/
noncomputable def p4Q2EY_originalWilsonRightModeNormFactor
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (i : Fin (r + 1)) : ℝ :=
  fineRightKrylovOriginalSignedSourceVacuumFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r (p4Q2EY_originalRightModeBasis r i)

/-- The true original-Wilson signed combination receiver with
coefficient e_i is DEFINITIONALLY the existing original uncentered
frozen-Wilson posterior Krylov mode innovation at physical link e. -/
theorem p4Q2EY_originalModeResidual_eq_signedBasisCombination
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)))
    (i : Fin (r + 1)) :
    fineRightKrylovOriginalWilsonSignedCombinationResidual
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r (p4Q2EY_originalRightModeBasis r i) e =
    fineRightKrylovOriginalPosteriorLinkResidual
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e i := by
  classical
  unfold fineRightKrylovOriginalWilsonSignedCombinationResidual
    fineRightKrylovOriginalPosteriorLinkResidual
    p4Q2EY_originalRightModeBasis
  simp

/-- Every genuine original Wilson frozen RIGHT-link mode residual
satisfies the new small-frozen-beta bound from EX, with the actual
signed individual fine-mode source/vacuum factor. -/
theorem p4Q2EY_originalModeLinkResidual_norm_sq_le_smallBeta
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ)
    (e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)))
    (i : Fin (r + 1))
    (hSmall : beta n ≤ (1 : ℝ) / 8) :
    ‖fineRightKrylovOriginalPosteriorLinkResidual
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e i‖ ^ 2 ≤
      128 * (beta n) ^ 2 *
        (p4Q2EY_originalWilsonRightModeNormFactor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r i) ^ 2 := by
  have h :=
    fineRightKrylovOriginalWilsonSignedCombinationResidual_norm_sq_le_smallBetaSource
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r (p4Q2EY_originalRightModeBasis r i) e hSmall
  rw [p4Q2EY_originalModeResidual_eq_signedBasisCombination] at h
  exact h

/-- Genuine SIGNED original Wilson mode-pair cross-covariance on
EVERY actual right link, from EX's actual Wilson signed-combination
Cauchy-Schwarz. No positivity assertion for the cross term. -/
theorem p4Q2EY_originalLinkModeCovariance_abs_le_smallBeta
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ)
    (e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)))
    (i j : Fin (r + 1))
    (hSmall : beta n ≤ (1 : ℝ) / 8) :
    |fineRightKrylovOriginalPosteriorLinkCovariance
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e i j| ≤
      64 * (beta n) ^ 2 *
        ((p4Q2EY_originalWilsonRightModeNormFactor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r i) ^ 2 +
         (p4Q2EY_originalWilsonRightModeNormFactor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r j) ^ 2) := by
  have h :=
    fineRightKrylovOriginalWilsonSignedCombinationResidual_inner_abs_le_smallBeta
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r (p4Q2EY_originalRightModeBasis r i)
      (p4Q2EY_originalRightModeBasis r j) e hSmall
  rw [p4Q2EY_originalModeResidual_eq_signedBasisCombination,
      p4Q2EY_originalModeResidual_eq_signedBasisCombination] at h
  exact h

/-- Genuine original Wilson SIGNED covariance sum over all actual
physical spatial right links, preserving each signed link contribution
until the final absolute-value triangle bound. The explicit cubic
spatial-volume factor is from EU's proved physical link count,
not an assumed H-uniform correlation decay. -/
theorem p4Q2EY_originalModeCovariance_abs_le_cubicSmallBeta
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (i j : Fin (r + 1))
    (hSmall : beta n ≤ (1 : ℝ) / 8) :
    |fineRightKrylovOriginalPosteriorModeCovariance
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r i j| ≤
      1536 * (halfExtent (n + 1) + 1 : ℝ) ^ 3 *
        (beta n) ^ 2 *
        ((p4Q2EY_originalWilsonRightModeNormFactor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r i) ^ 2 +
         (p4Q2EY_originalWilsonRightModeNormFactor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r j) ^ 2) := by
  classical
  let H := halfExtent (n + 1)
  let K (e : PeriodicHypercubicEvenSpatialSliceLink H) :=
    fineRightKrylovOriginalPosteriorLinkCovariance
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e i j
  let A := p4Q2EY_originalWilsonRightModeNormFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r i
  let B := p4Q2EY_originalWilsonRightModeNormFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r j
  have hAbs :
      |∑ e : PeriodicHypercubicEvenSpatialSliceLink H, K e| ≤
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H, |K e| :=
    Finset.abs_sum_le_sum_abs K Finset.univ
  have hEach (e : PeriodicHypercubicEvenSpatialSliceLink H) :
      |K e| ≤ 64 * (beta n) ^ 2 * (A ^ 2 + B ^ 2) :=
    p4Q2EY_originalLinkModeCovariance_abs_le_smallBeta
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r e i j hSmall
  have hTotal :
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H, |K e|) ≤
        ∑ _e : PeriodicHypercubicEvenSpatialSliceLink H,
          64 * (beta n) ^ 2 * (A ^ 2 + B ^ 2) :=
    Finset.sum_le_sum (fun e _ => hEach e)
  have hCard := p4Q2EU_originalPhysicalSpatialLinks_card_exact H
  calc
    |fineRightKrylovOriginalPosteriorModeCovariance
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r i j| =
        |∑ e : PeriodicHypercubicEvenSpatialSliceLink H, K e| := rfl
    _ ≤ ∑ e : PeriodicHypercubicEvenSpatialSliceLink H, |K e| := hAbs
    _ ≤ ∑ _e : PeriodicHypercubicEvenSpatialSliceLink H,
        64 * (beta n) ^ 2 * (A ^ 2 + B ^ 2) := hTotal
    _ = (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
        (64 * (beta n) ^ 2 * (A ^ 2 + B ^ 2)) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = 1536 * (H + 1 : ℝ) ^ 3 * (beta n) ^ 2 *
        (A ^ 2 + B ^ 2) := by
          rw [hCard]
          push_cast
          ring

/-- Original signed mode covariance SCHUR-ROW finite-volume envelope.
No signed cancellations are discarded UNTIL the absolute-value
Schur majorant is explicitly requested. All mode factors are ACTUAL
EU/EX frozen Wilson W/vacuum/signed fine source norms; a growing
spatial volume or growing Krylov horizon remains visible. -/
theorem p4Q2EY_originalSignedModeCovariance_absRow_le_cubicSmallBeta
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (i : Fin (r + 1))
    (hSmall : beta n ≤ (1 : ℝ) / 8) :
    (∑ j : Fin (r + 1),
      |fineRightKrylovOriginalPosteriorModeCovariance
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r i j|) ≤
      1536 * (halfExtent (n + 1) + 1 : ℝ) ^ 3 *
        (beta n) ^ 2 *
        (((r + 1 : ℕ) : ℝ) *
          (p4Q2EY_originalWilsonRightModeNormFactor
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r i) ^ 2 +
         ∑ j : Fin (r + 1),
           (p4Q2EY_originalWilsonRightModeNormFactor
             (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
             n r j) ^ 2) := by
  classical
  let C : ℝ := 1536 * (halfExtent (n + 1) + 1 : ℝ) ^ 3 * (beta n) ^ 2
  let T (j : Fin (r + 1)) : ℝ :=
    p4Q2EY_originalWilsonRightModeNormFactor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r j
  have hRow :
      (∑ j : Fin (r + 1),
        |fineRightKrylovOriginalPosteriorModeCovariance
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r i j|) ≤
        ∑ j : Fin (r + 1), C * (T i ^ 2 + T j ^ 2) := by
    apply Finset.sum_le_sum
    intro j _hj
    exact p4Q2EY_originalModeCovariance_abs_le_cubicSmallBeta
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r i j hSmall
  have hSum :
      (∑ j : Fin (r + 1), C * (T i ^ 2 + T j ^ 2)) =
        C * (((r + 1 : ℕ) : ℝ) * T i ^ 2 +
          ∑ j : Fin (r + 1), T j ^ 2) := by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [nsmul_eq_mul]
    ring
  exact hRow.trans_eq hSum

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2EY_originalModeResidual_eq_signedBasisCombination
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2EY_originalModeLinkResidual_norm_sq_le_smallBeta
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2EY_originalLinkModeCovariance_abs_le_smallBeta
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2EY_originalModeCovariance_abs_le_cubicSmallBeta
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2EY_originalSignedModeCovariance_absRow_le_cubicSmallBeta
