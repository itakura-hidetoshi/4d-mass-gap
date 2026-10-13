import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSignedFineFrozenGramCauchyTraceV5_EZ
import Mathlib.Tactic

/-!
# P4-Q2-FA: original Wilson posterior Gram trace controls Rayleigh without Schur l1 loss

EZ establishes the authentic original-Wilson signed fine/frozen right-Krylov
mode covariance G(i,j), its exact physical residual diagonal, and the
finite-H small-frozen-beta physical trace estimate.

The existing genuine original-posterior LINKWISE Rayleigh-L1 inequality
retains each link's signed mode innovations. Apply the pinned mathlib
finite Cauchy-Schwarz inequality within each physical link BEFORE any
volume or mode summation. Then exchange the genuine finite sums and use
the EZ exact physical diagonal/trace identity:

    a*G a <= (sum_i G(i,i)) * (sum_i a_i^2).

This true positive Gram trace estimate has no added explicit r+1 factor
and no sum_i F_i coefficient-l1 Schur gate. Combining with EZ:

    a*G a <= 3072*(H+1)^3*beta(n)^2 * (sum_i F_i^2) * (sum_i a_i^2)

for genuine frozen 0 <= beta(n) <= 1/8. Here each F_i is precisely the
original physical Wilson half-density, signed source, transfer and vacuum
norm factor. No H/r/n-uniform control of the TRACE factor is asserted.

A conditional scalar trace-trajectory certificate is isolated, but not
postulated or inferred. Cross-scale C1/C2/C3, physical H2/H3/H4 and
four-dimensional Yang-Mills positive mass gap remain OPEN.
No independent Haar posterior, artificial marginal, Dobrushin, axioms,
sorry or admit.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 900000

private noncomputable instance p4Q2FA_originalSpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Exact exchange of the physical LINK sum and the genuine original
Wilson signed MODE covariance trace, before any inequality. -/
theorem p4Q2FA_originalModeCovariance_trace_eq_sum_linkNormSq
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) :
    (∑ i : Fin (r + 1),
      fineRightKrylovOriginalPosteriorModeCovariance
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r i i) =
    ∑ e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)),
      ∑ i : Fin (r + 1),
        ‖fineRightKrylovOriginalPosteriorLinkResidual
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r e i‖ ^ 2 := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  exact p4Q2EZ_originalModeCovariance_diag_eq_linkResidualNormSq
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r i

/-- Unconditional original Wilson signed Gram trace Rayleigh bound.
Use each genuine physical link residual and Cauchy--Schwarz across
actual Krylov coefficient modes, then sum the EXACT physical links.
No mode-count factor or replacing Wilson posterior with pair-Haar law. -/
theorem p4Q2FA_originalSignedGram_rayleigh_le_actualPhysicalTrace
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ) :
    star a ⬝ᵥ (Matrix.mulVec
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a) ≤
    (∑ i : Fin (r + 1),
      fineRightKrylovOriginalPosteriorModeCovariance
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r i i) *
    (∑ j : Fin (r + 1), (a j) ^ 2) := by
  classical
  let H := halfExtent (n + 1)
  let d (e : PeriodicHypercubicEvenSpatialSliceLink H) (j : Fin (r + 1)) : ℝ :=
    fineRightKrylovOriginalPosteriorLinkResidualNorm
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r e j
  let A : ℝ := ∑ j : Fin (r + 1), (a j) ^ 2
  let T : ℝ := ∑ i : Fin (r + 1),
    fineRightKrylovOriginalPosteriorModeCovariance
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r i i
  have hLocal :
      star a ⬝ᵥ (Matrix.mulVec
        (fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) a) ≤
      ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
        (∑ j : Fin (r + 1), |a j| * d e j) ^ 2 := by
    exact fineRightKrylovPairHaarResidualGram_rayleigh_le_localLinkwiseL1
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a
  have hEach (e : PeriodicHypercubicEvenSpatialSliceLink H) :
      (∑ j : Fin (r + 1), |a j| * d e j) ^ 2 ≤
        A * (∑ j : Fin (r + 1), (d e j) ^ 2) := by
    simpa only [A, sq_abs] using
      (Finset.sum_mul_sq_le_sq_mul_sq
        (Finset.univ : Finset (Fin (r + 1)))
        (fun j => |a j|) (fun j => d e j))
  have hTrace :
      (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          ∑ j : Fin (r + 1), (d e j) ^ 2) = T := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [p4Q2EZ_originalModeCovariance_diag_eq_linkResidualNormSq]
    apply Finset.sum_congr rfl
    intro e _he
    exact congrArg (fun x : ℝ => x ^ 2)
      ((fineRightKrylovOriginalPosteriorLinkResidual_norm_eq
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r e j).symm)
  calc
    star a ⬝ᵥ (Matrix.mulVec
        (fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) a) ≤
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          (∑ j : Fin (r + 1), |a j| * d e j) ^ 2 := hLocal
    _ ≤ ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          A * (∑ j : Fin (r + 1), (d e j) ^ 2) := by
            apply Finset.sum_le_sum
            intro e _he
            exact hEach e
    _ = A * (∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          ∑ j : Fin (r + 1), (d e j) ^ 2) := by
            rw [Finset.mul_sum]
    _ = A * T := by rw [hTrace]
    _ = T * A := mul_comm _ _

/-- True physical posterior small-coupling RAYLEIGH inequality with no
l1-mode Schur loss: rank enters only through the actual Wilson L2-like
modal physical TRACE factor, with finite volume still explicit. -/
theorem p4Q2FA_originalSignedGram_rayleigh_le_smallBetaTrace
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ)
    (hSmall : beta n ≤ (1 : ℝ) / 8) :
    star a ⬝ᵥ (Matrix.mulVec
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a) ≤
    (3072 * (halfExtent (n + 1) + 1 : ℝ) ^ 3 * (beta n) ^ 2 *
      (∑ i : Fin (r + 1),
        (p4Q2EY_originalWilsonRightModeNormFactor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r i) ^ 2)) *
      (∑ j : Fin (r + 1), (a j) ^ 2) := by
  have hRay :=
    p4Q2FA_originalSignedGram_rayleigh_le_actualPhysicalTrace
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  have hTrace :=
    p4Q2EZ_originalModeCovariance_trace_le_smallBeta
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r hSmall
  have hCoeff : 0 ≤ ∑ j : Fin (r + 1), (a j) ^ 2 :=
    Finset.sum_nonneg (fun j _hj => sq_nonneg (a j))
  exact hRay.trans (mul_le_mul_of_nonneg_right hTrace hCoeff)

/-- A single scalar certificate on the actual physical mode TRACE would
suffice to remove both H and r from the real Rayleigh bound. This is
CONDITIONAL; no such original-Wilson trace trajectory is established. -/
theorem p4Q2FA_originalSignedGram_rayleigh_le_certifiedTrace
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ) (K : ℝ)
    (hSmall : beta n ≤ (1 : ℝ) / 8)
    (hTrace :
      (halfExtent (n + 1) + 1 : ℝ) ^ 3 * (beta n) ^ 2 *
        (∑ i : Fin (r + 1),
          (p4Q2EY_originalWilsonRightModeNormFactor
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r i) ^ 2) ≤ K) :
    star a ⬝ᵥ (Matrix.mulVec
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a) ≤
      (3072 * K) * (∑ j : Fin (r + 1), (a j) ^ 2) := by
  have hRay :=
    p4Q2FA_originalSignedGram_rayleigh_le_smallBetaTrace
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a hSmall
  have hScale :
      3072 * (halfExtent (n + 1) + 1 : ℝ) ^ 3 * (beta n) ^ 2 *
        (∑ i : Fin (r + 1),
          (p4Q2EY_originalWilsonRightModeNormFactor
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r i) ^ 2) ≤ 3072 * K := by
    calc
      3072 * (halfExtent (n + 1) + 1 : ℝ) ^ 3 * (beta n) ^ 2 *
          (∑ i : Fin (r + 1),
            (p4Q2EY_originalWilsonRightModeNormFactor
              (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
              n r i) ^ 2) =
        3072 * ((halfExtent (n + 1) + 1 : ℝ) ^ 3 * (beta n) ^ 2 *
          (∑ i : Fin (r + 1),
            (p4Q2EY_originalWilsonRightModeNormFactor
              (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
              n r i) ^ 2)) := by ring
      _ ≤ 3072 * K :=
        mul_le_mul_of_nonneg_left hTrace (by norm_num)
  have hCoeff : 0 ≤ ∑ j : Fin (r + 1), (a j) ^ 2 :=
    Finset.sum_nonneg (fun j _hj => sq_nonneg (a j))
  exact hRay.trans (mul_le_mul_of_nonneg_right hScale hCoeff)

/-- Exact scale/rank-uniform logical handoff via a *single* genuine
Wilson trace-trajectory certificate, with no invented positivity,
mode independence or fixed r. The certificate is still OPEN. -/
theorem p4Q2FA_originalSignedGram_uniformRayleigh_of_traceCertificate
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (K : ℝ)
    (hSmall : ∀ n, beta n ≤ (1 : ℝ) / 8)
    (hTrace : ∀ (n r : ℕ),
      (halfExtent (n + 1) + 1 : ℝ) ^ 3 * (beta n) ^ 2 *
        (∑ i : Fin (r + 1),
          (p4Q2EY_originalWilsonRightModeNormFactor
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r i) ^ 2) ≤ K) :
    ∀ (n r : ℕ) (a : Fin (r + 1) → ℝ),
      star a ⬝ᵥ (Matrix.mulVec
        (fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) a) ≤
        (3072 * K) * (∑ j : Fin (r + 1), (a j) ^ 2) := by
  intro n r a
  exact p4Q2FA_originalSignedGram_rayleigh_le_certifiedTrace
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r a K (hSmall n) (hTrace n r)

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FA_originalModeCovariance_trace_eq_sum_linkNormSq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FA_originalSignedGram_rayleigh_le_actualPhysicalTrace
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FA_originalSignedGram_rayleigh_le_smallBetaTrace
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FA_originalSignedGram_rayleigh_le_certifiedTrace
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2FA_originalSignedGram_uniformRayleigh_of_traceCertificate
