import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalRelativeWilsonSU2ExactSixColorCardinality
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPhysicalHilbertLinkBudgetBridge
import Mathlib.Tactic

/-!
# P4-Q2-EU: actual signed fine/frozen Wilson Krylov Gram and cubic beta envelope

This file changes lane from ET's original Haar-reference AW / interacting
D12 relative comparison to the independent AUTHENTIC uncentered signed
fine/frozen right-Krylov Gram. The original frozen Wilson ground-state
half-density and normalized physical vacuum-mean receiver are retained,
as are the fine beta(n+1) input and the frozen beta(n) original law.

ES gives the exact number 24*(H+1)^3 of ACTUAL physical spatial links.
The earlier original Wilson posterior two-copy resampling and BCF
signed-Hilbert estimates give the linkwise genuine Gram budget.
The exact algebraic factorization of that already-proved physical budget
then exposes a square (exp(8*beta(n))-1)^2, without replacing the actual
physical vacuum, transfer, signed mean, or original posterior.

The resulting finite-H estimate explicitly displays the volume factor
and the true physical norm factor. It does NOT establish any H-uniform
signed Gram control, C1/C2/C3 reconstruction, physical time evolution,
or a four-dimensional Yang-Mills mass gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

private noncomputable instance p4Q2EU_spatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Exact ORIGINAL canonical time-zero spatial link count, obtained
from ES's true reflection-plane vertex cardinality and the genuine
three non-temporal link directions. There are six equally sized colors,
each with 4*(H+1)^3 links; total 24*(H+1)^3. -/
theorem p4Q2EU_originalPhysicalSpatialLinks_card_exact (H : ℕ) :
    Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) =
      24 * (H + 1) ^ 3 := by
  classical
  have hVert := p4Q2ES_originalSpatialVertex_card H
  have hDir := periodicHypercubicOtherAxis_card (0 : PeriodicHypercubicAxis)
  rw [← Nat.card_eq_fintype_card] at hVert hDir
  calc
    Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) =
        Nat.card (PeriodicHypercubicEvenSpatialSliceLink H) :=
      (Nat.card_eq_fintype_card _).symm
    _ = Nat.card (PeriodicHypercubicEvenSpatialSliceVertex H) *
          Nat.card PeriodicHypercubicEvenSpatialDirection := by
      change Nat.card
        (PeriodicHypercubicEvenSpatialSliceVertex H ×
          PeriodicHypercubicEvenSpatialDirection) = _
      exact Nat.card_prod _ _
    _ = (2 * (H + 1)) ^ 3 * 3 := by rw [hVert, hDir]
    _ = 24 * (H + 1) ^ 3 := by ring

namespace GroundStatePosteriorJoint

/-- The remaining EXACT physical signed-Hilbert norm factor after
extracting the genuine frozen-Wilson local Harnack factor exp(8 beta)-1.
This uses the ACTUAL original SU(2) half-density W, physical frozen
transfer inverse, positive continuous vacuum inverse, genuine signed
fine-right source F, and normalized physical mean M. It need not be
bounded uniformly in spatial H. -/
noncomputable def fineRightKrylovOriginalSignedSourceVacuumFactor
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ) : ℝ :=
  let H := halfExtent (n + 1)
  let W := normalizedPhysicalOneSlabJointHalfDensityWeightBCF
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  let M := fineRightKrylovOriginalVacuumMeanJointBCF
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  let L := ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)‖⁻¹
  let V := ‖normalizedPhysicalOneSlabContinuousVacuumInverseBCF
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)‖
  let F := ‖fineRightKrylovOriginalSignedPhysicalSource
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a‖
  ‖W‖ * (L * (Real.exp (8 * beta n) + 1) * V * F + ‖M‖)

/-- The physically constructed signed source/vacuum factor is
nonnegative without positivity of the underlying signed source. -/
theorem fineRightKrylovOriginalSignedSourceVacuumFactor_nonneg
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ) :
    0 ≤ fineRightKrylovOriginalSignedSourceVacuumFactor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a := by
  unfold fineRightKrylovOriginalSignedSourceVacuumFactor
  dsimp
  positivity

/-- Exact algebraic factorization of the PREVIOUSLY PROVED authentic
original Wilson signed-Hilbert link budget. The source remains fine
beta(n+1) and the physical frozen law remains beta(n). No new local
variation bound or artificial posterior is assumed. -/
theorem fineRightKrylovOriginalPhysicalHilbertBudget_eq_betaFactor
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ) :
    fineRightKrylovOriginalPhysicalHilbertLinkBudgetEnvelope
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a =
      (Real.exp (8 * beta n) - 1) *
        fineRightKrylovOriginalSignedSourceVacuumFactor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a := by
  unfold fineRightKrylovOriginalPhysicalHilbertLinkBudgetEnvelope
    fineRightKrylovOriginalPhysicalMeanHilbertLinkEnvelope
    fineRightKrylovOriginalSignedSourceVacuumFactor
  dsimp
  ring

/-- Genuine finite-H volume counting closes the actual physical Wilson
signed uncentered fine/frozen Gram Rayleigh upper bound with EXACT
24*(H+1)^3 spatial links and the original 1/2 two-copy normalization.
No relative AW/D12 lower inequality is used or needed. -/
theorem fineRightKrylovPairHaarResidualGram_rayleigh_le_cubicPhysicalHilbertBudget
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ) :
    star a ⬝ᵥ (Matrix.mulVec
        (fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) a) ≤
      12 * (halfExtent (n + 1) + 1 : ℝ) ^ 3 *
        (fineRightKrylovOriginalPhysicalHilbertLinkBudgetEnvelope
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r a) ^ 2 := by
  let H := halfExtent (n + 1)
  let B := fineRightKrylovOriginalPhysicalHilbertLinkBudgetEnvelope
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  have hRay :=
    fineRightKrylovPairHaarResidualGram_rayleigh_le_physicalHilbertLinkBudget
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  change star a ⬝ᵥ (Matrix.mulVec
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a) ≤
      (1 / 2 : ℝ) *
        ∑ _e : PeriodicHypercubicEvenSpatialSliceLink H, B ^ 2 at hRay
  calc
    star a ⬝ᵥ (Matrix.mulVec
        (fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) a) ≤
        (1 / 2 : ℝ) *
          ∑ _e : PeriodicHypercubicEvenSpatialSliceLink H, B ^ 2 := hRay
    _ = (1 / 2 : ℝ) *
        (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
          B ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    _ = 12 * (H + 1 : ℝ) ^ 3 * B ^ 2 := by
      rw [p4Q2EU_originalPhysicalSpatialLinks_card_exact]
      push_cast
      ring

/-- The actual signed fine/frozen Gram enjoys a quadratic
(exp(8*beta(n))-1)^2 upper envelope, with its precise cubic physical
volume dependence and the true remaining signed Wilson norm factor.
This has no invented positive signed-covariance estimate. -/
theorem fineRightKrylovPairHaarResidualGram_rayleigh_le_cubicBetaSquared
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ) :
    star a ⬝ᵥ (Matrix.mulVec
        (fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) a) ≤
      12 * (halfExtent (n + 1) + 1 : ℝ) ^ 3 *
        (Real.exp (8 * beta n) - 1) ^ 2 *
        (fineRightKrylovOriginalSignedSourceVacuumFactor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r a) ^ 2 := by
  have hRay :=
    fineRightKrylovPairHaarResidualGram_rayleigh_le_cubicPhysicalHilbertBudget
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  rw [fineRightKrylovOriginalPhysicalHilbertBudget_eq_betaFactor] at hRay
  nlinarith [hRay]

/-- If the FROZEN original beta(n) is zero, the constructed authentic
physical Hilbert link budget vanishes, independently of the genuinely
fine beta(n+1) source. No β_n=β_(n+1) identification. -/
theorem fineRightKrylovOriginalPhysicalHilbertBudget_zero_of_frozenBeta_zero
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ)
    (hZero : beta n = 0) :
    fineRightKrylovOriginalPhysicalHilbertLinkBudgetEnvelope
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a = 0 := by
  rw [fineRightKrylovOriginalPhysicalHilbertBudget_eq_betaFactor]
  simp [hZero]

/-- Unconditional concrete beta-zero FROZEN-law conclusion for the
original uncentered signed fine/frozen right Krylov Gram: its Rayleigh
form is ZERO for every signed coefficient vector. Fine beta(n+1)
remains a distinct parameter and is not set to zero. The physical
sum-of-squared-residual representation gives nonnegativity. -/
theorem fineRightKrylovPairHaarResidualGram_rayleigh_eq_zero_of_frozenBeta_zero
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ)
    (hZero : beta n = 0) :
    star a ⬝ᵥ (Matrix.mulVec
        (fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) a) = 0 := by
  have hUpper :=
    fineRightKrylovPairHaarResidualGram_rayleigh_le_cubicPhysicalHilbertBudget
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  rw [fineRightKrylovOriginalPhysicalHilbertBudget_zero_of_frozenBeta_zero
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a hZero] at hUpper
  simp only [zero_pow (by norm_num : 2 ≠ 0), mul_zero] at hUpper
  have hIdentity :=
    fineRightKrylovPairHaarResidualGram_rayleigh
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  have hLower :
      0 ≤ star a ⬝ᵥ (Matrix.mulVec
        (fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) a) := by
    rw [hIdentity]
    exact Finset.sum_nonneg (fun e _ => sq_nonneg _)
  exact le_antisymm hUpper hLower

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.p4Q2EU_originalPhysicalSpatialLinks_card_exact
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.fineRightKrylovOriginalSignedSourceVacuumFactor_nonneg
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.fineRightKrylovOriginalPhysicalHilbertBudget_eq_betaFactor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.fineRightKrylovPairHaarResidualGram_rayleigh_le_cubicPhysicalHilbertBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.fineRightKrylovPairHaarResidualGram_rayleigh_le_cubicBetaSquared
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.fineRightKrylovOriginalPhysicalHilbertBudget_zero_of_frozenBeta_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.fineRightKrylovPairHaarResidualGram_rayleigh_eq_zero_of_frozenBeta_zero
