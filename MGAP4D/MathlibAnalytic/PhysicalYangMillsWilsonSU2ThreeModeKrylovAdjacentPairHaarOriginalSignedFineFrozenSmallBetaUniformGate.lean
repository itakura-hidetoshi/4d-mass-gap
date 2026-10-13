import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSignedFineFrozenCubicBetaEnvelope
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-!
# P4-Q2-EV: Actual signed Wilson fine/frozen Krylov small-beta quantitative gate

EU provides the genuine original-Wilson signed fine/frozen right-Krylov
Rayleigh estimate with actual posterior two-copy resampling, physical
frozen beta(n) half-density, positive continuous vacuum inverse, normalized
frozen physical mean and signed fine beta(n+1) input:

  aᵀ G(n,r) a <= 12*(H+1)^3 * (exp(8*beta(n))-1)^2 * F(n,r,a)^2.

Use the pinned mathlib real exponential estimate at 0 <= beta(n) <= 1/8
to derive the explicit polynomial 3072*(H+1)^3*beta(n)^2 factor.

The exact remaining physical source/vacuum norm F is never thrown away.
A formal sufficient *uniform gate* isolates TWO missing physical premises:
common control of volume*beta(n)^2 and a uniform signed physical norm
factor bound relative to the genuine coefficient l2 square. No such
uniform norm bound or genuine adjacent-scale trajectory is proved here.

The theorem is NOT a volume-uniform Yang-Mills mass-gap result,
not an AW/D12 relative comparison, and not a substitute posterior law.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

namespace GroundStatePosteriorJoint

/-- Pinned-mathlib real exponential estimate for a nonnegative frozen
Wilson beta in the exact small-coupling window beta <= 1/8. -/
theorem p4Q2EV_exp_eight_sub_one_le_sixteen_beta
    (b : ℝ) (hb : 0 ≤ b) (hSmall : b ≤ (1 : ℝ) / 8) :
    Real.exp (8 * b) - 1 ≤ 16 * b := by
  have hArgNonneg : 0 ≤ (8 : ℝ) * b := by positivity
  have hArg : |(8 : ℝ) * b| ≤ (1 : ℝ) := by
    rw [abs_of_nonneg hArgNonneg]
    nlinarith [hSmall]
  have hBound :=
    Real.abs_exp_sub_one_le (x := (8 : ℝ) * b) hArg
  calc
    Real.exp (8 * b) - 1 ≤ |Real.exp (8 * b) - 1| :=
      le_abs_self _
    _ ≤ 2 * |(8 : ℝ) * b| := hBound
    _ = 16 * b := by rw [abs_of_nonneg hArgNonneg]; ring

/-- A genuine quadratic frozen-beta coefficient: no invented bound
outside the pinned real-exponential small-coupling window. -/
theorem p4Q2EV_exp_eight_sub_one_sq_le_beta_sq
    (b : ℝ) (hb : 0 ≤ b) (hSmall : b ≤ (1 : ℝ) / 8) :
    (Real.exp (8 * b) - 1) ^ 2 ≤ (16 * b) ^ 2 := by
  have hExpOne : (1 : ℝ) ≤ Real.exp (8 * b) := by
    simpa using
      (Real.exp_le_exp.mpr (show (0 : ℝ) ≤ 8 * b by positivity) :
        Real.exp (0 : ℝ) ≤ Real.exp (8 * b))
  have hPos : 0 ≤ Real.exp (8 * b) - 1 := by linarith
  exact pow_le_pow_left₀ hPos
    (p4Q2EV_exp_eight_sub_one_le_sixteen_beta b hb hSmall) 2

/-- Fully authenticated original-Wilson signed uncentered right-Krylov
Gram small-frozen-beta Rayleigh with the true source/vacuum factor.
Frozen beta(n) and fine beta(n+1) remain distinct parameters. -/
theorem fineRightKrylovPairHaarResidualGram_rayleigh_le_smallBetaCubic
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ)
    (hSmall : beta n ≤ (1 : ℝ) / 8) :
    star a ⬝ᵥ (Matrix.mulVec
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a) ≤
      3072 * (halfExtent (n + 1) + 1 : ℝ) ^ 3 *
        (beta n) ^ 2 *
        (fineRightKrylovOriginalSignedSourceVacuumFactor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r a) ^ 2 := by
  let F := fineRightKrylovOriginalSignedSourceVacuumFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  have hEU :=
    fineRightKrylovPairHaarResidualGram_rayleigh_le_cubicBetaSquared
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  change star a ⬝ᵥ (Matrix.mulVec
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a) ≤
      12 * (halfExtent (n + 1) + 1 : ℝ) ^ 3 *
        (Real.exp (8 * beta n) - 1) ^ 2 * F ^ 2 at hEU
  have hSq :=
    p4Q2EV_exp_eight_sub_one_sq_le_beta_sq
      (beta n) (hbeta n) hSmall
  have hCoef : 0 ≤ (12 : ℝ) * (halfExtent (n + 1) + 1 : ℝ) ^ 3 := by
    positivity
  have hFirst :
      (12 : ℝ) * (halfExtent (n + 1) + 1 : ℝ) ^ 3 *
          (Real.exp (8 * beta n) - 1) ^ 2 ≤
        (12 : ℝ) * (halfExtent (n + 1) + 1 : ℝ) ^ 3 *
          (16 * beta n) ^ 2 :=
    mul_le_mul_of_nonneg_left hSq hCoef
  have hSecond :
      (12 : ℝ) * (halfExtent (n + 1) + 1 : ℝ) ^ 3 *
          (Real.exp (8 * beta n) - 1) ^ 2 * F ^ 2 ≤
        (12 : ℝ) * (halfExtent (n + 1) + 1 : ℝ) ^ 3 *
          (16 * beta n) ^ 2 * F ^ 2 :=
    mul_le_mul_of_nonneg_right hFirst (sq_nonneg F)
  calc
    star a ⬝ᵥ (Matrix.mulVec
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a) ≤
        12 * (halfExtent (n + 1) + 1 : ℝ) ^ 3 *
          (Real.exp (8 * beta n) - 1) ^ 2 * F ^ 2 := hEU
    _ ≤ 12 * (halfExtent (n + 1) + 1 : ℝ) ^ 3 *
          (16 * beta n) ^ 2 * F ^ 2 := hSecond
    _ = 3072 * (halfExtent (n + 1) + 1 : ℝ) ^ 3 *
          (beta n) ^ 2 * F ^ 2 := by ring

/-- Explicit finite-level sufficient physical input for a signed Gram
operator Rayleigh bound: independently certify the ACTUAL volume-beta
trajectory and the ACTUAL norm of the physical signed fine/frozen source.
Neither certificate is manufactured or claimed to hold generally. -/
theorem fineRightKrylovPairHaarResidualGram_rayleigh_le_certifiedScaleNorm
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ)
    (K M : ℝ) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hSmall : beta n ≤ (1 : ℝ) / 8)
    (hScale :
      (halfExtent (n + 1) + 1 : ℝ) ^ 3 * (beta n) ^ 2 ≤ K)
    (hFactor :
      (fineRightKrylovOriginalSignedSourceVacuumFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r a) ^ 2 ≤ M * ∑ j : Fin (r + 1), (a j) ^ 2) :
    star a ⬝ᵥ (Matrix.mulVec
        (fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) a) ≤
      (3072 * K * M) * ∑ j : Fin (r + 1), (a j) ^ 2 := by
  let F := fineRightKrylovOriginalSignedSourceVacuumFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  have hEU :=
    fineRightKrylovPairHaarResidualGram_rayleigh_le_smallBetaCubic
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a hSmall
  have hFirst :
      ((halfExtent (n + 1) + 1 : ℝ) ^ 3 * (beta n) ^ 2) * F ^ 2 ≤
        K * F ^ 2 :=
    mul_le_mul_of_nonneg_right hScale (sq_nonneg F)
  have hSecond :
      K * F ^ 2 ≤ K * (M * ∑ j : Fin (r + 1), (a j) ^ 2) :=
    mul_le_mul_of_nonneg_left hFactor hK
  have hCombined := hFirst.trans hSecond
  calc
    star a ⬝ᵥ (Matrix.mulVec
        (fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) a) ≤
        3072 * (halfExtent (n + 1) + 1 : ℝ) ^ 3 *
          (beta n) ^ 2 * F ^ 2 := hEU
    _ = 3072 *
          (((halfExtent (n + 1) + 1 : ℝ) ^ 3 * (beta n) ^ 2) *
            F ^ 2) := by ring
    _ ≤ 3072 * (K * (M * ∑ j : Fin (r + 1), (a j) ^ 2)) :=
      mul_le_mul_of_nonneg_left hCombined (by norm_num)
    _ = (3072 * K * M) * ∑ j : Fin (r + 1), (a j) ^ 2 := by ring

/-- Exact logical H/scale-uniform Rayleigh handoff:
the SAME nonnegative K,M work for every n,r and SIGNED real coefficient
vector, only if the two displayed independent original physical
certificates are actually supplied. This is a conditional theorem,
not a claim that C1/C2/C3 or the required Wilson norms are closed. -/
theorem fineRightKrylovPairHaarResidualGram_uniformRayleigh_of_certificates
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (K M : ℝ) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (hSmall : ∀ n, beta n ≤ (1 : ℝ) / 8)
    (hScale : ∀ n,
      (halfExtent (n + 1) + 1 : ℝ) ^ 3 * (beta n) ^ 2 ≤ K)
    (hFactor : ∀ (n r : ℕ) (a : Fin (r + 1) → ℝ),
      (fineRightKrylovOriginalSignedSourceVacuumFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r a) ^ 2 ≤ M * ∑ j : Fin (r + 1), (a j) ^ 2) :
    ∀ (n r : ℕ) (a : Fin (r + 1) → ℝ),
      star a ⬝ᵥ (Matrix.mulVec
        (fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) a) ≤
        (3072 * K * M) * ∑ j : Fin (r + 1), (a j) ^ 2 := by
  intro n r a
  exact fineRightKrylovPairHaarResidualGram_rayleigh_le_certifiedScaleNorm
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r a K M hK hM (hSmall n) (hScale n) (hFactor n r a)

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2EV_exp_eight_sub_one_le_sixteen_beta
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2EV_exp_eight_sub_one_sq_le_beta_sq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.fineRightKrylovPairHaarResidualGram_rayleigh_le_smallBetaCubic
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.fineRightKrylovPairHaarResidualGram_rayleigh_le_certifiedScaleNorm
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.fineRightKrylovPairHaarResidualGram_uniformRayleigh_of_certificates
