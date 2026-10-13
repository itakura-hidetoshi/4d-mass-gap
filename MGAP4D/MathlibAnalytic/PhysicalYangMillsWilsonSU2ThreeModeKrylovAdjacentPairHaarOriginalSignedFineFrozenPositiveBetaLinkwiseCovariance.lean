import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSignedFrozenWilsonLinkwiseZero
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPhysicalHilbertLinkBudgetBridge
import Mathlib.Tactic

/-!
# P4-Q2-EX: TRUE original Wilson positive-beta per-link resampling and signed covariance

This takes the INDEPENDENT uncentered signed fine/frozen right-Krylov
lane of EU/EV/EW further, WITHOUT original Haar Riesz AW / interacting
D12 relative comparison and WITHOUT substitute pair-Haar resampling.

For every genuine original spatial RIGHT link at frozen beta(n), the
actual original Wilson posterior two-replica resampling loss of the
full signed fine beta(n+1) physical source is bounded by the ACTUAL
frozen Wilson half-density/normalized mean certified link oscillation.
Factorization of the actual positive-beta Wilson Harnack and signed
source-Hilbert envelope gives, for 0 <= beta(n) <= 1/8,

    originalPosteriorResamplingEnergy_e(O_a)
        <= 256 * beta(n)^2 * F(n,r,a)^2.

The exact real 2-copy identity yields for the TRUE transported posterior
one-link residual in pair-Haar realization:

    ‖V(F_a) - Q_e V(F_a)‖² <= 128 * beta(n)^2 * F(n,r,a)^2.

For two signed coefficient combinations a,b, retain the SIGNED
original Wilson cross-mode covariance as the real Hilbert inner product
of these genuine transported residuals and bound only its final
absolute value, via Cauchy-Schwarz and the exact residual squares:

    |⟪I_e(F_a), I_e(F_b)⟫|
        <= 64 * beta(n)^2 * (F(n,r,a)^2 + F(n,r,b)^2).

Every estimate is genuinely LINKWISE (no premature spatial |E(H)|
factor). The original physical Wilson/vacuum norm F can still depend
on H, n and r. No H-uniform signed Gram, covariance decay, C1/C2/C3
or Yang-Mills continuum mass gap is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 900000

namespace GroundStatePosteriorJoint

/-- The actual original frozen Wilson posterior two-copy energy at each
real spatial link is bounded by the full genuine physical signed-source
Harnack factor. No cardinality summation or surrogate Wilson law. -/
theorem fineRightKrylovOriginalWilsonPosteriorResampling_le_betaFactor
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ)
    (e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1))) :
    posteriorResamplingEnergy
      (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
      (beta n) (hbeta n) e
      (fineRightKrylovOriginalPhysicalJointObservable
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r a) ≤
      (Real.exp (8 * beta n) - 1) ^ 2 *
        (fineRightKrylovOriginalSignedSourceVacuumFactor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r a) ^ 2 := by
  let H := halfExtent (n + 1)
  let O := fineRightKrylovOriginalPhysicalJointObservable
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  let B := fineRightKrylovOriginalHalfDensityMeanLinkBudget
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a e
  let E := fineRightKrylovOriginalPhysicalHilbertLinkBudgetEnvelope
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  let F := fineRightKrylovOriginalSignedSourceVacuumFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  have hPoint : ∀ z (g : Matrix.specialUnitaryGroup (Fin 2) ℂ),
      |O z - O (z.1, Function.update z.2 e g)| ≤ B := by
    intro z g
    exact fineRightKrylovOriginalPhysicalJointObservable_linkVariation_le_halfDensityMean
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a e z g
  have hPosterior :=
    originalWilsonPosteriorResamplingEnergy_le_constantLinkOscillation
      H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
      e O B hPoint
  have hBNonneg : 0 ≤ B :=
    fineRightKrylovOriginalHalfDensityMeanLinkBudget_nonneg
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a e
  have hBE : B ≤ E :=
    fineRightKrylovOriginalHalfDensityMeanLinkBudget_le_physicalHilbertEnvelope
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a e
  have hBSq : B ^ 2 ≤ E ^ 2 :=
    pow_le_pow_left₀ hBNonneg hBE 2
  have hFactor :
      E = (Real.exp (8 * beta n) - 1) * F :=
    fineRightKrylovOriginalPhysicalHilbertBudget_eq_betaFactor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a
  calc
    posteriorResamplingEnergy H 2 specialUnitaryTwoWilsonRankPositive
        (beta n) (hbeta n) e O ≤ B ^ 2 := hPosterior
    _ ≤ E ^ 2 := hBSq
    _ = (Real.exp (8 * beta n) - 1) ^ 2 * F ^ 2 := by rw [hFactor]; ring

/-- GENUINE positive-frozen-beta small-coupling bound on each physical
Wilson posterior resampling energy. The physical norm factor is
EXACTLY EU's original signed half-density/mean/vacuum factor. -/
theorem fineRightKrylovOriginalWilsonPosteriorResampling_le_smallBetaSource
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ)
    (e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)))
    (hSmall : beta n ≤ (1 : ℝ) / 8) :
    posteriorResamplingEnergy
      (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
      (beta n) (hbeta n) e
      (fineRightKrylovOriginalPhysicalJointObservable
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r a) ≤
      256 * (beta n) ^ 2 *
        (fineRightKrylovOriginalSignedSourceVacuumFactor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r a) ^ 2 := by
  let F := fineRightKrylovOriginalSignedSourceVacuumFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  have hEnergy :=
    fineRightKrylovOriginalWilsonPosteriorResampling_le_betaFactor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a e
  have hSmallExp :=
    p4Q2EV_exp_eight_sub_one_sq_le_beta_sq
      (beta n) (hbeta n) hSmall
  have hMul :
      (Real.exp (8 * beta n) - 1) ^ 2 * F ^ 2 ≤
        (16 * beta n) ^ 2 * F ^ 2 :=
    mul_le_mul_of_nonneg_right hSmallExp (sq_nonneg F)
  calc
    posteriorResamplingEnergy (halfExtent (n + 1)) 2
        specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) e
        (fineRightKrylovOriginalPhysicalJointObservable
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r a) ≤
        (Real.exp (8 * beta n) - 1) ^ 2 * F ^ 2 := hEnergy
    _ ≤ (16 * beta n) ^ 2 * F ^ 2 := hMul
    _ = 256 * (beta n) ^ 2 * F ^ 2 := by ring

/-- True transported ORIGINAL frozen Wilson right-link residual for the
whole genuinely SIGNED fine-right coefficient combination. The L²
carrier is its faithful pair-Haar realization, not an independent
Haar-conditional projection substituted for the Wilson posterior. -/
noncomputable def fineRightKrylovOriginalWilsonSignedCombinationResidual
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ)
    (e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1))) :
    PeriodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarL2
      (halfExtent (n + 1)) 2 :=
  let H := halfExtent (n + 1)
  let F := ∑ j : Fin (r + 1), a j •
    physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n (j : ℕ)
  let V := normalizedPhysicalOneSlabPairHaarReceiver
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) F
  V - pairHaarTransportedGroundStateSpatialLinkProjection
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) e V

/-- Retain the true TWO-copy posterior-residual identity on each
original Wilson link and sharpen to the genuine positive-beta
transported signed physical residual squared-norm bound. -/
theorem fineRightKrylovOriginalWilsonSignedCombinationResidual_norm_sq_le_smallBetaSource
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ)
    (e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)))
    (hSmall : beta n ≤ (1 : ℝ) / 8) :
    ‖fineRightKrylovOriginalWilsonSignedCombinationResidual
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a e‖ ^ 2 ≤
      128 * (beta n) ^ 2 *
        (fineRightKrylovOriginalSignedSourceVacuumFactor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r a) ^ 2 := by
  let H := halfExtent (n + 1)
  let F :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2 :=
    ∑ j : Fin (r + 1), a j •
      physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n (j : ℕ)
  let V := normalizedPhysicalOneSlabPairHaarReceiver
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  let Q := pairHaarTransportedGroundStateSpatialLinkProjection
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  let R := fineRightKrylovOriginalWilsonSignedCombinationResidual
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r a e
  let G := fineRightKrylovOriginalSignedSourceVacuumFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r a
  have hResampling :=
    normalizedPhysicalOneSlabJointReceiverProductBCF_resamplingEnergy_eq_two_pairHaarResidual
      H 2 specialUnitaryTwoWilsonRankPositive
      (beta n) (hbeta n) F e
  change posteriorResamplingEnergy H 2 specialUnitaryTwoWilsonRankPositive
      (beta n) (hbeta n) e
      (fineRightKrylovOriginalPhysicalJointObservable
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r a) = 2 * ‖R‖ ^ 2 at hResampling
  have hE :=
    fineRightKrylovOriginalWilsonPosteriorResampling_le_smallBetaSource
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a e hSmall
  rw [hResampling] at hE
  change ‖R‖ ^ 2 ≤ 128 * (beta n) ^ 2 * G ^ 2
  nlinarith [hE]

/-- SIGNED original Wilson cross-covariance of any two actual fine-right
Krylov combinations, on the SAME frozen original Wilson link. Positivity
is never attributed to the signed cross-inner product. The final
absolute value is bounded using the real Hilbert Cauchy-Schwarz and
the two genuine two-copy linkwise squared residual estimates. -/
theorem fineRightKrylovOriginalWilsonSignedCombinationResidual_inner_abs_le_smallBeta
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a b : Fin (r + 1) → ℝ)
    (e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)))
    (hSmall : beta n ≤ (1 : ℝ) / 8) :
    |inner ℝ
      (fineRightKrylovOriginalWilsonSignedCombinationResidual
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r a e)
      (fineRightKrylovOriginalWilsonSignedCombinationResidual
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r b e)| ≤
      64 * (beta n) ^ 2 *
        ((fineRightKrylovOriginalSignedSourceVacuumFactor
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r a) ^ 2 +
         (fineRightKrylovOriginalSignedSourceVacuumFactor
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r b) ^ 2) := by
  let Ra := fineRightKrylovOriginalWilsonSignedCombinationResidual
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r a e
  let Rb := fineRightKrylovOriginalWilsonSignedCombinationResidual
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r b e
  let A := fineRightKrylovOriginalSignedSourceVacuumFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r a
  let B := fineRightKrylovOriginalSignedSourceVacuumFactor
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r b
  have hA :
      ‖Ra‖ ^ 2 ≤ 128 * (beta n) ^ 2 * A ^ 2 :=
    fineRightKrylovOriginalWilsonSignedCombinationResidual_norm_sq_le_smallBetaSource
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a e hSmall
  have hB :
      ‖Rb‖ ^ 2 ≤ 128 * (beta n) ^ 2 * B ^ 2 :=
    fineRightKrylovOriginalWilsonSignedCombinationResidual_norm_sq_le_smallBetaSource
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r b e hSmall
  have hAM :
      ‖Ra‖ * ‖Rb‖ ≤ (‖Ra‖ ^ 2 + ‖Rb‖ ^ 2) / 2 := by
    nlinarith [sq_nonneg (‖Ra‖ - ‖Rb‖)]
  calc
    |inner ℝ Ra Rb| ≤ ‖Ra‖ * ‖Rb‖ :=
      abs_real_inner_le_norm Ra Rb
    _ ≤ (‖Ra‖ ^ 2 + ‖Rb‖ ^ 2) / 2 := hAM
    _ ≤ (128 * (beta n) ^ 2 * A ^ 2 +
          128 * (beta n) ^ 2 * B ^ 2) / 2 := by
        linarith [add_le_add hA hB]
    _ = 64 * (beta n) ^ 2 * (A ^ 2 + B ^ 2) := by ring

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.fineRightKrylovOriginalWilsonPosteriorResampling_le_betaFactor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.fineRightKrylovOriginalWilsonPosteriorResampling_le_smallBetaSource
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.fineRightKrylovOriginalWilsonSignedCombinationResidual_norm_sq_le_smallBetaSource
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.fineRightKrylovOriginalWilsonSignedCombinationResidual_inner_abs_le_smallBeta
