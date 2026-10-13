import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSignedFineFrozenSmallBetaUniformGate
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarUncenteredResamplingPolarization
import Mathlib.Tactic

/-!
# P4-Q2-EW: genuine link-resolved original Wilson posterior frozen-beta zero

EV/EU prove the true uncentered signed fine-right Krylov Gram Rayleigh
vanishes at the FROZEN original Wilson beta(n)=0, without setting the
genuinely distinct fine beta(n+1) to zero.

Here the exact original Wilson two-copy posterior resampling energy identity
implies a STRICTER typed statement: at frozen beta(n)=0 EVERY ACTUAL right
physical spatial link has zero original Wilson posterior resampling energy
for the SAME full signed fine-right input. Consequently the authentic
transported frozen-beta original Wilson one-link projection fixes the
complete signed receiver at EACH individual physical link.

All statements retain the true original posterior law, receiver, and
signed fine orbit. No independent Haar substitution, artificial local
support or Dobrushin assumption. This exact beta-zero boundary result
does not control positive-beta H-uniform signed Gram or continuum gaps.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

private noncomputable instance p4Q2EW_spatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Original physical Wilson posterior two-replica resampling loss is
ZERO at EACH actual spatial right link on the SAME frozen-beta-zero
signed fine/right Krylov combination (whose fine beta is independent).
This strengthens the already-proved vanishing of the total Gram. -/
theorem fineRightKrylovOriginalWilsonPosteriorResampling_each_eq_zero_of_frozenBeta_zero
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ) (hZero : beta n = 0)
    (e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1))) :
    posteriorResamplingEnergy
      (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
      (beta n) (hbeta n) e
      (fineRightKrylovOriginalPhysicalJointObservable
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r a) = 0 := by
  classical
  let H := halfExtent (n + 1)
  let F :
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2 :=
    ∑ j : Fin (r + 1), a j •
      physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n (j : ℕ)
  let O := fineRightKrylovOriginalPhysicalJointObservable
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  let V := normalizedPhysicalOneSlabPairHaarReceiver
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  let Q := pairHaarTransportedGroundStateSpatialLinkProjection
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  have hRay :=
    fineRightKrylovPairHaarResidualGram_rayleigh_eq_zero_of_frozenBeta_zero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a hZero
  have hExact :=
    fineRightKrylovPairHaarResidualGram_rayleigh_eq_half_originalResamplingEnergy
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a
  change
    star a ⬝ᵥ (Matrix.mulVec
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a) =
      (1 / 2 : ℝ) *
        ∑ k : PeriodicHypercubicEvenSpatialSliceLink H,
          posteriorResamplingEnergy H 2 specialUnitaryTwoWilsonRankPositive
            (beta n) (hbeta n) k O at hExact
  have hHalf :
      (1 / 2 : ℝ) *
        (∑ k : PeriodicHypercubicEvenSpatialSliceLink H,
          posteriorResamplingEnergy H 2 specialUnitaryTwoWilsonRankPositive
            (beta n) (hbeta n) k O) = 0 :=
    hExact.symm.trans hRay
  have hSum :
      (∑ k : PeriodicHypercubicEvenSpatialSliceLink H,
          posteriorResamplingEnergy H 2 specialUnitaryTwoWilsonRankPositive
            (beta n) (hbeta n) k O) = 0 := by
    linarith
  have hNonneg (k : PeriodicHypercubicEvenSpatialSliceLink H) :
      0 ≤ posteriorResamplingEnergy H 2 specialUnitaryTwoWilsonRankPositive
          (beta n) (hbeta n) k O := by
    have hEnergy :=
      normalizedPhysicalOneSlabJointReceiverProductBCF_resamplingEnergy_eq_two_pairHaarResidual
        H 2 specialUnitaryTwoWilsonRankPositive
        (beta n) (hbeta n) F k
    change posteriorResamplingEnergy H 2 specialUnitaryTwoWilsonRankPositive
        (beta n) (hbeta n) k O = 2 * ‖V F - Q k (V F)‖ ^ 2 at hEnergy
    rw [hEnergy]
    positivity
  have hFunction := (Fintype.sum_eq_zero_iff_of_nonneg hNonneg).mp hSum
  have hAtLink := congrFun hFunction e
  simpa using hAtLink

/-- The genuine frozen-original-Wilson one-link projection fixes
the signed physical fine-right receiver at EVERY ACTUAL right link,
provided ONLY that the original frozen beta(n) is zero. The distinct
fine beta(n+1) remains completely unrestricted except nonnegativity. -/
theorem fineRightKrylovOriginalWilsonPosteriorProjection_fixed_of_frozenBeta_zero
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ) (hZero : beta n = 0)
    (e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1))) :
    normalizedPhysicalOneSlabPairHaarReceiver
        (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
        (beta n) (hbeta n)
        (∑ j : Fin (r + 1), a j •
          physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n (j : ℕ)) =
      pairHaarTransportedGroundStateSpatialLinkProjection
        (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
        (beta n) (hbeta n) e
        (normalizedPhysicalOneSlabPairHaarReceiver
          (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
          (beta n) (hbeta n)
          (∑ j : Fin (r + 1), a j •
            physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
              (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
              n (j : ℕ))) := by
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
  have hPosterior :=
    fineRightKrylovOriginalWilsonPosteriorResampling_each_eq_zero_of_frozenBeta_zero
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a hZero e
  have hEnergy :=
    normalizedPhysicalOneSlabJointReceiverProductBCF_resamplingEnergy_eq_two_pairHaarResidual
      H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) F e
  change posteriorResamplingEnergy H 2 specialUnitaryTwoWilsonRankPositive
      (beta n) (hbeta n) e
      (fineRightKrylovOriginalPhysicalJointObservable
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a) =
      2 * ‖V F - Q e (V F)‖ ^ 2 at hEnergy
  rw [hPosterior] at hEnergy
  have hNorm : ‖V F - Q e (V F)‖ = 0 := by
    have hNN := norm_nonneg (V F - Q e (V F))
    nlinarith [hEnergy]
  change V F = Q e (V F)
  exact sub_eq_zero.mp (norm_eq_zero.mp hNorm)

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.fineRightKrylovOriginalWilsonPosteriorResampling_each_eq_zero_of_frozenBeta_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.fineRightKrylovOriginalWilsonPosteriorProjection_fixed_of_frozenBeta_zero
