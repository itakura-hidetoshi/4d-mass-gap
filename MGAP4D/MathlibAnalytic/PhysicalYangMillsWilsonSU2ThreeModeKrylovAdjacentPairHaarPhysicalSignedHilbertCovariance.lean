import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarExactJointHilbertScalarRayleigh
import Mathlib.Tactic

/-!
# P4-Q2-D: genuine original Wilson signed posterior Hilbert covariance

The authentic original Wilson signed posterior innovation
  I_e(f) = V_beta(f) - Q_{beta,e}(V_beta(f))
obeys an explicit *source-Hilbert* quadratic estimate obtained solely
from the genuine joint-Hilbert scalar resampling bound of PR #5337.
The local scalar coefficient is

  gamma_beta,H = (R (R^2-1) lambda^{-2})^2
                    + ((R-1)lambda^{-1})^2,
  R=exp(8 beta), lambda=||T_beta,H||.

The true signed covariance is therefore bounded as a BILINEAR
source-Hilbert form:
  |inner(I_e(f),I_e(g))| <= gamma_beta,H ||f||_2 ||g||_2.

This retains the original posterior, the sign of each cross-covariance
and the distinct frozen beta(n)/fine beta(n+1) right-Krylov data. It
does NOT manufacture cross-mode covariance decay or a volume-uniform
sum over links; a genuine signed Schur row bound still needs independent
physical locality/correlation information. No Dobrushin, sorry, admit,
or new axiom.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

local instance p4SignedCovTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4SignedCovCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4SignedCovSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4SignedCovMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4SignedCovBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4SignedCovLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Explicit physical beta-dependent squared source-Hilbert bound
for the actual original Wilson posterior innovation at a single link. -/
noncomputable def originalWilsonPhysicalSignedInnovationHilbertCoefficient
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) : ℝ :=
  let R : ℝ := Real.exp (8 * beta)
  let l : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖⁻¹
  (R * (R ^ 2 - 1) * l ^ 2) ^ 2 + ((R - 1) * l) ^ 2

theorem originalWilsonPhysicalSignedInnovationHilbertCoefficient_nonneg
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    0 ≤ originalWilsonPhysicalSignedInnovationHilbertCoefficient
      H N hN beta hbeta := by
  unfold originalWilsonPhysicalSignedInnovationHilbertCoefficient
  positivity

/-- The squared coefficient factors through (exp(8 beta)-1)^2;
in particular it vanishes exactly at beta=0, without a local-posterior
surrogate or extra positive-kernel comparison of signed inputs. -/
theorem originalWilsonPhysicalSignedInnovationHilbertCoefficient_factor
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    let R : ℝ := Real.exp (8 * beta)
    let l : ℝ :=
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖⁻¹
    originalWilsonPhysicalSignedInnovationHilbertCoefficient
      H N hN beta hbeta =
      (R - 1) ^ 2 * l ^ 2 *
        (1 + R ^ 2 * (R + 1) ^ 2 * l ^ 2) := by
  dsimp [originalWilsonPhysicalSignedInnovationHilbertCoefficient]
  ring

/-- Exact physical one-link innovation quadratic estimate:
  ||I_e(f)||^2 <= gamma_beta,H ||f||_HaarL2^2.
The original Wilson resampling-to-pair-Haar equality divides its
energy by precisely two. -/
theorem physicalOriginalReceiverPosteriorInnovation_norm_sq_le_signedHilbert
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    ‖physicalOriginalReceiverPosteriorInnovation H N hN beta hbeta e f‖ ^ 2 ≤
      originalWilsonPhysicalSignedInnovationHilbertCoefficient
        H N hN beta hbeta * ‖f‖ ^ 2 := by
  let l : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖⁻¹
  let R : ℝ := Real.exp (8 * beta)
  let S :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta
  let A : ℝ := R * (R ^ 2 - 1) * l ^ 2
  let B : ℝ := (R - 1) * l
  let gamma : ℝ :=
    originalWilsonPhysicalSignedInnovationHilbertCoefficient
      H N hN beta hbeta
  let J := normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f
  have hS : ‖S‖ = 1 := by
    simpa only [S] using
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_norm
        H N hN beta hbeta
  have hSn : ‖S f‖ ≤ ‖f‖ := by
    calc
      ‖S f‖ ≤ ‖S‖ * ‖f‖ := ContinuousLinearMap.le_opNorm S f
      _ = ‖f‖ := by rw [hS, one_mul]
  have hSsq : ‖S f‖ ^ 2 ≤ ‖f‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hSn 2
  have hGamma : gamma = A ^ 2 + B ^ 2 := rfl
  have hEnergy := 
    normalizedPhysicalOneSlabJointReceiverProductBCF_posteriorEnergy_le_exactJointHilbertScalar
      H N hN beta hbeta f e
  change posteriorResamplingEnergy H N hN beta hbeta e J ≤
    2 * (R * (l * (R ^ 2 - 1) * ‖f‖)) ^ 2 * l ^ 2 +
      2 * (R - 1) ^ 2 * (l * ‖S f‖) ^ 2 at hEnergy
  have hTotal :
      posteriorResamplingEnergy H N hN beta hbeta e J ≤
        2 * gamma * ‖f‖ ^ 2 := by
    calc
      posteriorResamplingEnergy H N hN beta hbeta e J ≤
          2 * (R * (l * (R ^ 2 - 1) * ‖f‖)) ^ 2 * l ^ 2 +
            2 * (R - 1) ^ 2 * (l * ‖S f‖) ^ 2 := hEnergy
      _ = 2 * A ^ 2 * ‖f‖ ^ 2 + 2 * B ^ 2 * ‖S f‖ ^ 2 := by
        dsimp [A, B]
        ring
      _ ≤ 2 * A ^ 2 * ‖f‖ ^ 2 + 2 * B ^ 2 * ‖f‖ ^ 2 := by
        exact add_le_add_right
          (mul_le_mul_of_nonneg_left hSsq (by positivity))
          (2 * A ^ 2 * ‖f‖ ^ 2)
      _ = 2 * gamma * ‖f‖ ^ 2 := by
        rw [hGamma]
        ring
  have hExact :=
    normalizedPhysicalOneSlabJointReceiverProductBCF_resamplingEnergy_eq_two_pairHaarResidual
      H N hN beta hbeta f e
  change posteriorResamplingEnergy H N hN beta hbeta e J =
    2 * ‖physicalOriginalReceiverPosteriorInnovation H N hN beta hbeta e f‖ ^ 2
    at hExact
  rw [hExact] at hTotal
  change ‖physicalOriginalReceiverPosteriorInnovation
    H N hN beta hbeta e f‖ ^ 2 ≤ gamma * ‖f‖ ^ 2
  nlinarith only [hTotal]

/-- Square-root operator amplitude consequence for the signed original
Wilson innovation, valid for every original physical source f. -/
theorem physicalOriginalReceiverPosteriorInnovation_norm_le_sqrt_signedHilbert
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    ‖physicalOriginalReceiverPosteriorInnovation H N hN beta hbeta e f‖ ≤
      Real.sqrt (originalWilsonPhysicalSignedInnovationHilbertCoefficient
        H N hN beta hbeta) * ‖f‖ := by
  let gamma := originalWilsonPhysicalSignedInnovationHilbertCoefficient
    H N hN beta hbeta
  have hGamma : 0 ≤ gamma :=
    originalWilsonPhysicalSignedInnovationHilbertCoefficient_nonneg
      H N hN beta hbeta
  have hSq :
      ‖physicalOriginalReceiverPosteriorInnovation H N hN beta hbeta e f‖ ^ 2 ≤
        gamma * ‖f‖ ^ 2 :=
    physicalOriginalReceiverPosteriorInnovation_norm_sq_le_signedHilbert
      H N hN beta hbeta e f
  have hRight : 0 ≤ Real.sqrt gamma * ‖f‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  have hRightSq : (Real.sqrt gamma * ‖f‖) ^ 2 = gamma * ‖f‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hGamma]
  change ‖physicalOriginalReceiverPosteriorInnovation
    H N hN beta hbeta e f‖ ≤ Real.sqrt gamma * ‖f‖
  nlinarith [hSq, hRightSq, norm_nonneg
    (physicalOriginalReceiverPosteriorInnovation H N hN beta hbeta e f)]

/-- The TRUE signed original Wilson one-link posterior covariance is
bounded by a product of the two original physical source-Hilbert norms.
The signed inner product is retained until its final absolute value. -/
theorem physicalOriginalReceiverPosteriorInnovation_inner_abs_le_signedHilbert
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (f g : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    |inner ℝ
      (physicalOriginalReceiverPosteriorInnovation H N hN beta hbeta e f)
      (physicalOriginalReceiverPosteriorInnovation H N hN beta hbeta e g)| ≤
        originalWilsonPhysicalSignedInnovationHilbertCoefficient
          H N hN beta hbeta * ‖f‖ * ‖g‖ := by
  let gamma := originalWilsonPhysicalSignedInnovationHilbertCoefficient
    H N hN beta hbeta
  let I := physicalOriginalReceiverPosteriorInnovation H N hN beta hbeta e
  have hGamma : 0 ≤ gamma :=
    originalWilsonPhysicalSignedInnovationHilbertCoefficient_nonneg
      H N hN beta hbeta
  have hF : ‖I f‖ ≤ Real.sqrt gamma * ‖f‖ :=
    physicalOriginalReceiverPosteriorInnovation_norm_le_sqrt_signedHilbert
      H N hN beta hbeta e f
  have hG : ‖I g‖ ≤ Real.sqrt gamma * ‖g‖ :=
    physicalOriginalReceiverPosteriorInnovation_norm_le_sqrt_signedHilbert
      H N hN beta hbeta e g
  change |inner ℝ (I f) (I g)| ≤ gamma * ‖f‖ * ‖g‖
  calc
    |inner ℝ (I f) (I g)| ≤ ‖I f‖ * ‖I g‖ :=
      abs_real_inner_le_norm (I f) (I g)
    _ ≤ (Real.sqrt gamma * ‖f‖) * ‖I g‖ :=
      mul_le_mul_of_nonneg_right hF (norm_nonneg _)
    _ ≤ (Real.sqrt gamma * ‖f‖) * (Real.sqrt gamma * ‖g‖) :=
      mul_le_mul_of_nonneg_left hG
        (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    _ = gamma * ‖f‖ * ‖g‖ := by
      calc
        (Real.sqrt gamma * ‖f‖) * (Real.sqrt gamma * ‖g‖) =
            (Real.sqrt gamma) ^ 2 * ‖f‖ * ‖g‖ := by ring
        _ = gamma * ‖f‖ * ‖g‖ := by rw [Real.sq_sqrt hGamma]

/-- Physical frozen beta(n) and fine beta(n+1) signed mode-pair bridge
to the exact-original Wilson covariance used by PR #5321 Schur.
This is a LINKWISE source-Hilbert bound, not a fictitious certified
summable spatial covariance decay. -/
theorem fineRightKrylovOriginalPosteriorLinkCovariance_abs_le_physicalSignedHilbert
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)))
    (i j : Fin (r + 1)) :
    let H := halfExtent (n + 1)
    let R : Fin (r + 1) →
        periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2 :=
      fun k => physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n (k : ℕ)
    |fineRightKrylovOriginalPosteriorLinkCovariance
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r e i j| ≤
      originalWilsonPhysicalSignedInnovationHilbertCoefficient
        H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) *
        ‖R i‖ * ‖R j‖ := by
  let H := halfExtent (n + 1)
  let R : Fin (r + 1) →
      periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2 :=
    fun k => physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n (k : ℕ)
  change |inner ℝ
    (physicalOriginalReceiverPosteriorInnovation H 2
      specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) e (R i))
    (physicalOriginalReceiverPosteriorInnovation H 2
      specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) e (R j))| ≤
    originalWilsonPhysicalSignedInnovationHilbertCoefficient
      H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) *
      ‖R i‖ * ‖R j‖
  exact physicalOriginalReceiverPosteriorInnovation_inner_abs_le_signedHilbert
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
    e (R i) (R j)

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
