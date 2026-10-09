import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarExactJointHalfDensityMoments
import Mathlib.Tactic

/-!
# P4-Q2-D: genuine original Wilson posterior-Hilbert scalar Rayleigh envelope

Use the exact physical joint moments now proved for W/Omega and for the
signed receiver J_f = W*M_f, together with the authentic local-Harnack
pointwise original Wilson two-copy posterior bound.

For R = exp(8 beta), lambda = ||T_beta||, and
C = lambda^{-1} (R^2-1) ||f||_HaarL2,

 E_e(J_f) <= 2 (R*C)^2 lambda^{-2}
                 + 2 (R-1)^2 (lambda^{-1}||S_beta f||)^2.

There are NO independent global ||W||_sup / ||M_f||_sup bounds and NO
unknown integrated joint moments in the conclusion. The coefficient is
derived from the original Wilson joint law, not a surrogate posterior.
The original uncentered right Krylov Gram inherits this linkwise
explicit scalar upper envelope, but lambda and the true full link sum
are still finite-volume dependent: no H-uniformity or continuum gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

local instance p4ScalarMomentTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4ScalarMomentCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4ScalarMomentSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4ScalarMomentMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4ScalarMomentBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4ScalarMomentLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Genuine original-Wilson linkwise posterior energy with both local
joint-square moments evaluated exactly; neither W nor M global sup
occurs. The square-of-sum estimate is the elementary real Hilbert
bound (x+y)^2 <= 2*x^2+2*y^2, without a fictitious independence law. -/
theorem normalizedPhysicalOneSlabJointReceiverProductBCF_posteriorEnergy_le_exactJointHilbertScalar
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    let l : ℝ := ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖⁻¹
    let R : ℝ := Real.exp (8 * beta)
    let C : ℝ := l * (R ^ 2 - 1) * ‖f‖
    let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta
    posteriorResamplingEnergy H N hN beta hbeta e
      (normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f) ≤
      2 * (R * C) ^ 2 * l ^ 2 +
        2 * (R - 1) ^ 2 * (l * ‖S f‖) ^ 2 := by
  let Cfg := PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
  let ν :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
      H N hN beta hbeta
  let W := normalizedPhysicalOneSlabJointHalfDensityWeightBCF H N hN beta hbeta
  let V := normalizedPhysicalOneSlabContinuousVacuumInverseBCF H N hN beta hbeta
  let J := normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f
  let l : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖⁻¹
  let R : ℝ := Real.exp (8 * beta)
  let C : ℝ := l * (R ^ 2 - 1) * ‖f‖
  let S :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta
  letI : IsProbabilityMeasure ν :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_isProbabilityMeasure
      H N hN beta hbeta
  let A : BoundedContinuousFunction (Cfg × Cfg) ℝ :=
    BoundedContinuousFunction.mkOfCompact
      ⟨fun z => (R * W z) * (C * V z.2),
        (continuous_const.mul W.continuous).mul
          (continuous_const.mul (V.continuous.comp continuous_snd))⟩
  let B : BoundedContinuousFunction (Cfg × Cfg) ℝ :=
    BoundedContinuousFunction.mkOfCompact
      ⟨fun z => (R - 1) * |J z|,
        continuous_const.mul J.continuous.abs⟩
  have hInt (G : BoundedContinuousFunction (Cfg × Cfg) ℝ) :
      Integrable (fun z => (G z) ^ 2) ν := by
    apply Integrable.of_bound
      ((G.continuous.pow 2).aestronglyMeasurable)
      (‖G‖ ^ 2)
    filter_upwards with z
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (G.norm_coe_le_norm z) 2
  have hIntA : Integrable (fun z => (A z) ^ 2) ν := hInt A
  have hIntB : Integrable (fun z => (B z) ^ 2) ν := hInt B
  have hIntSum : Integrable (fun z => (A z + B z) ^ 2) ν := by
    simpa only [BoundedContinuousFunction.add_apply] using hInt (A + B)
  have hIntUpper : Integrable
      (fun z => 2 * (A z) ^ 2 + 2 * (B z) ^ 2) ν :=
    (hIntA.const_mul 2).add (hIntB.const_mul 2)
  have hMomW : (∫ z, (W z * V z.2) ^ 2 ∂ν) = l ^ 2 := by
    have h :=
      normalizedPhysicalOneSlabJointHalfDensityWeightBCF_mul_vacuumInverse_sq_integral_joint_eq
        H N hN beta hbeta
    change (∫ z, (W z * V z.2) ^ 2 ∂ν) = l ^ 2 at h
    exact h
  have hMomJ : (∫ z, (J z) ^ 2 ∂ν) = (l * ‖S f‖) ^ 2 := by
    have h := normalizedPhysicalOneSlabJointReceiverProductBCF_sq_integral_joint_eq
      H N hN beta hbeta f
    change (∫ z, (J z) ^ 2 ∂ν) = (l * ‖S f‖) ^ 2 at h
    exact h
  have hA : (∫ z, (A z) ^ 2 ∂ν) = (R * C) ^ 2 * l ^ 2 := by
    change (∫ z, ((R * W z) * (C * V z.2)) ^ 2 ∂ν) =
      (R * C) ^ 2 * l ^ 2
    calc
      (∫ z, ((R * W z) * (C * V z.2)) ^ 2 ∂ν) =
          ∫ z, (R * C) ^ 2 * (W z * V z.2) ^ 2 ∂ν := by
        apply integral_congr_ae
        filter_upwards with z
        ring
      _ = (R * C) ^ 2 * (∫ z, (W z * V z.2) ^ 2 ∂ν) := by
        rw [integral_const_mul]
      _ = (R * C) ^ 2 * l ^ 2 := by rw [hMomW]
  have hB : (∫ z, (B z) ^ 2 ∂ν) =
      (R - 1) ^ 2 * (l * ‖S f‖) ^ 2 := by
    change (∫ z, ((R - 1) * |J z|) ^ 2 ∂ν) =
      (R - 1) ^ 2 * (l * ‖S f‖) ^ 2
    calc
      (∫ z, ((R - 1) * |J z|) ^ 2 ∂ν) =
          ∫ z, (R - 1) ^ 2 * (J z) ^ 2 ∂ν := by
        apply integral_congr_ae
        filter_upwards with z
        simp only [mul_pow, sq_abs]
      _ = (R - 1) ^ 2 * (∫ z, (J z) ^ 2 ∂ν) := by
        rw [integral_const_mul]
      _ = (R - 1) ^ 2 * (l * ‖S f‖) ^ 2 := by rw [hMomJ]
  have hPoint (z : Cfg × Cfg) :
      (A z + B z) ^ 2 ≤
        2 * (A z) ^ 2 + 2 * (B z) ^ 2 := by
    nlinarith [sq_nonneg (A z - B z)]
  have hBase :=
    normalizedPhysicalOneSlabJointReceiverProductBCF_posteriorEnergy_le_jointLocalHilbertMoment
      H N hN beta hbeta f e
  change posteriorResamplingEnergy H N hN beta hbeta e J ≤
    ∫ z, (A z + B z) ^ 2 ∂ν at hBase
  change posteriorResamplingEnergy H N hN beta hbeta e J ≤
    2 * (R * C) ^ 2 * l ^ 2 +
      2 * (R - 1) ^ 2 * (l * ‖S f‖) ^ 2
  calc
    posteriorResamplingEnergy H N hN beta hbeta e J ≤
        ∫ z, (A z + B z) ^ 2 ∂ν := hBase
    _ ≤ ∫ z, (2 * (A z) ^ 2 + 2 * (B z) ^ 2) ∂ν :=
      integral_mono hIntSum hIntUpper hPoint
    _ = 2 * (∫ z, (A z) ^ 2 ∂ν) +
        2 * (∫ z, (B z) ^ 2 ∂ν) := by
      rw [integral_add (hIntA.const_mul 2) (hIntB.const_mul 2),
        integral_const_mul, integral_const_mul]
    _ = 2 * (R * C) ^ 2 * l ^ 2 +
        2 * (R - 1) ^ 2 * (l * ‖S f‖) ^ 2 := by
      rw [hA, hB]
      ring

/-- Actual frozen physical Wilson parameters and fine-beta source;
each link receives the SAME genuine scalar envelope, making the
unresolved link cardinality/volume issue explicit rather than hidden. -/
noncomputable def fineRightKrylovOriginalPhysicalJointScalarHilbertEnergyEnvelope
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ) : ℝ :=
  let H := halfExtent (n + 1)
  let F := fineRightKrylovOriginalSignedPhysicalSource
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a
  let l : ℝ := ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)‖⁻¹
  let R : ℝ := Real.exp (8 * beta n)
  let C : ℝ := l * (R ^ 2 - 1) * ‖F‖
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  2 * (R * C) ^ 2 * l ^ 2 + 2 * (R - 1) ^ 2 * (l * ‖S F‖) ^ 2

theorem fineRightKrylovOriginalPhysicalJointObservable_posteriorEnergy_le_exactJointHilbertScalar
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ)
    (e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1))) :
    posteriorResamplingEnergy (halfExtent (n + 1)) 2
      specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) e
      (fineRightKrylovOriginalPhysicalJointObservable
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a) ≤
      fineRightKrylovOriginalPhysicalJointScalarHilbertEnergyEnvelope
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a := by
  simpa only [fineRightKrylovOriginalPhysicalJointScalarHilbertEnergyEnvelope,
    fineRightKrylovOriginalPhysicalJointObservable,
    fineRightKrylovOriginalSignedPhysicalSource] using
    (normalizedPhysicalOneSlabJointReceiverProductBCF_posteriorEnergy_le_exactJointHilbertScalar
      (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
      (beta n) (hbeta n)
      (∑ j : Fin (r + 1), a j •
        physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n (j : ℕ)) e)

/-- Original UN-CENTERED right-Krylov Gram Rayleigh using the actual
joint-L² physical scalar envelope with no factor global sup or unknown
joint integral. This DOES NOT prove uniform control of the true link sum. -/
theorem fineRightKrylovPairHaarResidualGram_rayleigh_le_exactJointHilbertScalar
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) (a : Fin (r + 1) → ℝ) :
    star a ⬝ᵥ (Matrix.mulVec
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a) ≤
      (1 / 2 : ℝ) *
        ∑ _e : PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1)),
          fineRightKrylovOriginalPhysicalJointScalarHilbertEnergyEnvelope
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r a := by
  let H := halfExtent (n + 1)
  let J := fineRightKrylovOriginalPhysicalJointObservable
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r a
  have hRay :
      star a ⬝ᵥ (Matrix.mulVec
        (fineRightKrylovPairHaarResidualGram
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) a) =
      (1 / 2 : ℝ) *
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          posteriorResamplingEnergy H 2 specialUnitaryTwoWilsonRankPositive
            (beta n) (hbeta n) e J := by
    simpa only [H, J, fineRightKrylovOriginalPhysicalJointObservable] using
      (fineRightKrylovPairHaarResidualGram_rayleigh_eq_half_originalResamplingEnergy
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r a)
  have hOne (e : PeriodicHypercubicEvenSpatialSliceLink H) :
      posteriorResamplingEnergy H 2 specialUnitaryTwoWilsonRankPositive
        (beta n) (hbeta n) e J ≤
      fineRightKrylovOriginalPhysicalJointScalarHilbertEnergyEnvelope
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r a :=
    fineRightKrylovOriginalPhysicalJointObservable_posteriorEnergy_le_exactJointHilbertScalar
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r a e
  calc
    star a ⬝ᵥ (Matrix.mulVec
      (fineRightKrylovPairHaarResidualGram
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r) a) =
      (1 / 2 : ℝ) *
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H,
          posteriorResamplingEnergy H 2 specialUnitaryTwoWilsonRankPositive
            (beta n) (hbeta n) e J := hRay
    _ ≤ (1 / 2 : ℝ) *
        ∑ _e : PeriodicHypercubicEvenSpatialSliceLink H,
          fineRightKrylovOriginalPhysicalJointScalarHilbertEnergyEnvelope
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r a := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro e _he
        exact hOne e
      · norm_num

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
