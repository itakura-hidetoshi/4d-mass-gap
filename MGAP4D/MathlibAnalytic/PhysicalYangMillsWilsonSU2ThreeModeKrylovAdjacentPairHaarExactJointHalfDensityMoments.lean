import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPhysicalJointLocalHilbertMoment
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentFrozenHalfDensityPairHaarL2
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-!
# P4-Q2-D: exact genuine Wilson joint half-density squared moments

The actual normalized Wilson joint law is the physical ground-state
density times spatial pair Haar.  Its continuous positive square root
is already identified a.e. with the original L² eigenvector density.

The half-density W(z) times the inverse physical vacuum Omega(z.2)^{-1}
is exactly lambda^{-1}/sqrt(rho_joint(z)). Thus its SQUARED original
Wilson joint moment cancels the density and equals lambda^{-2},
with no global W or Omega inverse supremum.

For the signed product J_f=W*M_f, use the previously proved authentic
half-density isometry to identify its JOINT L² moment exactly with
lambda^{-2} times the norm squared of the original normalized physical
transfer output. No reconstructed conditional law, Dobrushin, new axiom
or finite-volume-uniform claim.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

local instance p4ExactHalfMomentTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4ExactHalfMomentCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4ExactHalfMomentSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4ExactHalfMomentMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4ExactHalfMomentBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4ExactHalfMomentLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The exact ORIGINAL joint moment of the genuine Wilson half-density
weighted by the inverse continuous positive vacuum. This is an
integrated density cancellation, not a claim on either global sup norm. -/
theorem normalizedPhysicalOneSlabJointHalfDensityWeightBCF_mul_vacuumInverse_sq_integral_joint_eq
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    let W := normalizedPhysicalOneSlabJointHalfDensityWeightBCF H N hN beta hbeta
    let V := normalizedPhysicalOneSlabContinuousVacuumInverseBCF H N hN beta hbeta
    (∫ z, (W z * V z.2) ^ 2
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta) =
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖⁻¹ ^ 2 := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  let w :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
      H N hN beta hbeta
  let rho : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ENNReal :=
    fun z => ENNReal.ofReal (w z)
  let Ω :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
      H N hN beta hbeta
  let W := normalizedPhysicalOneSlabJointHalfDensityWeightBCF H N hN beta hbeta
  let V := normalizedPhysicalOneSlabContinuousVacuumInverseBCF H N hN beta hbeta
  let l : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖⁻¹
  have hwStrong : AEStronglyMeasurable w μ :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight_integrable
      H N hN beta hbeta).aestronglyMeasurable
  have hrhoMeas : AEMeasurable rho μ :=
    hwStrong.aemeasurable.ennreal_ofReal
  have hrhoTop : ∀ᵐ z ∂μ, rho z < (⊤ : ENNReal) := by
    filter_upwards with z
    simp [rho]
  have hwPos : ∀ᵐ z ∂μ, 0 < w z :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight_ae_pos
      H N hN beta hbeta
  have hDensity :
      (fun z => continuousJointSqrtDensity H N hN beta hbeta z) =ᵐ[μ]
      (fun z => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSqrtDensity
        H N hN beta hbeta z) :=
    continuousJointSqrtDensity_ae_eq H N hN beta hbeta
  haveI : IsProbabilityMeasure μ := by
    dsimp [μ, periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure,
      periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
    infer_instance
  change (∫ z, (W z * V z.2) ^ 2 ∂(μ.withDensity rho)) = l ^ 2
  calc
    (∫ z, (W z * V z.2) ^ 2 ∂(μ.withDensity rho)) =
        ∫ z, (rho z).toReal • (W z * V z.2) ^ 2 ∂μ :=
      integral_withDensity_eq_integral_toReal_smul₀ hrhoMeas hrhoTop _
    _ = ∫ _z, l ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [hwPos, hDensity] with z hw hD
      have hOmega : Ω z.2 ≠ 0 :=
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
          H N hN beta hbeta z.2).ne'
      have hSqrt : Real.sqrt (w z) ≠ 0 :=
        (Real.sqrt_pos.2 hw).ne'
      have hDen :
          continuousJointSqrtDensity H N hN beta hbeta z =
            Real.sqrt (w z) := by
        rw [hD]
        rfl
      simp only [smul_eq_mul]
      dsimp [rho]
      rw [ENNReal.toReal_ofReal hw.le]
      change w z * (((l * Ω z.2) /
        continuousJointSqrtDensity H N hN beta hbeta z) *
          (Ω z.2)⁻¹) ^ 2 = l ^ 2
      rw [hDen]
      calc
        w z * (((l * Ω z.2) / Real.sqrt (w z)) * (Ω z.2)⁻¹) ^ 2 =
            (Real.sqrt (w z)) ^ 2 *
              (((l * Ω z.2) / Real.sqrt (w z)) * (Ω z.2)⁻¹) ^ 2 := by
                rw [Real.sq_sqrt hw.le]
        _ = l ^ 2 := by field_simp [hOmega, hSqrt]
    _ = l ^ 2 := by simp

/-- The original signed physical receiver joint L² moment is exactly
the normalized physical-transfer image norm times lambda^{-2}; this
is the genuine pair-Haar-to-joint isometry, not an estimated sup. -/
theorem normalizedPhysicalOneSlabJointReceiverProductBCF_sq_integral_joint_eq
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    (∫ z,
      (normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f z) ^ 2
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta) =
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖⁻¹ *
        ‖periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta f‖) ^ 2 := by
  let ν :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
      H N hN beta hbeta
  let J := normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f
  let U := BoundedContinuousFunction.toLp 2 ν ℝ J
  let l : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖⁻¹
  let S :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta
  letI : IsProbabilityMeasure ν :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_isProbabilityMeasure
      H N hN beta hbeta
  have hrep : U =ᵐ[ν] fun z => J z :=
    BoundedContinuousFunction.coeFn_toLp 2 ν ℝ J
  have hn : ‖U‖ = l * ‖S f‖ := by
    simpa only [U, J, l, S] using
      normalizedPhysicalOneSlabJointReceiverProductBCF_toLp_norm_eq_inv_transferNorm
        H N hN beta hbeta f
  change (∫ z, (J z) ^ 2 ∂ν) = (l * ‖S f‖) ^ 2
  calc
    (∫ z, (J z) ^ 2 ∂ν) = ‖U‖ ^ 2 := by
      rw [realL2_norm_sq_eq_integral_norm_sq]
      apply integral_congr_ae
      filter_upwards [hrep] with z hz
      rw [hz]
      simp only [Real.norm_eq_abs, sq_abs]
    _ = (l * ‖S f‖) ^ 2 := by rw [hn]

/-- A consequence relying only on the actual normalized physical
transfer contraction; still retains the true lambda^{-1} factor. -/
theorem normalizedPhysicalOneSlabJointReceiverProductBCF_sq_integral_joint_le_input
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    (∫ z,
      (normalizedPhysicalOneSlabJointReceiverProductBCF H N hN beta hbeta f z) ^ 2
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta) ≤
      (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H N hN beta hbeta‖⁻¹ * ‖f‖) ^ 2 := by
  let S :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta
  let l : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖⁻¹
  have hS : ‖S‖ = 1 := by
    simpa only [S] using
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_norm
        H N hN beta hbeta
  have hNorm : ‖S f‖ ≤ ‖f‖ := by
    calc
      ‖S f‖ ≤ ‖S‖ * ‖f‖ := ContinuousLinearMap.le_opNorm S f
      _ = ‖f‖ := by rw [hS, one_mul]
  have hl : 0 ≤ l :=
    (inv_pos.mpr
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
        H N hN beta hbeta)).le
  have hm : l * ‖S f‖ ≤ l * ‖f‖ :=
    mul_le_mul_of_nonneg_left hNorm hl
  have hp : (l * ‖S f‖) ^ 2 ≤ (l * ‖f‖) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hl (norm_nonneg _)) hm 2
  exact (normalizedPhysicalOneSlabJointReceiverProductBCF_sq_integral_joint_eq
    H N hN beta hbeta f).trans hp

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
