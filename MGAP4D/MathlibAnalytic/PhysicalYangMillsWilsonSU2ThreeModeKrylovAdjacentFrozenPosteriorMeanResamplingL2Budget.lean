import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentFrozenPosteriorMeanJointL2
import Mathlib.Tactic

/-!
# Coefficient-one projection budget for the genuine frozen posterior receiver

PR #5259 identifies the actual right-boundary frozen posterior mean as
a joint-L2 vector of norm bounded by the physical input norm.

The original posterior resampling energy is exactly twice the squared
residual of the existing genuine joint conditional-expectation
orthogonal projection.  Pythagoras thus gives, for any joint BCF F,

  E_e(F) = 2 (||F||_L2(joint)^2 - ||P_e F||_L2(joint)^2)
         <= 2 ||F||_L2(joint)^2.

Specializing to the frozen posterior mean M_f yields

  E_e(M_f) <= 2 ||S f||_Haar^2 <= 2 ||f||_Haar^2,

with coefficient two independent of finite spatial volume.
For each left-mode factor and the common-right factor in the actual
adjacent orbit, this yields E_e(M) <= 2 at every finite depth r,
while the orbit uses beta(n+1) and the final receiver uses beta(n).

This only controls each fixed-link mean resampling energy, not
the sum over spatial links, the half-density product W*M, or the
continuum Yang--Mills mass gap.  No new Dobrushin bound, support
assumption, or covariance/L2 identification is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

local instance p3ResamplingL2TopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance p3ResamplingL2CompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance p3ResamplingL2SecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance p3ResamplingL2MeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance p3ResamplingL2BorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance p3ResamplingL2SpatialLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance p3ResamplingL2JointProbability
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    IsProbabilityMeasure
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_isProbabilityMeasure
    H N hN beta hbeta

namespace GroundStatePosteriorJoint

/-- The original posterior resampling energy is exactly twice the difference
of the original joint-L2 norm square and the projected joint-L2 norm square.
There is no independent resampling law or conditional-variance surrogate. -/
theorem posteriorResamplingEnergy_eq_two_jointL2_projectionLoss
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ) :
    posteriorResamplingEnergy H N hN beta hbeta e F =
      2 * (
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2RepresentativeBCF
            H N hN beta hbeta F‖ ^ 2 -
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
            H N hN beta hbeta e
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2RepresentativeBCF
              H N hN beta hbeta F)‖ ^ 2) := by
  rw [
    posteriorResamplingEnergy_eq_twice_stageEnergy,
    posteriorStageResidualEnergy_eq_norm_loss
      H N hN beta hbeta [] e F
      F.continuous.stronglyMeasurable ‖F‖ F.norm_coe_le_norm
  ]
  simp only [
    List.nil_append,
    posteriorScheduleL2_eq_projectionSchedule,
    jointBCF_boundedConcreteL2_eq_standardRepresentative,
    realHilbertProjectionSweep,
    ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply
  ]

/-- The Pythagorean projection loss gives the universal coefficient-two
bound for an arbitrary genuine joint bounded continuous observable. -/
theorem posteriorResamplingEnergy_le_two_jointL2_norm_sq
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (F : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ) :
    posteriorResamplingEnergy H N hN beta hbeta e F ≤
      2 *
        ‖BoundedContinuousFunction.toLp
          2
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
            H N hN beta hbeta)
          ℝ F‖ ^ 2 := by
  rw [posteriorResamplingEnergy_eq_two_jointL2_projectionLoss
    H N hN beta hbeta e F]
  let fJ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2RepresentativeBCF
      H N hN beta hbeta F
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
      H N hN beta hbeta e
  have hp : 0 ≤ ‖P fJ‖ ^ 2 := sq_nonneg _
  change 2 * (‖fJ‖ ^ 2 - ‖P fJ‖ ^ 2) ≤ 2 * ‖fJ‖ ^ 2
  nlinarith

/-- For a physical Haar-L2 input, the literal frozen posterior receiver
has one-link resampling energy controlled by the actual normalized physical
transfer image, not by a volume-dependent supremum norm. -/
theorem normalizedPhysicalOneSlabVacuumMeanJointBCF_resamplingEnergy_le_two_transfer_norm_sq
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    posteriorResamplingEnergy H N hN beta hbeta e
        (normalizedPhysicalOneSlabVacuumMeanJointBCF H N hN beta hbeta f) ≤
      2 * ‖periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
        H N hN beta hbeta f‖ ^ 2 := by
  have hBound :=
    posteriorResamplingEnergy_le_two_jointL2_norm_sq H N hN beta hbeta e
      (normalizedPhysicalOneSlabVacuumMeanJointBCF H N hN beta hbeta f)
  rw [normalizedPhysicalOneSlabVacuumMeanJointBCF_toLp_norm_eq_transfer
    H N hN beta hbeta f] at hBound
  exact hBound

/-- Generic physical-input bound with coefficient two and no volume factor. -/
theorem normalizedPhysicalOneSlabVacuumMeanJointBCF_resamplingEnergy_le_two_input_norm_sq
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    posteriorResamplingEnergy H N hN beta hbeta e
        (normalizedPhysicalOneSlabVacuumMeanJointBCF H N hN beta hbeta f) ≤
      2 * ‖f‖ ^ 2 := by
  have hEnergy :=
    normalizedPhysicalOneSlabVacuumMeanJointBCF_resamplingEnergy_le_two_transfer_norm_sq
      H N hN beta hbeta e f
  let S :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
      H N hN beta hbeta
  have hNorm :
      ‖S‖ = 1 := by
    simpa [S] using
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_norm
        H N hN beta hbeta
  have hTransfer : ‖S f‖ ≤ ‖f‖ := by
    calc
      ‖S f‖ ≤ ‖S‖ * ‖f‖ := ContinuousLinearMap.le_opNorm S f
      _ = ‖f‖ := by rw [hNorm, one_mul]
  have hSq : ‖S f‖ ^ 2 ≤ ‖f‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hTransfer 2
  have hScaled := mul_le_mul_of_nonneg_left hSq (by norm_num : (0 : ℝ) ≤ 2)
  exact hEnergy.trans (by simpa [S] using hScaled)

section ActualAdjacentOrbit

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ)

local notation "Hn" => halfExtent (n + 1)
local notation "Pos" => specialUnitaryTwoWilsonRankPositive

/-- Every actual evolved left mode has frozen posterior one-link
resampling energy at most two, uniformly over finite orbit depth. -/
theorem fineOrbitLeftFrozenPosteriorMean_resamplingEnergy_le_two
    (k : Fin 3)
    (e : PeriodicHypercubicEvenSpatialSliceLink Hn) :
    posteriorResamplingEnergy Hn 2 Pos (beta n) (hbeta n) e
      (normalizedPhysicalOneSlabVacuumMeanJointBCF
        Hn 2 Pos (beta n) (hbeta n)
        (physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r k)) ≤ 2 := by
  have hEnergy :=
    normalizedPhysicalOneSlabVacuumMeanJointBCF_resamplingEnergy_le_two_input_norm_sq
      Hn 2 Pos (beta n) (hbeta n) e
      (physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r k)
  have hNorm :=
    fineOrbitLeftFactor_norm_le_one
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r k
  have hSq :
      ‖physicalYangMillsSU2AdjacentFinePairOrbitLeftFactor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r k‖ ^ 2 ≤ 1 := by
    simpa only [one_pow] using
      (pow_le_pow_left₀ (norm_nonneg _) hNorm 2)
  nlinarith

/-- The mode-independent actual right factor obeys the same frozen
one-link mean energy budget at every finite orbit depth. -/
theorem fineOrbitRightFrozenPosteriorMean_resamplingEnergy_le_two
    (e : PeriodicHypercubicEvenSpatialSliceLink Hn) :
    posteriorResamplingEnergy Hn 2 Pos (beta n) (hbeta n) e
      (normalizedPhysicalOneSlabVacuumMeanJointBCF
        Hn 2 Pos (beta n) (hbeta n)
        (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r)) ≤ 2 := by
  have hEnergy :=
    normalizedPhysicalOneSlabVacuumMeanJointBCF_resamplingEnergy_le_two_input_norm_sq
      Hn 2 Pos (beta n) (hbeta n) e
      (physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r)
  have hNorm :=
    physicalYangMillsSU2AdjacentFinePairOrbitRightFactor_norm_le_one
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r
  have hSq :
      ‖physicalYangMillsSU2AdjacentFinePairOrbitRightFactor
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r‖ ^ 2 ≤ 1 := by
    simpa only [one_pow] using
      (pow_le_pow_left₀ (norm_nonneg _) hNorm 2)
  nlinarith

end ActualAdjacentOrbit
end GroundStatePosteriorJoint

end
end MathlibAnalytic
end MGAP4D
