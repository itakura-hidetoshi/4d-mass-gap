import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferPosteriorJointKernelRightVariation
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentExactBCF

/-!
# Actual frozen right-link variation from the full normalized kernel

The input below is the existing orbit at beta(n+1); the final transfer and
half-density use beta(n), on halfExtent(n+1). No vector or measure is redefined.
The initial variation and positive envelope are CONSTRUCTED, not assumed.
A local factor exp(16 beta_n)-1 is explicit. Neither this envelope nor its
propagated energy is asserted to have a support-distance tail.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory

noncomputable section

attribute [local instance]
  groundStateJointOneLinkBoundedCoreSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkBoundedCoreSpecialUnitaryCompactSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkBoundedCoreSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitaryBorelSpace
  groundStateJointOneLinkBoundedCoreSpatialLinkFintype

namespace GroundStatePosteriorJoint

variable {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
variable (n r : ℕ) (k : Fin 3)

local notation "Hn" => halfExtent (n + 1)
local notation "Pos" => specialUnitaryTwoWilsonRankPositive
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration Hn 2
local notation "Joint" => Cfg × Cfg
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink Hn
local notation "ResponseData" => PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteExpectationResponseMatrixData Hn 2 Pos (beta n) (hbeta n)
local notation "Agree" => PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorAgreeOff
local notation "Orbit" => physicalYangMillsSU2AdjacentFinePairOrbitVector (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k
local notation "ExactO" => fineFrozenBCF (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k
local notation "Rate" => kernelRightVariationRate (beta n)
local notation "OscEnergy" => periodicHypercubicEvenSpecialUnitaryGroundStateSixSpatialSweepStageOscillationEnergy Hn
local notation "FrozenProfile" => physicalYangMillsSU2AdjacentFineGroundStateSweepStageProfileEnergy (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k

/-- Positive BCF envelope constructed from the absolute ACTUAL orbit input. -/
def fineFrozenKernelEnvelope : BoundedContinuousFunction Joint ℝ :=
  jointTransferEnvelope Hn 2 Pos (beta n) (hbeta n) Orbit

/-- Quantitative initial width, retaining the envelope rather than hiding its size. -/
def fineFrozenKernelInitialVariation : Link → ℝ :=
  kernelRightInitialVariation Hn 2 Pos (beta n) (hbeta n) Orbit

/-- Direct pointwise variation, with no response-data or cutoff premise. -/
theorem fineFrozenBCF_right_variation (B : Cfg) (e : Link) (A C : Cfg)
    (hAgree : Agree A C e) :
    |ExactO (B, A) - ExactO (B, C)| ≤
      Rate * fineFrozenKernelEnvelope (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k (B, A) :=
  jointTransferBCF_right_variation Hn 2 Pos (beta n) (hbeta n) Orbit B e A C hAgree

/-- Actual one-link residual energy with the lossless positive-envelope L2 norm. -/
theorem fineFrozenPosteriorResidualEnergy_le (e : Link) :
    posteriorStageResidualEnergy Hn 2 Pos (beta n) (hbeta n) [] e ExactO ≤
      Rate ^ 2 * ‖periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalPairTransferOperator
        Hn 2 Pos (beta n) (hbeta n) (pairAbsoluteInput Hn 2 Orbit)‖ ^ 2 :=
  jointTransferPosteriorResidualEnergy_le Hn 2 Pos (beta n) (hbeta n) Orbit e

/-- Chronological propagation consumes the constructed initial width. There is
no hypothesis of a final residual bound or of an oscillation bound on ExactO. -/
theorem fineFrozenProfileEnergy_le_kernelVariationEnergy (R : ResponseData) :
    FrozenProfile ≤ OscEnergy (posteriorSixColorVariationProfile Hn 2 Pos (beta n) (hbeta n) R
      (fineFrozenKernelInitialVariation (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k)) := by
  rw [physicalYangMillsSU2AdjacentFineGroundStateSweepStageProfileEnergy_eq_generalProfileEnergy]
  rw [← fineFrozenBCF_rep_eq (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k]
  apply sixColorProfileEnergy_le_variationOscillationEnergy Hn 2 Pos (beta n) (hbeta n) R ExactO
    (fineFrozenKernelInitialVariation (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k)
    (kernelRightInitialVariation_nonneg Hn 2 Pos (beta n) (hbeta n) Orbit)
  exact kernelRightInitialVariation_bound Hn 2 Pos (beta n) (hbeta n) Orbit

/-- The canonical response data are constructed only under the original
fixed-right half-barrier cutoff, s>=1; this is not the strict-Dobrushin interval. -/
theorem fineFrozenProfileEnergy_le_canonicalKernelVariationEnergy
    (s : ℝ) (hs : 1 ≤ s)
    (hcut : beta n ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff s) :
    FrozenProfile ≤ OscEnergy (canonicalPosteriorSixColorVariation Hn 2 Pos (beta n) (hbeta n) s hs hcut
      (fineFrozenKernelInitialVariation (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k)) :=
  fineFrozenProfileEnergy_le_kernelVariationEnergy n r k
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorCanonicalFixedRightBootstrapRemoteExpectationResponseMatrixData
      Hn 2 Pos s hs (beta n) (hbeta n) hcut)

/-- Zero frozen coupling makes the constructed initial width exactly zero,
regardless of the earlier orbit coupling beta(n+1). -/
theorem fineFrozenKernelInitialVariation_eq_zero (hzero : beta n = 0) :
    fineFrozenKernelInitialVariation (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r k =
      (fun _ : Link => 0) := by
  have hr : Rate = 0 := by rw [hzero, kernelRightVariationRate_zero]
  funext e
  change Rate * ‖jointTransferEnvelope Hn 2 Pos (beta n) (hbeta n) Orbit‖ = 0
  rw [hr, zero_mul]

/-- Propagation of the exact zero width stays zero; no continuity-in-beta
or continuum statement is inferred from this endpoint test. -/
theorem fineFrozenProfileEnergy_eq_zero_of_kernelRate_zero (R : ResponseData) (hzero : beta n = 0) :
    FrozenProfile = 0 := by
  have h := fineFrozenProfileEnergy_le_kernelVariationEnergy n r k R
  rw [fineFrozenKernelInitialVariation_eq_zero n r k hzero] at h
  simp only [posteriorSixColorVariationProfile, posteriorVariationSchedule_zero,
    periodicHypercubicEvenSpecialUnitaryGroundStateSixSpatialSweepStageOscillationEnergy,
    zero_pow (by decide : (2 : ℕ) ≠ 0), Finset.sum_const_zero, mul_zero] at h
  apply le_antisymm h
  rw [physicalYangMillsSU2AdjacentFineGroundStateSweepStageProfileEnergy_eq_generalProfileEnergy]
  exact sixColorProfileEnergy_nonneg Hn 2 Pos (beta n) (hbeta n) _

end GroundStatePosteriorJoint

end

end MGAP4D.MathlibAnalytic
