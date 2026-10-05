import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorTerminalCovarianceDecay
import Mathlib.Tactic

/-!
# Harnack seed for the continuous-vacuum posterior response bootstrap

The terminal covariance obstruction is now closed by the posterior Doeblin
block contraction.  To start the recursive response/influence bootstrap
without external response assumptions, this file constructs a canonical
finite-volume seed directly from the one-link Harnack interval.

Both the base posterior target expectation and the remote source-re-tilted
target expectation lie in

  [exp(-8 beta), exp(8 beta)].

Hence their discrepancy is bounded by

  width(beta) = exp(8 beta) - exp(-8 beta).

This uniform bound gives concrete
`PosteriorRemoteExpectationResponseMatrixData`, and therefore concrete
posterior non-strict influence data `D₀` at every right boundary.  The
terminal-decay theorem can then be instantiated with `D₀` with no external
response certificate.

This is a seed only.  No strict Dobrushin row-sum bound or volume-uniform
contraction is asserted.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance posteriorHarnackResponseSeedTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance posteriorHarnackResponseSeedCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance posteriorHarnackResponseSeedSecondCountable
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance posteriorHarnackResponseSeedMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance posteriorHarnackResponseSeedBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance posteriorHarnackResponseSeedSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The continuous-vacuum one-link update ratio is at most exp(8 beta). -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuum_update_ratio_le_exp_eight_mul
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta (Function.update B target g) /
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta B ≤
      Real.exp (8 * beta) := by
  have hB :
      0 <
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
          H N hN beta hbeta B :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_pos
      H N hN beta hbeta B
  apply (div_le_iff₀ hB).2
  have hH :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuousVacuumReplaceLink_le_exp_eight_mul
      H N hN beta hbeta B target g (B target)
  simpa [
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink,
    mul_comm] using hH

/-- The base posterior target expectation lies below exp(8 beta). -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorTargetExpectation_le_exp_eight_mul
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorTargetExpectation
        H N hN beta hbeta B target g ≤
      Real.exp (8 * beta) := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorTargetExpectation_eq_vacuum_ratio]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuum_update_ratio_le_exp_eight_mul
      H N hN beta hbeta B target g

/-- Under remote source separation, the source-re-tilted target expectation
also lies below exp(8 beta). -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSourceTiltedTargetExpectation_le_exp_eight_mul
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue g : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hNe : source ≠ target)
    (hRemote :
      ¬ periodicHypercubicEvenSpatialSlicePlaquetteLocal H target source) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSourceTiltedTargetExpectation
        H N hN beta hbeta B target source sourceValue g ≤
      Real.exp (8 * beta) := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSourceTiltedTargetExpectation_eq_updated_vacuum_ratio
      H N hN beta hbeta B target source sourceValue g hNe hRemote]
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuum_update_ratio_le_exp_eight_mul
      H N hN beta hbeta
      (Function.update B source sourceValue) target g

/-- Harnack alone gives a uniform ordinary remote-source posterior response
bound by the full one-link Harnack width. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorTargetExpectationResponseBound_harnackWidth
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (hNe : source ≠ target)
    (hRemote :
      ¬ periodicHypercubicEvenSpatialSlicePlaquetteLocal H target source) :
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorTargetExpectationResponseBound
      H N hN beta hbeta B target source sourceValue
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
        beta) := by
  intro g
  let x :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorTargetExpectation
      H N hN beta hbeta B target g
  let y :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSourceTiltedTargetExpectation
      H N hN beta hbeta B target source sourceValue g
  have hxLower :
      Real.exp (-8 * beta) ≤ x := by
    simpa [x] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorTargetExpectation_exp_neg_eight_mul_le
        H N hN beta hbeta B target g
  have hxUpper :
      x ≤ Real.exp (8 * beta) := by
    simpa [x] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorTargetExpectation_le_exp_eight_mul
        H N hN beta hbeta B target g
  have hyLower :
      Real.exp (-8 * beta) ≤ y := by
    simpa [y] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSourceTiltedTargetExpectation_exp_neg_eight_mul_le
        H N hN beta hbeta B target source sourceValue g hNe hRemote
  have hyUpper :
      y ≤ Real.exp (8 * beta) := by
    simpa [y] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSourceTiltedTargetExpectation_le_exp_eight_mul
        H N hN beta hbeta B target source sourceValue g hNe hRemote
  unfold
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
  change |x - y| ≤ Real.exp (8 * beta) - Real.exp (-8 * beta)
  rw [abs_le]
  constructor <;> linarith

/-- Canonical global remote-response seed obtained from the Harnack interval. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorHarnackRemoteExpectationResponseMatrixData
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteExpectationResponseMatrixData
      H N hN beta hbeta := by
  refine
    { epsilon := fun _target _source =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
          beta
      epsilon_nonneg := ?_
      remote_response := ?_ }
  · intro target source
    exact
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth_nonneg
        beta hbeta
  · intro A C target source hNe hRemote hAgree
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorTargetExpectationResponseBound_harnackWidth
        H N hN beta hbeta A target source (C source) hNe hRemote

/-- Canonical non-strict posterior influence data generated from the Harnack
response seed, available at every right boundary with no external response
assumption. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorHarnackNonstrictInfluenceData
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
      H N hN beta hbeta B :=
  (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorHarnackRemoteExpectationResponseMatrixData
    H N hN beta hbeta).toNonstrictInfluenceData B

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorHarnackNonstrictInfluenceData_influence
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorHarnackNonstrictInfluenceData
      H N hN beta hbeta B).influence target source =
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluence
        H beta
        (fun _target _source =>
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
            beta)
        target source := by
  rfl

/-- The block-Doeblin terminal-decay response theorem is now available from a
fully canonical seed, with no externally supplied posterior influence data. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorTargetExpectationResponseBound_of_harnackSeed_blockDoeblinTerminalDecay
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (k : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorTargetExpectationResponseBound
      H N hN beta hbeta B target source sourceValue
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFiniteBootstrapResponseRadius
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorHarnackNonstrictInfluenceData
          H N hN beta hbeta B)
        target source
        (k *
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
            H).length)
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorBlockTerminalCovarianceEnvelope
          H N beta B source sourceValue k)) := by
  exact
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorTargetExpectationResponseBound_of_blockDoeblinTerminalDecay
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorHarnackNonstrictInfluenceData
        H N hN beta hbeta B)
      target source sourceValue k

end

end MathlibAnalytic
end MGAP4D
