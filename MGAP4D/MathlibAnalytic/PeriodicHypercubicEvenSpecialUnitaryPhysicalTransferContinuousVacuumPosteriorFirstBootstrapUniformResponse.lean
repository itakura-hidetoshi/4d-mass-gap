import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorHarnackSeedFiniteResolventBound
import Mathlib.Tactic

/-!
# First uniform posterior bootstrap response

PR #5176 supplies a canonical Harnack response seed and hence concrete
posterior non-strict influence data. PR #5177 removes the environment
dependence from the associated finite resolvent:

  w_M(s) <= M * 2^M * width(beta).

PR #5175 gives the terminal block envelope

  ||L_s|| * rho^k * width(beta),

with rho = 1 - delta.  The source local factor itself has the pointwise upper
bound exp(8 beta), so its bounded-continuous norm is also at most exp(8 beta).

Combining these facts yields a fully explicit finite-volume scalar response
radius, independent of the boundary, target, source and source value:

  epsilon_1(H,beta,k)
    =
      [ (width/2) * M * 2^M * width
        + exp(8 beta) * rho^k * width ]
      / exp(-8 beta),

where M = k * n and n is the canonical all-spatial-link schedule length.

This produces the first response matrix after the Harnack seed with no
external posterior-response assumptions.  It is intentionally fixed-volume
and coarse; no strict Dobrushin row sum or volume-uniform bound is claimed.
-/

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance posteriorFirstBootstrapUniformResponseSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Every source local-factor bounded-continuous observable has norm at most
exp(8 beta). -/
theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF_norm_le_exp_eight_mul
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    ‖periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
        H N beta B source sourceValue‖ ≤
      Real.exp (8 * beta) := by
  rw [BoundedContinuousFunction.norm_le (Real.exp_pos _).le]
  intro A
  rw [Real.norm_eq_abs,
    abs_of_pos
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_pos
        H N beta A B source sourceValue)]
  exact
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_le_exp_eight_mul
      H N hN beta hbeta A B source sourceValue

/-- Environment-independent terminal envelope obtained by replacing the source
local-factor norm by exp(8 beta). -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorUniformBlockTerminalCovarianceEnvelope
    (H : ℕ)
    (beta : ℝ)
    (k : ℕ) : ℝ :=
  Real.exp (8 * beta) *
    ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMass
        H beta).toReal ^ k *
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
        beta)

/-- The literal terminal envelope is bounded by the environment-independent
one. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorBlockTerminalCovarianceEnvelope_le_uniform
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (k : ℕ) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorBlockTerminalCovarianceEnvelope
        H N beta B source sourceValue k ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorUniformBlockTerminalCovarianceEnvelope
        H beta k := by
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorBlockTerminalCovarianceEnvelope
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorUniformBlockTerminalCovarianceEnvelope
  apply mul_le_mul_of_nonneg_right
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF_norm_le_exp_eight_mul
      H N hN beta hbeta B source sourceValue)
  exact
    mul_nonneg
      (pow_nonneg ENNReal.toReal_nonneg _)
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth_nonneg
        beta hbeta)

/-- Fully explicit scalar radius for the first Harnack-seed bootstrap update. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapResponseRadius
    (H : ℕ)
    (beta : ℝ)
    (k : ℕ) : ℝ :=
  let M :=
    k *
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
        H).length
  let width :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
      beta
  let rho :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMass
      H beta).toReal
  (((width / 2) * ((M : ℝ) * (2 : ℝ) ^ M * width) +
      Real.exp (8 * beta) * (rho ^ k * width)) /
    Real.exp (-8 * beta))

/-- The explicit first-bootstrap response radius is nonnegative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapResponseRadius_nonneg
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapResponseRadius
        H beta k := by
  let M :=
    k *
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
        H).length
  let width :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
      beta
  let rho :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMass
      H beta).toReal
  have hWidth : 0 ≤ width := by
    dsimp [width]
    exact
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth_nonneg
        beta hbeta
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapResponseRadius
  dsimp [M, width, rho]
  exact
    div_nonneg
      (add_nonneg
        (mul_nonneg
          (div_nonneg hWidth (by norm_num))
          (mul_nonneg
            (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _))
            hWidth))
        (mul_nonneg
          (Real.exp_pos _).le
          (mul_nonneg (pow_nonneg ENNReal.toReal_nonneg _) hWidth)))
      (Real.exp_pos _).le

/-- The concrete Harnack-seed finite bootstrap radius from #5175 is bounded by
the new boundary-independent scalar radius. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFiniteBootstrapResponseRadius_harnackSeed_le_firstBootstrapRadius
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (k : ℕ) :
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFiniteBootstrapResponseRadius
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorHarnackNonstrictInfluenceData
          H N hN beta hbeta B)
        target source
        (k *
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
            H).length)
        (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorBlockTerminalCovarianceEnvelope
          H N beta B source sourceValue k) ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapResponseRadius
        H beta k := by
  let M :=
    k *
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
        H).length
  let width :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
      beta
  let rho :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorRandomScanFullBlockResidualMass
      H beta).toReal
  let terminal :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorBlockTerminalCovarianceEnvelope
      H N beta B source sourceValue k
  have hWidth : 0 ≤ width := by
    dsimp [width]
    exact
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth_nonneg
        beta hbeta
  have hResolvent :
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRandomScanFiniteResolventProfile
          (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorHarnackNonstrictInfluenceData
            H N hN beta hbeta B)
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariation
            beta target)
          M source ≤
        (M : ℝ) * (2 : ℝ) ^ M * width := by
    dsimp [M, width]
    exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorHarnackSeedRandomScanFiniteResolventProfile_le
        H N hN beta hbeta B target source
        (k *
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
            H).length)
  have hTerminal :
      terminal ≤ Real.exp (8 * beta) * (rho ^ k * width) := by
    dsimp [terminal, rho, width]
    exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorBlockTerminalCovarianceEnvelope_le_uniform
        H N hN beta hbeta B source sourceValue k
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFiniteBootstrapResponseRadius
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFiniteBootstrapCovarianceRadius
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapResponseRadius
  dsimp [M, width, rho, terminal]
  rw [div_le_div_iff_of_pos_right (Real.exp_pos (-8 * beta))]
  exact
    add_le_add
      (mul_le_mul_of_nonneg_left hResolvent
        (div_nonneg hWidth (by norm_num)))
      hTerminal

/-- The first bootstrap response is uniformly controlled by the explicit
boundary-independent scalar radius. -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorTargetExpectationResponseBound_of_firstBootstrapRadius
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
      (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapResponseRadius
        H beta k) := by
  have hExact :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorTargetExpectationResponseBound_of_harnackSeed_blockDoeblinTerminalDecay
      H N hN beta hbeta B target source sourceValue k
  have hRadius :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFiniteBootstrapResponseRadius_harnackSeed_le_firstBootstrapRadius
      H N hN beta hbeta B target source sourceValue k
  intro g
  exact (hExact g).trans hRadius

/-- The first Harnack-seed bootstrap update is a concrete global
remote-response matrix, independent of the right boundary. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapRemoteExpectationResponseMatrixData
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ) :
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorRemoteExpectationResponseMatrixData
      H N hN beta hbeta := by
  refine
    { epsilon := fun _target _source =>
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapResponseRadius
          H beta k
      epsilon_nonneg := ?_
      remote_response := ?_ }
  · intro target source
    exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapResponseRadius_nonneg
        H beta hbeta k
  · intro A C target source hNe hRemote hAgree
    exact
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorTargetExpectationResponseBound_of_firstBootstrapRadius
        H N hN beta hbeta A target source (C source) k

/-- Boundarywise non-strict influence data generated by the explicit first
bootstrap response radius. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapNonstrictInfluenceData
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluenceData
      H N hN beta hbeta B :=
  (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapRemoteExpectationResponseMatrixData
    H N hN beta hbeta k).toNonstrictInfluenceData B

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapNonstrictInfluenceData_influence
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (k : ℕ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    (periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapNonstrictInfluenceData
      H N hN beta hbeta k B).influence target source =
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorNonstrictInfluence
        H beta
        (fun _target _source =>
          periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorFirstBootstrapResponseRadius
            H beta k)
        target source := by
  rfl

end

end MathlibAnalytic
end MGAP4D
