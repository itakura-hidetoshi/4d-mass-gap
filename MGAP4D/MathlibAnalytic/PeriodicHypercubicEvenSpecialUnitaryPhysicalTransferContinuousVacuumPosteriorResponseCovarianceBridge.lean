import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumPosteriorNonstrictInfluenceFiniteResolvent
import Mathlib.Tactic

/-!
# Posterior remote response as a local covariance

The remaining remote expectation response is a comparison between the posterior
law pi_B and the source-updated posterior pi_{B[source := h]}.

PR #5156 already proves that the updated posterior is exactly the local
exponential re-tilt of pi_B by the positive source-local Wilson factor L_s.
This file makes the resulting response algebra explicit:

  E_{pi_{B[s:=h]}} F_t - E_{pi_B} F_t
    = Cov_{pi_B}(F_t, L_s) / E_{pi_B} L_s.

The source-factor mean has the volume-uniform lower bound exp(-8 beta), so any
posterior covariance bound K immediately gives the ordinary response radius

  epsilon = K / exp(-8 beta).

We also package the target/source local factors as bounded continuous
observables with exact one-coordinate variation support.  Their declared
nonzero variation is the Harnack width

  exp(8 beta) - exp(-8 beta).

This is the direct bridge from the finite posterior Dobrushin resolvent to the
response matrix epsilon.  No covariance decay, strict row-sum bound, infinite
resolvent, posterior fixed point, heat-bath-time / Euclidean-time
identification, H1-D5 exact descent, or complete Yang--Mills mass-gap claim is
introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance posteriorResponseCovarianceTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance posteriorResponseCovarianceCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance posteriorResponseCovarianceSecondCountable
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance posteriorResponseCovarianceMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance posteriorResponseCovarianceBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Posterior mean of a bounded-continuous spatial-slice observable. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (F : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ) :
    ℝ :=
  ∫ A, F A
    ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
      H N hN beta hbeta B

/-- Posterior covariance of two bounded-continuous spatial-slice observables. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (F G : BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ) :
    ℝ :=
  (∫ A, F A * G A
      ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
        H N hN beta hbeta B) -
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
        H N hN beta hbeta B F *
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
        H N hN beta hbeta B G

/-- As a function of the posterior integration variable A, a right-boundary
local update factor is continuous and depends only on A at the named target
coordinate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_continuous_left
    (H N : ℕ)
    (beta : ℝ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Continuous
      (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A B target g) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
  apply Real.continuous_exp.comp
  apply continuous_const.mul
  have hRelativeG :
      Continuous
        (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
          (A target)⁻¹ * g) := by
    fun_prop
  have hRelativeB :
      Continuous
        (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
          (A target)⁻¹ * B target) := by
    fun_prop
  have hEnergyG :
      Continuous
        (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
          specialUnitaryWilsonPlaquetteEnergy N ((A target)⁻¹ * g)) :=
    (continuous_specialUnitaryWilsonPlaquetteEnergy N).comp hRelativeG
  have hEnergyB :
      Continuous
        (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
          specialUnitaryWilsonPlaquetteEnergy N ((A target)⁻¹ * B target)) :=
    (continuous_specialUnitaryWilsonPlaquetteEnergy N).comp hRelativeB
  exact (hEnergyG.sub hEnergyB).add continuous_const

/-- Bounded-continuous carrier of the exact posterior local factor. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
    (H N : ℕ)
    (beta : ℝ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    BoundedContinuousFunction
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) ℝ :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun A =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A B target g,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_continuous_left
        H N beta B target g⟩

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF_apply
    (H N : ℕ)
    (beta : ℝ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
        H N beta B target g A =
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
        H N beta A B target g :=
  rfl

/-- Volume-independent oscillation width of one posterior local factor. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
    (beta : ℝ) : ℝ :=
  Real.exp (8 * beta) - Real.exp (-8 * beta)

/-- The local-factor Harnack width is nonnegative for beta >= 0. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth_nonneg
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
        beta := by
  unfold
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
  exact sub_nonneg.mpr
    (Real.exp_le_exp.mpr (by linarith))

/-- Exact one-coordinate variation profile of a posterior local factor. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariation
    {H : ℕ}
    (beta : ℝ)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ := by
  classical
  exact if source = target then
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
      beta
  else 0

/-- The local-factor variation profile is nonnegative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariation_nonneg
    {H : ℕ}
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariation
        beta target source := by
  classical
  unfold
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariation
  by_cases h : source = target
  · simp [h,
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth_nonneg
        beta hbeta]
  · simp [h]

/-- The bounded-continuous local factor has exactly one-coordinate declared
variation support. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationBound
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorLinkVariationBound
      H N
      (fun A =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
          H N beta B target g A) := by
  classical
  refine
    { variation :=
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariation
          beta target
      variation_nonneg :=
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariation_nonneg
          beta hbeta target
      variation_bound := ?_ }
  intro source A C hAgree
  by_cases h : source = target
  · subst source
    have hALower :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_exp_neg_eight_mul_le
        H N hN beta hbeta A B target g
    have hAUpper :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_le_exp_eight_mul
        H N hN beta hbeta A B target g
    have hCLower :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_exp_neg_eight_mul_le
        H N hN beta hbeta C B target g
    have hCUpper :=
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_le_exp_eight_mul
        H N hN beta hbeta C B target g
    simp only [
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF_apply]
    change
      |periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A B target g -
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta C B target g| ≤
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
          beta
    unfold
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariationWidth
    rw [abs_le]
    constructor <;> linarith
  · have hTarget : A target = C target :=
      hAgree target (Ne.symm h)
    have hEq :
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta A B target g =
          periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
            H N beta C B target g := by
      unfold
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
      rw [hTarget]
    simp only [
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF_apply,
      hEq, sub_self, abs_zero]
    unfold
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorVariation
    simp [h]

/-- The posterior mean of a local factor has the uniform lower floor
exp(-8 beta). -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean_localFactor_exp_neg_eight_mul_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Real.exp (-8 * beta) ≤
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
        H N hN beta hbeta B
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
          H N beta B source sourceValue) := by
  let mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
      H N hN beta hbeta B
  let L :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
      H N beta B source sourceValue
  letI : IsProbabilityMeasure mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure_isProbabilityMeasure
      H N hN beta hbeta B
  have hLInt : Integrable (fun A => L A) mu :=
    L.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hConstInt :
      Integrable
        (fun _A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
          Real.exp (-8 * beta))
        mu :=
    integrable_const _
  unfold
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
  change
    Real.exp (-8 * beta) ≤ ∫ A, L A ∂mu
  calc
    Real.exp (-8 * beta) =
        ∫ _A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
          Real.exp (-8 * beta) ∂mu := by simp
    _ ≤ ∫ A, L A ∂mu := by
      apply integral_mono hConstInt hLInt
      intro A
      simpa [L] using
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_exp_neg_eight_mul_le
          H N hN beta hbeta A B source sourceValue

/-- The source-local tilted target expectation is exactly the posterior
target/source covariance divided by the source-factor mean. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSourceTiltedTargetExpectation_sub_targetExpectation_eq_covariance_div_sourceMean
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSourceTiltedTargetExpectation
          H N hN beta hbeta B target source sourceValue g -
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorTargetExpectation
          H N hN beta hbeta B target g =
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
          H N hN beta hbeta B
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
            H N beta B target g)
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
            H N beta B source sourceValue) /
        periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
          H N hN beta hbeta B
          (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
            H N beta B source sourceValue) := by
  let mu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorMeasure
      H N hN beta hbeta B
  let F :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
      H N beta B target g
  let L :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
      H N beta B source sourceValue
  let Z : ℝ := ∫ A, L A ∂mu
  have hZLower :
      Real.exp (-8 * beta) ≤ Z := by
    simpa [Z, mu, L,
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean] using
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean_localFactor_exp_neg_eight_mul_le
        H N hN beta hbeta B source sourceValue
  have hZPos : 0 < Z :=
    lt_of_lt_of_le (Real.exp_pos _) hZLower
  have hZNe : Z ≠ 0 := ne_of_gt hZPos
  have hTilt :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSourceTiltedTargetExpectation
          H N hN beta hbeta B target source sourceValue g =
        (∫ A, F A * L A ∂mu) / Z := by
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSourceTiltedTargetExpectation
    rw [MeasureTheory.integral_tilted]
    simp_rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSourceLocalLogTilt,
      Real.exp_log
        (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_pos
          H N beta _ B source sourceValue),
      smul_eq_mul]
    change
      (∫ A,
          (L A / Z) * F A ∂mu) =
        (∫ A, F A * L A ∂mu) / Z
    simp_rw [div_mul_eq_mul_div]
    rw [integral_div]
    congr 1
    apply integral_congr_ae
    filter_upwards with A
    ring
  rw [hTilt]
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorTargetExpectation
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
  change
    (∫ A, F A * L A ∂mu) / Z - (∫ A, F A ∂mu) =
      ((∫ A, F A * L A ∂mu) -
        (∫ A, F A ∂mu) * (∫ A, L A ∂mu)) / Z
  change
    (∫ A, F A * L A ∂mu) / Z - (∫ A, F A ∂mu) =
      ((∫ A, F A * L A ∂mu) -
        (∫ A, F A ∂mu) * Z) / Z
  field_simp [hZNe]

/-- Any uniform posterior covariance bound K gives the ordinary remote
expectation-response radius K / exp(-8 beta). -/
theorem
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorTargetExpectationResponseBound_of_covariance
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (sourceValue : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (K : ℝ)
    (hK : 0 ≤ K)
    (hCov :
      ∀ g : Matrix.specialUnitaryGroup (Fin N) ℂ,
        |periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
            H N hN beta hbeta B
            (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
              H N beta B target g)
            (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
              H N beta B source sourceValue)| ≤ K) :
    PeriodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorTargetExpectationResponseBound
      H N hN beta hbeta B target source sourceValue
      (K / Real.exp (-8 * beta)) := by
  intro g
  let sourceMean :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean
      H N hN beta hbeta B
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
        H N beta B source sourceValue)
  let cov :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorCovariance
      H N hN beta hbeta B
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
        H N beta B target g)
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactorBCF
        H N beta B source sourceValue)
  have hMeanLower :
      Real.exp (-8 * beta) ≤ sourceMean := by
    simpa [sourceMean] using
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumPosteriorMean_localFactor_exp_neg_eight_mul_le
        H N hN beta hbeta B source sourceValue
  have hm : 0 < Real.exp (-8 * beta) := Real.exp_pos _
  have hMeanPos : 0 < sourceMean :=
    lt_of_lt_of_le hm hMeanLower
  have hIdentity :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSourceTiltedTargetExpectation_sub_targetExpectation_eq_covariance_div_sourceMean
      H N hN beta hbeta B target source sourceValue g
  have hCovG : |cov| ≤ K := by
    simpa [cov] using hCov g
  rw [abs_sub_comm]
  rw [hIdentity]
  change |cov / sourceMean| ≤ K / Real.exp (-8 * beta)
  rw [abs_div, abs_of_pos hMeanPos]
  apply (div_le_div_iff₀ hMeanPos hm).2
  calc
    |cov| * Real.exp (-8 * beta) ≤
        K * Real.exp (-8 * beta) :=
      mul_le_mul_of_nonneg_right hCovG hm.le
    _ ≤ K * sourceMean :=
      mul_le_mul_of_nonneg_left hMeanLower hK

end

end MathlibAnalytic
end MGAP4D
