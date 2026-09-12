import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumGroundStateOneLinkNormalizedMinorization
import MGAP4D.MathlibAnalytic.DoobWeightedConditionalMeasureCenteredVariance
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

noncomputable section

local instance continuousVacuumGroundStateNormalizedVarianceSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance continuousVacuumGroundStateNormalizedVarianceSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance continuousVacuumGroundStateNormalizedVarianceSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance continuousVacuumGroundStateNormalizedVarianceSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance continuousVacuumGroundStateNormalizedVarianceSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- The normalized complete one-link law inherits `L²` observables from Haar
through the sharp normalized majorization. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure_memLp_two
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (X : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hX : MemLp X 2
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))) :
    MemLp X 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure
        H N hN beta hbeta left right target) := by
  let μ := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let ν :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure
      H N hN beta hbeta left right target
  let R : ℝ≥0∞ := ENNReal.ofReal (Real.exp (16 * beta))
  have hRtop : R ≠ ∞ := ne_of_lt ENNReal.ofReal_lt_top
  have hUpper : ν ≤ R • μ := by
    simpa [ν, R, μ] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure_upper_bound
        H N hN beta hbeta left right target
  have hXμ : MemLp X 2 μ := by simpa [μ] using hX
  exact (hXμ.smul_measure hRtop).mono_measure hUpper

/-- Sharp fixed-center squared-residual comparison obtained directly from the
normalized Doeblin minorization.  The Harnack factor is paid exactly once. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure_centeredSquaredResidual_lower_bound
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (X : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (c : ℝ) :
    (ENNReal.ofReal (Real.exp (16 * beta)))⁻¹ *
        doobCenteredSquaredResidual
          (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) X c ≤
      doobCenteredSquaredResidual
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure
          H N hN beta hbeta left right target) X c := by
  let μ := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let ν :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure
      H N hN beta hbeta left right target
  let R : ℝ≥0∞ := ENNReal.ofReal (Real.exp (16 * beta))
  have hLower : R⁻¹ • μ ≤ ν := by
    simpa [ν, R, μ] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure_lower_bound
        H N hN beta hbeta left right target
  calc
    R⁻¹ * doobCenteredSquaredResidual μ X c =
        ∫⁻ x, ENNReal.ofReal ((X x - c) ^ 2) ∂(R⁻¹ • μ) := by
      simpa [doobCenteredSquaredResidual, smul_eq_mul] using
        (lintegral_smul_measure (μ := μ) R⁻¹
          (fun x => ENNReal.ofReal ((X x - c) ^ 2))).symm
    _ ≤ ∫⁻ x, ENNReal.ofReal ((X x - c) ^ 2) ∂ν :=
      lintegral_mono' hLower le_rfl
    _ = doobCenteredSquaredResidual ν X c := rfl

/-- Sharp best-constant residual comparison for the normalized complete
continuous-vacuum one-link law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure_bestConstantSquaredResidual_lower_bound
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (X : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ) :
    (ENNReal.ofReal (Real.exp (16 * beta)))⁻¹ *
        doobBestConstantSquaredResidual
          (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) X ≤
      doobBestConstantSquaredResidual
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure
          H N hN beta hbeta left right target) X := by
  refine le_iInf fun c => ?_
  calc
    (ENNReal.ofReal (Real.exp (16 * beta)))⁻¹ *
        doobBestConstantSquaredResidual
          (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) X ≤
      (ENNReal.ofReal (Real.exp (16 * beta)))⁻¹ *
        doobCenteredSquaredResidual
          (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) X c :=
      mul_le_mul_left'
        (doobBestConstantSquaredResidual_le_centered
          (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) X c)
        (ENNReal.ofReal (Real.exp (16 * beta)))⁻¹
    _ ≤ doobCenteredSquaredResidual
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure
          H N hN beta hbeta left right target) X c :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure_centeredSquaredResidual_lower_bound
        H N hN beta hbeta left right target X c

/-- Sharp normalized one-link conditional-variance comparison.  Relative to
normalized compact Haar probability, the exact complete continuous-vacuum
ground-state one-link law loses only the single Harnack factor
`(ofReal (exp (16 * beta)))⁻¹`, i.e. `exp (-16 * beta)`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure_evariance_lower_bound
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (X : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hX : MemLp X 2
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))) :
    (ENNReal.ofReal (Real.exp (16 * beta)))⁻¹ *
        evariance X
          (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) ≤
      evariance X
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure
          H N hN beta hbeta left right target) := by
  let μ := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let ν :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure
      H N hN beta hbeta left right target
  have hXμ : MemLp X 2 μ := by simpa [μ] using hX
  have hXν : MemLp X 2 ν := by
    simpa [ν] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure_memLp_two
        H N hN beta hbeta left right target X hX
  calc
    (ENNReal.ofReal (Real.exp (16 * beta)))⁻¹ * evariance X μ =
        (ENNReal.ofReal (Real.exp (16 * beta)))⁻¹ *
          doobBestConstantSquaredResidual μ X := by
      rw [doobBestConstantSquaredResidual_eq_evariance μ X hXμ]
    _ ≤ doobBestConstantSquaredResidual ν X := by
      simpa [μ, ν] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumGroundStateSpatialLinkNormalizedFiberMeasure_bestConstantSquaredResidual_lower_bound
          H N hN beta hbeta left right target X
    _ = evariance X ν :=
      doobBestConstantSquaredResidual_eq_evariance ν X hXν

end

end MathlibAnalytic
end MGAP4D
