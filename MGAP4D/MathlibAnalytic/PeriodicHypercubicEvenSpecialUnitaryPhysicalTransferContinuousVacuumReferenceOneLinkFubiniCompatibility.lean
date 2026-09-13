import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceOneLinkNormalizationIdentity
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceProbability
import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped ENNReal

noncomputable section

local instance continuousVacuumReferenceOneLinkFubiniCompatibilitySpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance continuousVacuumReferenceOneLinkFubiniCompatibilitySpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance continuousVacuumReferenceOneLinkFubiniCompatibilitySpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance continuousVacuumReferenceOneLinkFubiniCompatibilitySpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance continuousVacuumReferenceOneLinkFubiniCompatibilitySpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance continuousVacuumReferenceOneLinkFubiniCompatibilitySpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

private theorem continuousVacuumReferenceENNRealDensity_measurable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Measurable
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceENNRealDensity
        H N hN beta hbeta B target source k g₂) := by
  have hOmega : Continuous
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
        H N hN beta hbeta) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative_continuous
      H N hN beta hbeta
  have hLocal : Continuous
      (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
          H N beta A B target g₂) :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_continuous_left
      H N beta B target g₂
  have hKernelMeas : Measurable
      (fun A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
        periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
          H N beta A (Function.update B source k)) := by
    exact
      ((periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
        H N beta).comp
        (Continuous.prodMk continuous_id continuous_const)).measurable
  have hwMeas : Measurable
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
        H N hN beta hbeta B target source k g₂) := by
    unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
    exact (hOmega.measurable.mul hLocal.measurable).mul hKernelMeas
  change Measurable
    (fun A => ENNReal.ofReal
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
        H N hN beta hbeta B target source k g₂ A))
  exact ENNReal.measurable_ofReal.comp hwMeas

private theorem continuousVacuumReferenceOneLinkFiberExpectation_measurable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ≥0∞)
    (hF : Measurable F) :
    Measurable
      (fun A =>
        ∫⁻ g,
          F (Function.update A fiber g)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
            H N hN beta hbeta B target source fiber k g₂ A) := by
  let μCoord :
      PeriodicHypercubicEvenSpatialSliceLink H →
        Measure (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    fun _ => normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let ρ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ≥0∞ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceENNRealDensity
      H N hN beta hbeta B target source k g₂
  let E : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ≥0∞ :=
    fun A =>
      ∫⁻ g,
        F (Function.update A fiber g)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B target source fiber k g₂ A
  let m : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ≥0∞ :=
    MeasureTheory.lmarginal μCoord {fiber} ρ
  let num : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ≥0∞ :=
    MeasureTheory.lmarginal μCoord {fiber} (fun A => ρ A * F A)
  have hρ : Measurable ρ := by
    dsimp [ρ]
    exact continuousVacuumReferenceENNRealDensity_measurable
      H N hN beta hbeta B target source k g₂
  have hmMeas : Measurable m := by
    dsimp [m]
    exact hρ.lmarginal μCoord
  have hnumMeas : Measurable num := by
    dsimp [num]
    exact (hρ.mul hF).lmarginal μCoord
  have hEeq : E = fun A => num A / m A := by
    funext A
    have hmEq :
        m A = ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberPartitionFunction
            H N hN beta hbeta B target source fiber k g₂ A) := by
      symm
      simpa [m, μCoord, ρ] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberPartitionFunction_ofReal_eq_lmarginal_singleton
          H N hN beta hbeta B target source fiber k g₂ A
    have hmZero : m A ≠ 0 := by
      rw [hmEq, ENNReal.ofReal_ne_zero_iff]
      exact
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberPartitionFunction_pos
          H N hN beta hbeta B target source fiber k g₂ A
    have hmTop : m A ≠ ∞ := by
      rw [hmEq]
      exact ENNReal.ofReal_ne_top
    have hnorm :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiber_normalizationIdentity
        H N hN beta hbeta B target source fiber k g₂ A F hF
    change m A * E A = num A at hnorm
    calc
      E A = E A * 1 := by simp
      _ = E A * (m A * (m A)⁻¹) := by
        rw [ENNReal.mul_inv_cancel hmZero hmTop]
      _ = (m A * E A) * (m A)⁻¹ := by ac_rfl
      _ = num A * (m A)⁻¹ := by rw [hnorm]
      _ = num A / m A := by rw [div_eq_mul_inv]
  have hEMeas : Measurable E := by
    rw [hEeq]
    exact hnumMeas.div hmMeas
  simpa [E] using hEMeas

private theorem continuousVacuumReferenceENNRealDensity_lintegral_oneLinkFiber
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ≥0∞)
    (hF : Measurable F) :
    (∫⁻ A,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceENNRealDensity
            H N hN beta hbeta B target source k g₂ A *
          (∫⁻ g,
            F (Function.update A fiber g)
            ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
              H N hN beta hbeta B target source fiber k g₂ A)
        ∂periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N) =
      ∫⁻ A,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceENNRealDensity
            H N hN beta hbeta B target source k g₂ A * F A
        ∂periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N := by
  let μCoord :
      PeriodicHypercubicEvenSpatialSliceLink H →
        Measure (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
    fun _ => normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let ρ : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ≥0∞ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceENNRealDensity
      H N hN beta hbeta B target source k g₂
  let E : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ≥0∞ :=
    fun A =>
      ∫⁻ g,
        F (Function.update A fiber g)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B target source fiber k g₂ A
  have hρ : Measurable ρ := by
    dsimp [ρ]
    exact continuousVacuumReferenceENNRealDensity_measurable
      H N hN beta hbeta B target source k g₂
  have hE : Measurable E := by
    dsimp [E]
    exact continuousVacuumReferenceOneLinkFiberExpectation_measurable
      H N hN beta hbeta B target source fiber k g₂ F hF
  change
    (∫⁻ A, ρ A * E A ∂Measure.pi μCoord) =
      ∫⁻ A, ρ A * F A ∂Measure.pi μCoord
  apply MeasureTheory.lintegral_eq_of_lmarginal_eq
    (μ := μCoord) {fiber} (hρ.mul hE) (hρ.mul hF)
  funext A
  rw [MeasureTheory.lmarginal_singleton, MeasureTheory.lmarginal_singleton]
  have hEupdate
      (g₀ : Matrix.specialUnitaryGroup (Fin N) ℂ) :
      E (Function.update A fiber g₀) = E A := by
    dsimp [E]
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_update_fiber
        H N hN beta hbeta B target source fiber k g₂ A g₀]
    apply lintegral_congr
    intro g
    simp
  have hρFiber : AEMeasurable
      (fun g => ρ (Function.update A fiber g)) (μCoord fiber) :=
    (hρ.comp (measurable_update A)).aemeasurable
  have hnorm :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiber_normalizationIdentity
      H N hN beta hbeta B target source fiber k g₂ A F hF
  rw [MeasureTheory.lmarginal_singleton, MeasureTheory.lmarginal_singleton] at hnorm
  change
    (∫⁻ g, ρ (Function.update A fiber g) ∂μCoord fiber) * E A =
      ∫⁻ g, ρ (Function.update A fiber g) * F (Function.update A fiber g) ∂μCoord fiber
    at hnorm
  calc
    (∫⁻ g, ρ (Function.update A fiber g) * E (Function.update A fiber g) ∂μCoord fiber) =
        ∫⁻ g, ρ (Function.update A fiber g) * E A ∂μCoord fiber := by
      apply lintegral_congr
      intro g
      rw [hEupdate g]
    _ = (∫⁻ g, ρ (Function.update A fiber g) ∂μCoord fiber) * E A := by
      rw [lintegral_mul_const'' (E A) hρFiber]
    _ = ∫⁻ g, ρ (Function.update A fiber g) * F (Function.update A fiber g) ∂μCoord fiber :=
      hnorm

/-- The normalized continuous-vacuum reference law is invariant under
resampling one spatial link from the exact normalized literal reference fiber.

The proof first lifts the pointwise normalization identity to the full product
Haar law by a singleton-marginal Fubini argument, and only then cancels the
global reference normalization.  This is a full-law heat-bath compatibility
statement; it does not identify the fiber family as a regular conditional
distribution. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure_lintegral_oneLinkFiber
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ≥0∞)
    (hF : Measurable F) :
    (∫⁻ A,
        (∫⁻ g,
          F (Function.update A fiber g)
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
            H N hN beta hbeta B target source fiber k g₂ A)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
          H N hN beta hbeta B target source k g₂) =
      ∫⁻ A, F A
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure
          H N hN beta hbeta B target source k g₂ := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let w :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
      H N hN beta hbeta B target source k g₂
  let ρ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceENNRealDensity
      H N hN beta hbeta B target source k g₂
  let E : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ≥0∞ :=
    fun A =>
      ∫⁻ g,
        F (Function.update A fiber g)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B target source fiber k g₂ A
  have hρ : Measurable ρ := by
    dsimp [ρ]
    exact continuousVacuumReferenceENNRealDensity_measurable
      H N hN beta hbeta B target source k g₂
  have hE : Measurable E := by
    dsimp [E]
    exact continuousVacuumReferenceOneLinkFiberExpectation_measurable
      H N hN beta hbeta B target source fiber k g₂ F hF
  have hUnnormalized :
      (∫⁻ A, ρ A * E A ∂μ) = ∫⁻ A, ρ A * F A ∂μ := by
    simpa [μ, ρ, E] using
      continuousVacuumReferenceENNRealDensity_lintegral_oneLinkFiber
        H N hN beta hbeta B target source fiber k g₂ F hF
  have hwInt : Integrable w μ := by
    simpa [μ, w] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight_integrable
        H N hN beta hbeta B target source k g₂
  have hwNonneg : ∀ᵐ A ∂μ, 0 ≤ w A :=
    ae_of_all μ fun A => by
      dsimp [w]
      exact
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight_pos
          H N hN beta hbeta B target source k g₂ A).le
  let mass : ℝ≥0∞ := doobWeightMass μ ρ
  have hMassEq : mass = ENNReal.ofReal (∫ A, w A ∂μ) := by
    change doobWeightMass μ (fun A => ENNReal.ofReal (w A)) =
      ENNReal.ofReal (∫ A, w A ∂μ)
    exact realIntegralWeighted_doobWeightMass_eq_ofReal_integral μ w hwInt hwNonneg
  have hRealMassPos : 0 < ∫ A, w A ∂μ := by
    simpa [μ, w,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePartitionFunction] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePartitionFunction_pos
        H N hN beta hbeta B target source k g₂
  have hMassZero : mass ≠ 0 := by
    rw [hMassEq, ENNReal.ofReal_ne_zero_iff]
    exact hRealMassPos
  have hMassTop : mass ≠ ∞ := by
    rw [hMassEq]
    exact ENNReal.ofReal_ne_top
  have hScaledE :
      mass * (∫⁻ A, E A ∂doobWeightedMeasure μ ρ) =
        ∫⁻ A, ρ A * E A ∂μ := by
    simpa [mass] using
      (doobWeightMass_mul_lintegral_doobWeightedMeasure
        μ ρ E hρ.aemeasurable hE.aemeasurable hMassZero hMassTop)
  have hScaledF :
      mass * (∫⁻ A, F A ∂doobWeightedMeasure μ ρ) =
        ∫⁻ A, ρ A * F A ∂μ := by
    simpa [mass] using
      (doobWeightMass_mul_lintegral_doobWeightedMeasure
        μ ρ F hρ.aemeasurable hF.aemeasurable hMassZero hMassTop)
  have hScaled :
      mass * (∫⁻ A, E A ∂doobWeightedMeasure μ ρ) =
        mass * (∫⁻ A, F A ∂doobWeightedMeasure μ ρ) := by
    rw [hScaledE, hScaledF]
    exact hUnnormalized
  have hNormalized :
      (∫⁻ A, E A ∂doobWeightedMeasure μ ρ) =
        ∫⁻ A, F A ∂doobWeightedMeasure μ ρ := by
    calc
      (∫⁻ A, E A ∂doobWeightedMeasure μ ρ) =
          (mass * (∫⁻ A, E A ∂doobWeightedMeasure μ ρ)) * mass⁻¹ := by
        calc
          (∫⁻ A, E A ∂doobWeightedMeasure μ ρ) =
              (∫⁻ A, E A ∂doobWeightedMeasure μ ρ) * 1 := by simp
          _ = (∫⁻ A, E A ∂doobWeightedMeasure μ ρ) * (mass * mass⁻¹) := by
            rw [ENNReal.mul_inv_cancel hMassZero hMassTop]
          _ = (mass * (∫⁻ A, E A ∂doobWeightedMeasure μ ρ)) * mass⁻¹ := by
            ac_rfl
      _ = (mass * (∫⁻ A, F A ∂doobWeightedMeasure μ ρ)) * mass⁻¹ := by
        rw [hScaled]
      _ = ∫⁻ A, F A ∂doobWeightedMeasure μ ρ := by
        calc
          (mass * (∫⁻ A, F A ∂doobWeightedMeasure μ ρ)) * mass⁻¹ =
              (∫⁻ A, F A ∂doobWeightedMeasure μ ρ) * (mass * mass⁻¹) := by
            ac_rfl
          _ = ∫⁻ A, F A ∂doobWeightedMeasure μ ρ := by
            rw [ENNReal.mul_inv_cancel hMassZero hMassTop, mul_one]
  simpa [E, μ, ρ,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceENNRealDensity,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceProbabilityMeasure,
    realIntegralWeightedProbabilityMeasure] using hNormalized

end

end MathlibAnalytic
end MGAP4D
