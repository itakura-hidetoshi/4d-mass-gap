import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceOneLinkConditionalDensity
import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped ENNReal

noncomputable section

local instance continuousVacuumReferenceOneLinkNormalizationIdentitySpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance continuousVacuumReferenceOneLinkNormalizationIdentitySpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance continuousVacuumReferenceOneLinkNormalizationIdentitySpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance continuousVacuumReferenceOneLinkNormalizationIdentitySpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance continuousVacuumReferenceOneLinkNormalizationIdentitySpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance continuousVacuumReferenceOneLinkNormalizationIdentitySpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- RED test for the exact fiber normalization identity.  Multiplying the
normalized fiber expectation of a nonnegative measurable observable by the
singleton marginal of the reference density should recover the singleton
marginal of the density times that observable. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiber_normalizationIdentity
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (F : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N → ℝ≥0∞)
    (hF : Measurable F) :
    MeasureTheory.lmarginal
        (fun _ : PeriodicHypercubicEvenSpatialSliceLink H =>
          normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
        {fiber}
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceENNRealDensity
          H N hN beta hbeta B target source k g₂)
        A *
      (∫⁻ g,
        F (Function.update A fiber g)
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B target source fiber k g₂ A) =
      MeasureTheory.lmarginal
        (fun _ : PeriodicHypercubicEvenSpatialSliceLink H =>
          normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
        {fiber}
        (fun X =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceENNRealDensity
              H N hN beta hbeta B target source k g₂ X * F X)
        A := by
  classical
  let μ := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  let ρ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceENNRealDensity
      H N hN beta hbeta B target source k g₂
  let m := MeasureTheory.lmarginal
    (fun _ : PeriodicHypercubicEvenSpatialSliceLink H => μ)
    {fiber} ρ A
  let obs : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ≥0∞ :=
    fun g => F (Function.update A fiber g)
  let w : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
      H N hN beta hbeta B target source fiber k g₂ A
  have hwInt : Integrable w μ := by
    simpa [μ, w] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight_integrable
        H N hN beta hbeta B target source fiber k g₂ A
  have hρ : AEMeasurable (fun g => ρ (Function.update A fiber g)) μ := by
    change AEMeasurable (fun g => ENNReal.ofReal (w g)) μ
    exact ENNReal.measurable_ofReal.comp_aemeasurable hwInt.aestronglyMeasurable.aemeasurable
  have hobs : AEMeasurable obs μ := by
    simpa [obs] using (hF.comp (measurable_update A)).aemeasurable
  have hmEq :
      m = ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberPartitionFunction
          H N hN beta hbeta B target source fiber k g₂ A) := by
    symm
    simpa [m, μ, ρ] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberPartitionFunction_ofReal_eq_lmarginal_singleton
        H N hN beta hbeta B target source fiber k g₂ A
  have hmZero : m ≠ 0 := by
    rw [hmEq, ENNReal.ofReal_ne_zero_iff]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberPartitionFunction_pos
        H N hN beta hbeta B target source fiber k g₂ A
  have hmTop : m ≠ ∞ := by
    rw [hmEq]
    exact ENNReal.ofReal_ne_top
  change m *
      (∫⁻ g, obs g
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B target source fiber k g₂ A) = _
  rw [MeasureTheory.lmarginal_singleton]
  change m *
      (∫⁻ g, obs g
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B target source fiber k g₂ A) =
    ∫⁻ g, ρ (Function.update A fiber g) * obs g ∂μ
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_eq_withDensity_lmarginal
    H N hN beta hbeta B target source fiber k g₂ A]
  change m *
      (∫⁻ g, obs g ∂μ.withDensity
        (fun g => ρ (Function.update A fiber g) / m)) =
    ∫⁻ g, ρ (Function.update A fiber g) * obs g ∂μ
  rw [lintegral_withDensity_eq_lintegral_mul₀ (hρ.div_const m) hobs]
  simp only [Pi.mul_apply, div_eq_mul_inv]
  rw [show
    (fun g => ρ (Function.update A fiber g) * m⁻¹ * obs g) =
      (fun g => (ρ (Function.update A fiber g) * obs g) * m⁻¹) by
        funext g
        ac_rfl]
  rw [lintegral_mul_const'' _ (hρ.mul hobs)]
  calc
    m * ((∫⁻ g, ρ (Function.update A fiber g) * obs g ∂μ) * m⁻¹) =
        (∫⁻ g, ρ (Function.update A fiber g) * obs g ∂μ) * (m * m⁻¹) := by
      ac_rfl
    _ = ∫⁻ g, ρ (Function.update A fiber g) * obs g ∂μ := by
      rw [ENNReal.mul_inv_cancel hmZero hmTop, mul_one]

end

end MathlibAnalytic
end MGAP4D
