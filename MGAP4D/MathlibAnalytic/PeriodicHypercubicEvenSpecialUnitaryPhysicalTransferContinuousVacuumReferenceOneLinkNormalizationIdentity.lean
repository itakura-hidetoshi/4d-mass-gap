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
  rfl

end

end MathlibAnalytic
end MGAP4D
