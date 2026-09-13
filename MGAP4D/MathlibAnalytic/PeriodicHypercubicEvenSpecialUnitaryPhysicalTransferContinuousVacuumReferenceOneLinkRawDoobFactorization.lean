import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceOneLinkFiber
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumDoobVariance
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open ProbabilityTheory
open scoped ENNReal

noncomputable section

local instance continuousVacuumReferenceOneLinkRawDoobSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance continuousVacuumReferenceOneLinkRawDoobSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance continuousVacuumReferenceOneLinkRawDoobSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance continuousVacuumReferenceOneLinkRawDoobSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance continuousVacuumReferenceOneLinkRawDoobSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance continuousVacuumReferenceOneLinkRawDoobSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The non-vacuum part of the C5 literal reference fiber density.  This is a
one-slab fiber weight, not the full four-dimensional Wilson single-link Gibbs
weight. -/
def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkRawWeight
    (H N : ℕ)
    (beta : ℝ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  let A' :=
    periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
      H N A fiber g
  periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
      H N beta A' B target g₂ *
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
      H N beta A' (Function.update B source k)

/-- The C5 raw one-link weight is continuous, hence Haar-integrable. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkRawWeight_integrable
    (H N : ℕ)
    (beta : ℝ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    Integrable
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkRawWeight
        H N beta B target source fiber k g₂ A)
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) := by
  let replace : Matrix.specialUnitaryGroup (Fin N) ℂ →
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
    fun g =>
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
        H N A fiber g
  have hReplace : Continuous replace := by
    simpa [replace] using
      periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink_continuous
        H N A fiber
  have hLocal : Continuous (fun g =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor
        H N beta (replace g) B target g₂) :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_continuous_left
      H N beta B target g₂).comp hReplace
  have hKernel : Continuous (fun g =>
      periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
        H N beta (replace g) (Function.update B source k)) :=
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_continuous
      H N beta).comp (hReplace.prodMk continuous_const)
  have hCont := hLocal.mul hKernel
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkRawWeight,
    replace] using
    hCont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The C5 raw one-link weight is strictly positive. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkRawWeight_pos
    (H N : ℕ)
    (beta : ℝ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    0 <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkRawWeight
        H N beta B target source fiber k g₂ A g := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkRawWeight
  exact mul_pos
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabRightTargetLocalFactor_pos
      H N beta _ B target g₂)
    (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_pos
      H N beta _ (Function.update B source k))

/-- Normalized C5 raw one-link law obtained from `local × kernel` before the
continuous-vacuum Doob factor is inserted. -/
def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkRawProbabilityMeasure
    (H N : ℕ)
    (beta : ℝ)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    Measure (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  realIntegralWeightedProbabilityMeasure
    (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkRawWeight
      H N beta B target source fiber k g₂ A)

/-- The literal C5 reference fiber weight is exactly the continuous vacuum
factor times the normalized-law precursor `local × kernel`. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight_eq_vacuum_mul_rawWeight
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
        H N hN beta hbeta B target source fiber k g₂ A =
      fun g =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumRepresentative
            H N hN beta hbeta
            (periodicHypercubicEvenSpecialUnitaryContinuousVacuumSpatialSliceReplaceLink
              H N A fiber g) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkRawWeight
            H N beta B target source fiber k g₂ A g := by
  funext g
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberWeight
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWeight
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkRawWeight
  ring

/-- RED specification: after normalizing `local × kernel`, inserting only the
continuous-vacuum fiber weight should reproduce the literal C5 reference fiber
probability law exactly. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_eq_rawDoob
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
        H N hN beta hbeta B target source fiber k g₂ A =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumSpatialLinkDoobMeasure
        H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkRawProbabilityMeasure
          H N beta B target source fiber k g₂ A)
        A fiber := by
  rfl

end

end MathlibAnalytic
end MGAP4D
