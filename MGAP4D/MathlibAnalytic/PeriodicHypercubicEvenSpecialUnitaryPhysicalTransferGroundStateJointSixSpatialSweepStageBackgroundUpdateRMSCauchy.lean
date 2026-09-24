import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialSweepStageSharpHaar
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointBoundedConcreteBackgroundUpdateRMSCauchy
import Mathlib.Tactic

/-!
# Physical RMS background transport at canonical ground-state sweep stages

The bounded-concrete sweep-stage theorem supplies a single bounded strongly
measurable representative of every canonical fixed-color sweep prefix and
simultaneously controls its sharp Haar variance by the genuine one-link
conditional-expectation residual.

The bounded-concrete physical RMS theorem applies to exactly the same class of
representatives.  This file composes the two statements without choosing a new
representative.  Thus each canonical sweep stage has one explicit concrete
representative which simultaneously:

* realizes the genuine ground-state L2 stage vector;
* satisfies the sharp Haar residual bound used by the local sweep profile; and
* satisfies the actual continuous-vacuum physical centered RMS background
  update estimate with the existing BackgroundUpdateHarnackInfluence
  coefficient.

This is a local physical transport theorem.  It does not yet replace the
background-update coefficient by the full physical envelope kernel, whose
remote/resolvent part remains the next assembly step.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Set
open scoped ENNReal BigOperators

noncomputable section

local instance sweepStageRMSCauchySpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance sweepStageRMSCauchySpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance sweepStageRMSCauchySpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance sweepStageRMSCauchySpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance sweepStageRMSCauchySpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance sweepStageRMSCauchySpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- A canonical fixed-color sweep prefix admits one bounded concrete
representative which simultaneously carries the sharp Haar local residual
bound and the actual physical centered RMS background-update estimate.

The same representative is used in both conclusions.  In particular, the
proof does not evaluate an arbitrary L2 quotient representative pointwise. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorCanonicalOneLinkSweepPrefix_exists_boundedRepresentative_sharpHaar_and_backgroundUpdate_centeredRMS
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (stage : ℕ)
    (e : PeriodicHypercubicEvenFixedSpatialColorLink H color)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta)
    (hf :
      f ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (retained :
      PeriodicHypercubicEvenSpatialSliceOffTargetLink H e.1 →
        Matrix.specialUnitaryGroup (Fin N) ℂ)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedTarget distinguishedSource backgroundFiber :
      PeriodicHypercubicEvenSpatialSliceLink H)
    (hDistinct : e.1 ≠ backgroundFiber)
    (k g₂ u v : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (center : ℝ) :
    ∃
      (F :
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
      (hF : StronglyMeasurable F)
      (bound : ℝ)
      (hbound : ∀ z, ‖F z‖ ≤ bound),
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
          H N hN beta hbeta F hF bound hbound =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
          H N hN beta hbeta color
          (((Finset.univ :
            Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList).take stage)
          f ∧
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkBoundedCoreSharpHaarVarianceFunctional
          H N hN beta hbeta e.1 F ≤
        ENNReal.ofReal
          (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
                H N hN beta hbeta color
                (((Finset.univ :
                  Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList).take stage)
                f -
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2
                H N hN beta hbeta color e
                (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageVector
                  H N hN beta hbeta color
                  (((Finset.univ :
                    Finset (PeriodicHypercubicEvenFixedSpatialColorLink H color)).toList).take stage)
                  f)‖ ^ 2) ∧
      |(∫ g,
          periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
              H N e.1 F left retained g - center
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
            H N hN beta hbeta B distinguishedTarget distinguishedSource e.1 k g₂
            (Function.update A backgroundFiber u)) -
        (∫ g,
          periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
              H N e.1 F left retained g - center
          ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
            H N hN beta hbeta B distinguishedTarget distinguishedSource e.1 k g₂
            (Function.update A backgroundFiber v))| ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta *
          Real.sqrt
            ((∫ g,
                (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
                    H N e.1 F left retained g - center) ^ 2
                ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
                  H N hN beta hbeta B distinguishedTarget distinguishedSource e.1 k g₂
                  (Function.update A backgroundFiber u)) +
              ∫ g,
                (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
                    H N e.1 F left retained g - center) ^ 2
                ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
                  H N hN beta hbeta B distinguishedTarget distinguishedSource e.1 k g₂
                  (Function.update A backgroundFiber v)) := by
  rcases
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorCanonicalOneLinkSweepPrefix_exists_boundedRepresentative_sharpHaarVariance_le_residual
        H N hN beta hbeta color stage e f hf with
    ⟨F, hF, bound, hbound, hRep, hSharp⟩
  refine ⟨F, hF, bound, hbound, hRep, hSharp, ?_⟩
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSection_backgroundUpdate_centered_integral_sub_abs_le_harnackInfluence_mul_sqrt_energy_of_bounded
      H N hN beta hbeta e.1 F hF bound hbound left retained B A
      distinguishedTarget distinguishedSource backgroundFiber hDistinct
      k g₂ u v center

end

end MGAP4D.MathlibAnalytic
