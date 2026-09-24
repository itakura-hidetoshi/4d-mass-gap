import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOneLinkBoundedCoreCondExp
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
import Mathlib.Tactic

/-!
# Bounded-concrete ground-state sections feed the physical influence envelope

The current positive-beta L2 frontier uses bounded strongly measurable
representatives of genuine ground-state joint L2 vectors.  The physical
influence envelope, independently, already controls literal one-link fiber
probability laws against bounded strongly measurable tests.

This file connects those two theorem spines without reverting to bounded
continuous observables and without evaluating an arbitrary L2 quotient
representative pointwise.

For a bounded-concrete joint observable whose pointwise norm bound is at most
one, every genuine one-link concrete section is an admissible test for the
actual physical left influence envelope.  Therefore changing one source link
in the physical background changes the target-fiber expectation of that
section by at most the already-canonical envelope coefficient K(target,source).

The result is the type/measure-theoretic transport layer needed before
constructing the observable-specific hybrid profile.  No new influence
coefficient, coupling geometry, Schur estimate, or volume-dependent factor is
introduced here.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped BigOperators

noncomputable section

local instance groundStateBoundedConcretePhysicalInfluenceBridgeSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance groundStateBoundedConcretePhysicalInfluenceBridgeSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance groundStateBoundedConcretePhysicalInfluenceBridgeSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance groundStateBoundedConcretePhysicalInfluenceBridgeSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance groundStateBoundedConcretePhysicalInfluenceBridgeSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance groundStateBoundedConcretePhysicalInfluenceBridgeSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- A bounded-concrete ground-state joint observable with pointwise bound at
most one gives, at every retained outer context, an admissible strongly
measurable test for the actual physical one-link influence envelope.

The conclusion uses the literal normalized one-link reference fiber laws and
the actual envelope kernel from the positive-beta physical spine.  In
particular, no continuity hypothesis on the observable is required. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSection_physicalLeft_difference_le_envelopeKernel_of_bound_le_one
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (hboundOne : bound ≤ 1)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (retained :
      PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ u v : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    |(∫ g,
        periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
          H N target F left retained g
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B source distinguishedSource target k g₂
          (Function.update A source u)) -
      (∫ g,
        periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
          H N target F left retained g
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B source distinguishedSource target k g₂
          (Function.update A source v))| ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
        H N hN beta hbeta A).influence target source := by
  let phi : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
      H N target F left retained
  have hphi : StronglyMeasurable phi := by
    simpa [phi] using
      periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection_stronglyMeasurable
        H N target F hF left retained
  have hphiBound : ∀ g, |phi g| ≤ 1 := by
    intro g
    have h :=
      hbound
        (left,
          (periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
            (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target).symm
            ((periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
              (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target).symm g,
              retained))
    have habs : |phi g| ≤ bound := by
      simpa [
        phi,
        periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection,
        Real.norm_eq_abs] using h
    exact habs.trans hboundOne
  simpa [phi] using
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_physicalLeft_boundedTest_difference_le_envelopeKernel
      H N hN beta hbeta B A source distinguishedSource target
      k g₂ u v phi hphi hphiBound

end

end MGAP4D.MathlibAnalytic
