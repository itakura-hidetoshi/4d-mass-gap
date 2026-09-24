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


/-- The actual physical one-link influence envelope scales sharply from
unit-bounded tests to arbitrary strongly measurable tests controlled in a
centered fiber interval.

This is the strongly-measurable analogue of the older continuous Wilson
center/radius transport.  The proof normalizes the test by the declared radius,
uses the already-established unit-ball physical envelope theorem, and then
rescales.  It neither changes the envelope coefficient nor introduces a
cardinality factor. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_physicalLeft_centeredTest_difference_le_envelopeKernel_mul_radius
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source distinguishedSource target : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ u v : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (phi : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hphi : StronglyMeasurable phi)
    (center radius : ℝ)
    (hRadiusNonneg : 0 ≤ radius)
    (hRadius : ∀ g, |phi g - center| ≤ radius) :
    |(∫ g, phi g
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B source distinguishedSource target k g₂
          (Function.update A source u)) -
      (∫ g, phi g
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B source distinguishedSource target k g₂
          (Function.update A source v))| ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
        H N hN beta hbeta A).influence target source * radius := by
  let μu :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
      H N hN beta hbeta B source distinguishedSource target k g₂
      (Function.update A source u)
  let μv :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
      H N hN beta hbeta B source distinguishedSource target k g₂
      (Function.update A source v)
  letI : IsProbabilityMeasure μu := by
    dsimp [μu]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_isProbabilityMeasure
        H N hN beta hbeta B source distinguishedSource target k g₂
        (Function.update A source u)
  letI : IsProbabilityMeasure μv := by
    dsimp [μv]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_isProbabilityMeasure
        H N hN beta hbeta B source distinguishedSource target k g₂
        (Function.update A source v)
  by_cases hRadiusZero : radius = 0
  · have hConst : phi = fun _ => center := by
      funext g
      have hle := hRadius g
      rw [hRadiusZero] at hle
      have hz : |phi g - center| = 0 :=
        le_antisymm hle (abs_nonneg _)
      exact sub_eq_zero.mp (abs_eq_zero.mp hz)
    simp [μu, μv, hConst, hRadiusZero]
  · have hRadiusPos : 0 < radius :=
      lt_of_le_of_ne hRadiusNonneg (Ne.symm hRadiusZero)
    let psi : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ :=
      fun g => (phi g - center) * radius⁻¹
    have hpsi : StronglyMeasurable psi := by
      dsimp [psi]
      exact (hphi.sub stronglyMeasurable_const).mul_const radius⁻¹
    have hpsiBound : ∀ g, |psi g| ≤ 1 := by
      intro g
      dsimp [psi]
      rw [abs_mul, abs_inv, abs_of_pos hRadiusPos]
      calc
        |phi g - center| * radius⁻¹ ≤ radius * radius⁻¹ :=
          mul_le_mul_of_nonneg_right
            (hRadius g) (inv_nonneg.mpr hRadiusPos.le)
        _ = 1 := mul_inv_cancel₀ (ne_of_gt hRadiusPos)
    have hEnvelope :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_physicalLeft_boundedTest_difference_le_envelopeKernel
        H N hN beta hbeta B A source distinguishedSource target
        k g₂ u v psi hpsi hpsiBound
    have hpsiU : Integrable psi μu := by
      exact Integrable.of_bound hpsi.aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun g => by
          simpa [Real.norm_eq_abs] using hpsiBound g)
    have hpsiV : Integrable psi μv := by
      exact Integrable.of_bound hpsi.aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun g => by
          simpa [Real.norm_eq_abs] using hpsiBound g)
    have hPhiU :
        (∫ g, phi g ∂μu) = radius * (∫ g, psi g ∂μu) + center := by
      calc
        (∫ g, phi g ∂μu) =
            ∫ g, radius * psi g + center ∂μu := by
          apply integral_congr_ae
          filter_upwards [] with g
          dsimp [psi]
          field_simp [ne_of_gt hRadiusPos]
          ring
        _ = radius * (∫ g, psi g ∂μu) + center := by
          rw [integral_add (hpsiU.const_mul radius) (integrable_const center),
            integral_const_mul]
          simp
    have hPhiV :
        (∫ g, phi g ∂μv) = radius * (∫ g, psi g ∂μv) + center := by
      calc
        (∫ g, phi g ∂μv) =
            ∫ g, radius * psi g + center ∂μv := by
          apply integral_congr_ae
          filter_upwards [] with g
          dsimp [psi]
          field_simp [ne_of_gt hRadiusPos]
          ring
        _ = radius * (∫ g, psi g ∂μv) + center := by
          rw [integral_add (hpsiV.const_mul radius) (integrable_const center),
            integral_const_mul]
          simp
    change
      |(∫ g, phi g ∂μu) - (∫ g, phi g ∂μv)| ≤
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
          H N hN beta hbeta A).influence target source * radius
    rw [hPhiU, hPhiV]
    have hAlgebra :
        radius * (∫ g, psi g ∂μu) + center -
            (radius * (∫ g, psi g ∂μv) + center) =
          radius * ((∫ g, psi g ∂μu) - ∫ g, psi g ∂μv) := by
      ring
    rw [hAlgebra, abs_mul, abs_of_pos hRadiusPos]
    calc
      radius * |(∫ g, psi g ∂μu) - ∫ g, psi g ∂μv| ≤
          radius *
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
              H N hN beta hbeta A).influence target source :=
        mul_le_mul_of_nonneg_left hEnvelope hRadiusPos.le
      _ =
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
            H N hN beta hbeta A).influence target source * radius := by
        ring

/-- A genuine bounded-concrete ground-state one-link section inherits the
center/radius-scaled actual physical influence estimate directly from the
preceding strongly-measurable theorem.

This is the form intended for sweep-stage representatives returned by the
bounded-concrete invariance/sharp-Haar spine: the representative is used
pointwise, while the ambient joint L2 quotient itself is never evaluated
pointwise. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkConcreteSection_physicalLeft_centered_difference_le_envelopeKernel_mul_radius
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (retained :
      PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ)
    (B A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (source distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ u v : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (center radius : ℝ)
    (hRadiusNonneg : 0 ≤ radius)
    (hRadius :
      ∀ g,
        |periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
            H N target F left retained g - center| ≤ radius) :
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
        H N hN beta hbeta A).influence target source * radius := by
  let phi : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
      H N target F left retained
  have hphi : StronglyMeasurable phi := by
    simpa [phi] using
      periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection_stronglyMeasurable
        H N target F hF left retained
  simpa [phi] using
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_physicalLeft_centeredTest_difference_le_envelopeKernel_mul_radius
      H N hN beta hbeta B A source distinguishedSource target
      k g₂ u v phi hphi center radius hRadiusNonneg hRadius

end

end MGAP4D.MathlibAnalytic
