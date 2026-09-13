import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOneLinkCondExpOuterRepresentative
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOneLinkCenteredResidual
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

local instance groundStateJointOneLinkBoundedCoreSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance groundStateJointOneLinkBoundedCoreSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance groundStateJointOneLinkBoundedCoreSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance groundStateJointOneLinkBoundedCoreSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance groundStateJointOneLinkBoundedCoreSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance groundStateJointOneLinkBoundedCoreSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance groundStateJointOneLinkBoundedCoreTargetLinkFintype
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Fintype (PeriodicHypercubicEvenSpatialSliceTargetLink H target) :=
  Subtype.fintype (fun e : PeriodicHypercubicEvenSpatialSliceLink H => e = target)

local instance groundStateJointOneLinkBoundedCoreTargetLinkUnique
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Unique (PeriodicHypercubicEvenSpatialSliceTargetLink H target) where
  default := ⟨target, rfl⟩
  uniq e := by
    apply Subtype.ext
    exact e.property

/-- Concrete target-link section of an ambient joint observable.  The complete
right boundary is reconstructed from a direct target-group coordinate and the
retained off-target coordinates through the canonical measurable equivalences.
No `L²` quotient representative is evaluated here. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
    (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (retained :
      PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ)
    (g : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  F
    (left,
      (periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
        (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target).symm
        ((periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target).symm g,
          retained))

/-- A strongly measurable concrete joint observable has a strongly measurable
direct target-link section at every retained outer context. -/
theorem
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection_stronglyMeasurable
    (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (retained :
      PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ) :
    StronglyMeasurable
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
        H N target F left retained) := by
  let split := periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
    (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target
  let eval := periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
    (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target
  have hTarget : Measurable
      (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ => eval.symm g) :=
    eval.symm.measurable
  have hTargetRetained : Measurable
      (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
        (eval.symm g, retained)) :=
    hTarget.prodMk measurable_const
  have hRight : Measurable
      (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
        split.symm (eval.symm g, retained)) :=
    split.symm.measurable.comp hTargetRetained
  have hJoint : Measurable
      (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
        (left, split.symm (eval.symm g, retained))) :=
    measurable_const.prodMk hRight
  simpa [periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection,
    split, eval] using hF.comp_measurable hJoint

/-- Pointwise boundedness of a concrete joint observable gives `L²` membership
of every direct target-Haar section.  This is the safe bounded-core substitute
for taking pointwise sections of an arbitrary joint `L²` quotient class. -/
theorem
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection_memLp_two_of_bounded
    (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (retained :
      PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ) :
    MemLp
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
        H N target F left retained)
      2
      (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) := by
  let μ := normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)
  letI : IsFiniteMeasure μ := by
    dsimp [μ]
    infer_instance
  exact MemLp.of_bound
    (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection_stronglyMeasurable
      H N target F hF left retained).aestronglyMeasurable
    bound
    (Filter.Eventually.of_forall fun g => by
      simpa [periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection]
        using hbound
          (left,
            (periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
              (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target).symm
              ((periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
                (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target).symm g,
                retained)))

/-- A bounded strongly measurable concrete joint observable defines a genuine
vector in the ground-state joint `L²` space. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcrete_memLp_two
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    MemLp F 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta) := by
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
      H N hN beta hbeta
  letI : IsProbabilityMeasure μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_isProbabilityMeasure
      H N hN beta hbeta
  exact MemLp.of_bound hF.aestronglyMeasurable bound
    (Filter.Eventually.of_forall hbound)

/-- Canonical genuine joint `L²` vector represented by a bounded strongly
measurable concrete observable. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcrete_memLp_two
    H N hN beta hbeta F hF bound hbound).toLp F

/-- The canonical bounded-core joint `L²` vector has the original concrete
observable as an almost-everywhere representative for the genuine ground-state
joint law. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2_coeFn
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    (fun z =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
        H N hN beta hbeta F hF bound hbound z) =ᵐ[
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta] F := by
  exact
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcrete_memLp_two
      H N hN beta hbeta F hF bound hbound).coeFn_toLp

/-- Sharp Haar one-link variance functional on the bounded concrete core,
weighted by the genuine singleton-target fiber mass.  The coefficient is
exactly `exp (-16 * beta)`, represented as the already-canonical inverse
`ENNReal.ofReal (exp (16 * beta))`. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkBoundedCoreSharpHaarVarianceFunctional
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ) : ℝ≥0∞ :=
  ∫⁻ left,
    ∫⁻ retained,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass
            H N hN beta hbeta left target retained *
          ((ENNReal.ofReal (Real.exp (16 * beta)))⁻¹ *
            evariance
              (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
                H N target F left retained)
              (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))
        ∂(Measure.pi
          (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
            normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))
    ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)

/-- Actual singleton-target centered residual functional for a concrete joint
observable and an outer-context center. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkBoundedCoreCenteredResidualFunctional
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (C :
      PeriodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContext
        H N target → ℝ) : ℝ≥0∞ :=
  ∫⁻ left,
    ∫⁻ retained,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass
            H N hN beta hbeta left target retained *
          doobCenteredSquaredResidual
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
              H N hN beta hbeta left target retained)
            (fun targetCfg =>
              periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
                H N target F left retained
                (periodicHypercubicEvenSpatialSliceTargetEvaluationMeasurableEquiv
                  (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target targetCfg))
            (C (left, retained))
        ∂(Measure.pi
          (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
            normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))
    ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)

/-- On the bounded strongly measurable concrete core, the genuine one-link
`condExpL2` admits its canonical retained-outer-context representative and that
same center may be inserted into the sharp weighted one-link variance bound.

This theorem deliberately stops before identifying the centered residual
functional with the global `L²` residual norm.  It uses neither an RCD claim nor
pointwise evaluation of an arbitrary joint `L²` quotient representative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkBoundedCore_exists_condExpOuter_centeredResidual
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
    (hbound : ∀ z, ‖F z‖ ≤ bound) :
    ∃ C :
        PeriodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContext
          H N target → ℝ,
      StronglyMeasurable C ∧
        (fun z =>
          C (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap
            H N target z)) =ᵐ[
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
            H N hN beta hbeta]
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
            H N hN beta hbeta target
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
              H N hN beta hbeta F hF bound hbound) :
            (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ) ∧
        (fun z =>
          C (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap
            H N target z)) =ᵐ[
          periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N]
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
            H N hN beta hbeta target
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
              H N hN beta hbeta F hF bound hbound) :
            (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ) ∧
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkBoundedCoreSharpHaarVarianceFunctional
            H N hN beta hbeta target F ≤
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkBoundedCoreCenteredResidualFunctional
            H N hN beta hbeta target F C := by
  let f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteL2
      H N hN beta hbeta F hF bound hbound
  obtain ⟨C, hC, hJoint, hPair⟩ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_exists_outerContext_representative_pairHaar
      H N hN beta hbeta target f
  refine ⟨C, hC, ?_, ?_, ?_⟩
  · simpa [f] using hJoint
  · simpa [f] using hPair
  · have hSections :
        ∀ᵐ left ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N),
          ∀ᵐ retained ∂(Measure.pi
            (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
              normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))),
            MemLp
              (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
                H N target F left retained)
              2
              (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)) := by
      refine Filter.Eventually.of_forall ?_
      intro left
      refine Filter.Eventually.of_forall ?_
      intro retained
      exact
        periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection_memLp_two_of_bounded
          H N target F hF bound hbound left retained
    have hineq :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTarget_context_haar_evariance_weighted_lintegral_le_centeredSquaredResidual
        H N hN beta hbeta target
        (fun left retained g =>
          periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkConcreteSection
            H N target F left retained g)
        (fun left retained => C (left, retained))
        hSections
    simpa [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkBoundedCoreSharpHaarVarianceFunctional,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointOneLinkBoundedCoreCenteredResidualFunctional]
      using hineq

end

end MathlibAnalytic
end MGAP4D
