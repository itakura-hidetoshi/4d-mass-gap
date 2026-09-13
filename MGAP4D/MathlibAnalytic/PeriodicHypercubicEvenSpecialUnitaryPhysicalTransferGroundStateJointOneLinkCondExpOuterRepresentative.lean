import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointOneLinkCenteredResidual
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointOneLinkConditionalExpectation
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointMeasureEquivalence
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter

noncomputable section

local instance groundStateJointOneLinkCondExpOuterRepresentativeSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance groundStateJointOneLinkCondExpOuterRepresentativeSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance groundStateJointOneLinkCondExpOuterRepresentativeSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance groundStateJointOneLinkCondExpOuterRepresentativeSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance groundStateJointOneLinkCondExpOuterRepresentativeSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance groundStateJointOneLinkCondExpOuterRepresentativeSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The complete context retained when conditioning away exactly one target
right-boundary spatial link: the entire left boundary together with every
right-boundary coordinate except the target. -/
abbrev PeriodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContext
    (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) : Type :=
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
    (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
      Matrix.specialUnitaryGroup (Fin N) ℂ)

/-- Forget exactly the selected target link from the right boundary while
retaining the complete left boundary. -/
def periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap
    (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) →
      PeriodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContext
        H N target :=
  fun z =>
    (z.1,
      periodicHypercubicEvenSpatialSliceOffTargetRestriction
        (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target z.2)

/-- The one-link retained sigma-algebra is exactly the pullback of the ordinary
product sigma-algebra on the concrete outer-context carrier. -/
theorem
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace_eq_comap_outerContextMap
    (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
        H N target =
      MeasurableSpace.comap
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap
          H N target)
        (inferInstance : MeasurableSpace
          (PeriodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContext
            H N target)) := by
  change
    MeasurableSpace.comap Prod.fst inferInstance ⊔
        MeasurableSpace.comap
          (fun z :
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
            periodicHypercubicEvenSpatialSliceOffTargetRestriction
              (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target z.2)
          inferInstance =
      MeasurableSpace.comap
        (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap
          H N target)
        inferInstance
  rw [← MeasurableSpace.comap_prodMk
    (fun z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N => z.1)
    (fun z :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
      periodicHypercubicEvenSpatialSliceOffTargetRestriction
        (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target z.2)]
  rfl

/-- The concrete one-link outer-context map is measurable for the ambient joint
product measurable structure. -/
theorem
    measurable_periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap
    (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Measurable
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap
        H N target) := by
  exact measurable_fst.prodMk
    ((measurable_periodicHypercubicEvenSpecialUnitarySpatialSliceOffTargetRestriction
      H N target).comp measurable_snd)

/-- A genuine one-link `condExpL2` admits a strongly measurable real-valued
representative depending only on the complete retained outer context.

This is a Doob--Dynkin factorization of a safely chosen strongly measurable
representative of the `L²` conditional expectation.  It does not pointwise
evaluate an arbitrary quotient representative and makes no RCD or conditional
law identification. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_exists_outerContext_representative
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta) :
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
            H N hN beta hbeta target f :
            (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ) := by
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
      H N hN beta hbeta
  let m :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace
      H N target
  let outer :=
    periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap
      H N target
  have hAE :
      AEStronglyMeasurable[m]
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H N hN beta hbeta target f :
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
        μ := by
    simpa [μ, m,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_apply]
      using
        (aestronglyMeasurable_condExpL2
          (E := ℝ) (𝕜 := ℝ)
          (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace_le
            H N target) f)
  let g := hAE.choose
  have hgMeas : StronglyMeasurable[m] g := hAE.choose_spec.1
  have hgEq :
      g =ᵐ[μ]
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H N hN beta hbeta target f :
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ) :=
    hAE.choose_spec.2.symm
  have hgOuter :
      StronglyMeasurable[
        MeasurableSpace.comap outer
          (inferInstance : MeasurableSpace
            (PeriodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContext
              H N target))] g := by
    rw [← periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialLinkMeasurableSpace_eq_comap_outerContextMap
      H N target]
    exact hgMeas
  obtain ⟨C, hC, hfactor⟩ := hgOuter.exists_eq_measurable_comp
  refine ⟨C, hC, ?_⟩
  filter_upwards [hgEq] with z hz
  calc
    C (outer z) = g z := by
      simpa [Function.comp_apply] using (congrFun hfactor z).symm
    _ =
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H N hN beta hbeta target f :
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ) z := hz

/-- The same outer-context representative equality also holds pair-Haar almost
everywhere, by the already-proved reverse absolute continuity from pair Haar to
the genuine Wilson ground-state joint law.  This transports only null-set
geometry; it is not an `L²` norm comparison. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_exists_outerContext_representative_pairHaar
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta) :
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
            H N hN beta hbeta target f :
            (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ) ∧
        (fun z =>
          C (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap
            H N target z)) =ᵐ[
          periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N]
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
            H N hN beta hbeta target f :
            (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ) := by
  obtain ⟨C, hC, hJoint⟩ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2_exists_outerContext_representative
      H N hN beta hbeta target f
  have hPair :
      (fun z =>
        C (periodicHypercubicEvenSpecialUnitaryGroundStateJointOneLinkOuterContextMap
          H N target z)) =ᵐ[
        periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N]
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSpatialLinkCondExpL2
          H N hN beta hbeta target f :
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ) :=
    hJoint.filter_mono
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure_absolutelyContinuous_groundStateJointMeasure
        H N hN beta hbeta).ae_le
  exact ⟨C, hC, hJoint, hPair⟩

end

end MathlibAnalytic
end MGAP4D
