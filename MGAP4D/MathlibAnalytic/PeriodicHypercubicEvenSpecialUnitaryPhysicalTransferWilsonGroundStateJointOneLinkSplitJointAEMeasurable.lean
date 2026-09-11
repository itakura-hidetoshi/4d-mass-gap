import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointOneLinkAEFiberMeasurable
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

noncomputable section

local instance specialUnitaryGroupIsTopologicalGroupForSplitJointAE (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance specialUnitaryGroupCompactSpaceForSplitJointAE (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance specialUnitaryGroupSecondCountableTopologyForSplitJointAE (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance specialUnitaryGroupMeasurableSpaceForSplitJointAE (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance specialUnitaryGroupBorelSpaceForSplitJointAE (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance periodicHypercubicEvenSpatialSliceLinkFintypeForSplitJointAE (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance periodicHypercubicEvenSpatialSliceTargetLinkFintypeForSplitJointAE
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Fintype (PeriodicHypercubicEvenSpatialSliceTargetLink H target) :=
  Subtype.fintype (fun e : PeriodicHypercubicEvenSpatialSliceLink H => e = target)

/-- The actual ground-state right-joint density is jointly a.e.-measurable in
`(left, retained off-target context, singleton target configuration)` when the
context is grouped as `(left, retained)` and the singleton target factor is kept
separate.

The proof transports the globally a.e.-measurable ground-state joint density
through three explicit measure-preserving coordinate changes:

1. product associativity,
2. swapping the off-target and target factors inside the right context,
3. the inverse canonical target/off-target Haar split.

Thus this theorem does not infer joint measurability from the earlier
fiberwise double-a.e. statement.  It also makes no RCD or Wilson conditional-law
identification. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity_aemeasurable_contextTarget
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    AEMeasurable
      (fun z :
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
              Matrix.specialUnitaryGroup (Fin N) ℂ)) ×
          (PeriodicHypercubicEvenSpatialSliceTargetLink H target →
            Matrix.specialUnitaryGroup (Fin N) ℂ) =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity
          H N hN beta hbeta z.1.1 target (z.2, z.1.2))
      (((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
          (Measure.pi
            (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
              normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))).prod
        (Measure.pi
          (fun _ : PeriodicHypercubicEvenSpatialSliceTargetLink H target =>
            normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))) := by
  classical
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let μTarget := Measure.pi
    (fun _ : PeriodicHypercubicEvenSpatialSliceTargetLink H target =>
      normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
  let μOff := Measure.pi
    (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
      normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
  let split := periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
    (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target
  let assoc :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
            Matrix.specialUnitaryGroup (Fin N) ℂ)) ×
        (PeriodicHypercubicEvenSpatialSliceTargetLink H target →
          Matrix.specialUnitaryGroup (Fin N) ℂ) ≃ᵐ
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        ((PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
            Matrix.specialUnitaryGroup (Fin N) ℂ) ×
          (PeriodicHypercubicEvenSpatialSliceTargetLink H target →
            Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
    MeasurableEquiv.prodAssoc
  let swapInner :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          ((PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
              Matrix.specialUnitaryGroup (Fin N) ℂ) ×
            (PeriodicHypercubicEvenSpatialSliceTargetLink H target →
              Matrix.specialUnitaryGroup (Fin N) ℂ)) ≃ᵐ
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          ((PeriodicHypercubicEvenSpatialSliceTargetLink H target →
              Matrix.specialUnitaryGroup (Fin N) ℂ) ×
            (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
              Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
    (MeasurableEquiv.refl _).prodCongr MeasurableEquiv.prodComm
  let splitNested :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          ((PeriodicHypercubicEvenSpatialSliceTargetLink H target →
              Matrix.specialUnitaryGroup (Fin N) ℂ) ×
            (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
              Matrix.specialUnitaryGroup (Fin N) ℂ)) ≃ᵐ
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N :=
    (MeasurableEquiv.refl _).prodCongr split.symm
  have hAssoc :
      MeasurePreserving assoc
        ((μ.prod μOff).prod μTarget)
        (μ.prod (μOff.prod μTarget)) := by
    simpa [assoc] using
      (MeasureTheory.measurePreserving_prodAssoc μ μOff μTarget)
  have hSwap :
      MeasurePreserving swapInner
        (μ.prod (μOff.prod μTarget))
        (μ.prod (μTarget.prod μOff)) := by
    simpa [swapInner] using
      (MeasurePreserving.id μ).prod
        (Measure.measurePreserving_swap :
          MeasurePreserving Prod.swap (μOff.prod μTarget) (μTarget.prod μOff))
  have hsplit : MeasurePreserving split μ (μTarget.prod μOff) := by
    simpa [split, μ, μTarget, μOff] using
      (periodicHypercubicEvenSpecialUnitarySpatialSliceTargetOffTargetHaar_measurePreserving
        H N target)
  have hsplitInv : MeasurePreserving split.symm (μTarget.prod μOff) μ :=
    hsplit.symm
  have hSplitNested :
      MeasurePreserving splitNested
        (μ.prod (μTarget.prod μOff))
        (μ.prod μ) := by
    simpa [splitNested] using
      (MeasurePreserving.id μ).prod hsplitInv
  have hglobal :
      AEStronglyMeasurable
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
          H N hN beta hbeta)
        (μ.prod μ) := by
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight_integrable
        H N hN beta hbeta).aestronglyMeasurable
  have hglobalDensity :
      AEMeasurable
        (fun z :
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointDensity
            H N hN beta hbeta z.1 z.2)
        (μ.prod μ) := by
    simpa [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointDensity] using
      hglobal.aemeasurable.ennreal_ofReal
  have hSplitAE :=
    hglobalDensity.comp_quasiMeasurePreserving hSplitNested.quasiMeasurePreserving
  have hSwapAE :=
    hSplitAE.comp_quasiMeasurePreserving hSwap.quasiMeasurePreserving
  have hAssocAE :=
    hSwapAE.comp_quasiMeasurePreserving hAssoc.quasiMeasurePreserving
  simpa [μ, μTarget, μOff, assoc, swapInner, splitNested, split,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity,
    Function.comp_def] using hAssocAE

end

end MathlibAnalytic
end MGAP4D
