import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointOneLinkSplitMarkovDisintegration
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance specialUnitaryGroupIsTopologicalGroupForSplitContextEquiv (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance specialUnitaryGroupCompactSpaceForSplitContextEquiv (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance specialUnitaryGroupSecondCountableTopologyForSplitContextEquiv (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance specialUnitaryGroupMeasurableSpaceForSplitContextEquiv (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance specialUnitaryGroupBorelSpaceForSplitContextEquiv (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance periodicHypercubicEvenSpatialSliceLinkFintypeForSplitContextEquiv
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance periodicHypercubicEvenSpatialSliceTargetLinkFintypeForSplitContextEquiv
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Fintype (PeriodicHypercubicEvenSpatialSliceTargetLink H target) :=
  Subtype.fintype (fun e : PeriodicHypercubicEvenSpatialSliceLink H => e = target)

/-- Reassociate `(left, off-target, target)`, swap the two right-coordinate
factors, and reconstruct the complete right boundary through the canonical
Haar coordinate split.

The singleton target configuration remains a literal subtype-indexed function;
no identification with a direct `SU(N)` variable is made. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitContextTargetMeasurableEquiv
    (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    ((PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
          Matrix.specialUnitaryGroup (Fin N) ℂ)) ×
      (PeriodicHypercubicEvenSpatialSliceTargetLink H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ)) ≃ᵐ
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) := by
  classical
  let split := periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
    (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target
  let assoc :
      ((PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
            Matrix.specialUnitaryGroup (Fin N) ℂ)) ×
        (PeriodicHypercubicEvenSpatialSliceTargetLink H target →
          Matrix.specialUnitaryGroup (Fin N) ℂ)) ≃ᵐ
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          ((PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
              Matrix.specialUnitaryGroup (Fin N) ℂ) ×
            (PeriodicHypercubicEvenSpatialSliceTargetLink H target →
              Matrix.specialUnitaryGroup (Fin N) ℂ))) :=
    MeasurableEquiv.prodAssoc
  let swapInner :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          ((PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
              Matrix.specialUnitaryGroup (Fin N) ℂ) ×
            (PeriodicHypercubicEvenSpatialSliceTargetLink H target →
              Matrix.specialUnitaryGroup (Fin N) ℂ))) ≃ᵐ
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          ((PeriodicHypercubicEvenSpatialSliceTargetLink H target →
              Matrix.specialUnitaryGroup (Fin N) ℂ) ×
            (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
              Matrix.specialUnitaryGroup (Fin N) ℂ))) :=
    (MeasurableEquiv.refl _).prodCongr MeasurableEquiv.prodComm
  let splitNested :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          ((PeriodicHypercubicEvenSpatialSliceTargetLink H target →
              Matrix.specialUnitaryGroup (Fin N) ℂ) ×
            (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
              Matrix.specialUnitaryGroup (Fin N) ℂ))) ≃ᵐ
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :=
    (MeasurableEquiv.refl _).prodCongr split.symm
  exact (assoc.trans swapInner).trans splitNested

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitContextTargetMeasurableEquiv_apply
    (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (z :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
          Matrix.specialUnitaryGroup (Fin N) ℂ)) ×
      (PeriodicHypercubicEvenSpatialSliceTargetLink H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitContextTargetMeasurableEquiv
        H N target z =
      (z.1.1,
        (periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
          (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target).symm
            (z.2, z.1.2)) := by
  classical
  rfl

/-- The explicit split-context coordinate equivalence is measure-preserving
from `(left Haar × off-target Haar) × target Haar` to the original
`left Haar × right Haar` configuration space. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitContextTargetHaar_measurePreserving
    (H N : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    MeasurePreserving
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitContextTargetMeasurableEquiv
        H N target)
      (((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
          (Measure.pi
            (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
              normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))).prod
        (Measure.pi
          (fun _ : PeriodicHypercubicEvenSpatialSliceTargetLink H target =>
            normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))))
      ((periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N).prod
        (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)) := by
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
      ((PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
            Matrix.specialUnitaryGroup (Fin N) ℂ)) ×
        (PeriodicHypercubicEvenSpatialSliceTargetLink H target →
          Matrix.specialUnitaryGroup (Fin N) ℂ)) ≃ᵐ
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          ((PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
              Matrix.specialUnitaryGroup (Fin N) ℂ) ×
            (PeriodicHypercubicEvenSpatialSliceTargetLink H target →
              Matrix.specialUnitaryGroup (Fin N) ℂ))) :=
    MeasurableEquiv.prodAssoc
  let swapInner :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          ((PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
              Matrix.specialUnitaryGroup (Fin N) ℂ) ×
            (PeriodicHypercubicEvenSpatialSliceTargetLink H target →
              Matrix.specialUnitaryGroup (Fin N) ℂ))) ≃ᵐ
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          ((PeriodicHypercubicEvenSpatialSliceTargetLink H target →
              Matrix.specialUnitaryGroup (Fin N) ℂ) ×
            (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
              Matrix.specialUnitaryGroup (Fin N) ℂ))) :=
    (MeasurableEquiv.refl _).prodCongr MeasurableEquiv.prodComm
  let splitNested :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          ((PeriodicHypercubicEvenSpatialSliceTargetLink H target →
              Matrix.specialUnitaryGroup (Fin N) ℂ) ×
            (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
              Matrix.specialUnitaryGroup (Fin N) ℂ))) ≃ᵐ
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
          PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :=
    (MeasurableEquiv.refl _).prodCongr split.symm
  have hAssoc : MeasurePreserving assoc
      ((μ.prod μOff).prod μTarget)
      (μ.prod (μOff.prod μTarget)) := by
    simpa [assoc] using
      (MeasureTheory.measurePreserving_prodAssoc μ μOff μTarget)
  have hSwap : MeasurePreserving swapInner
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
  have hSplitNested : MeasurePreserving splitNested
      (μ.prod (μTarget.prod μOff)) (μ.prod μ) := by
    simpa [splitNested] using
      (MeasurePreserving.id μ).prod hsplit.symm
  simpa [μ, μTarget, μOff, split, assoc, swapInner, splitNested,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitContextTargetMeasurableEquiv] using
    (hAssoc.trans hSwap).trans hSplitNested

end

end MathlibAnalytic
end MGAP4D
