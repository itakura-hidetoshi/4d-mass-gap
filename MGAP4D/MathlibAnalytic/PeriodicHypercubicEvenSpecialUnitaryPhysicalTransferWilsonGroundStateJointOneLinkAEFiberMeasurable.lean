import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointOneLinkHaarCoordinateSplit
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Keep the singleton target subtype on the same `Fintype` presentation used
by the canonical Haar coordinate split. -/
local instance periodicHypercubicEvenSpatialSliceTargetLinkFintypeForAEFiber
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Fintype (PeriodicHypercubicEvenSpatialSliceTargetLink H target) :=
  Subtype.fintype (fun e : PeriodicHypercubicEvenSpatialSliceLink H => e = target)

/-- The actual ground-state right-joint density expressed in the canonical
`target × off-target` Haar coordinates.  This is only a coordinate transport;
no fiber normalization or conditional-probability identification is made. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (z :
      (PeriodicHypercubicEvenSpatialSliceTargetLink H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ) ×
      (PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ)) : ℝ≥0∞ :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointDensity
    H N hN beta hbeta left
      ((periodicHypercubicEvenSpatialSliceTargetOffTargetMeasurableEquiv
        (Gauge := Matrix.specialUnitaryGroup (Fin N) ℂ) target).symm z)

/-- After transporting the right boundary to canonical `target × off-target`
coordinates, the target-link density is AE-measurable for Haar-a.e. retained
left boundary and Haar-a.e. off-target context.

The two successive almost-everywhere quantifiers are intentional.  The global
ground-state density is represented through an `L²` vacuum representative, so
this theorem does not promote a global a.e. statement to an arbitrary fixed
left boundary or arbitrary fixed fiber. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity_ae_targetFiber
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    ∀ᵐ left ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N),
      ∀ᵐ retained ∂(Measure.pi
        (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
          normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))),
        AEMeasurable
          (fun targetCfg :
              PeriodicHypercubicEvenSpatialSliceTargetLink H target →
                Matrix.specialUnitaryGroup (Fin N) ℂ =>
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity
              H N hN beta hbeta left target (targetCfg, retained))
          (Measure.pi
            (fun _ : PeriodicHypercubicEvenSpatialSliceTargetLink H target =>
              normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))) := by
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
  have hglobal :
      AEStronglyMeasurable
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
          H N hN beta hbeta)
        (μ.prod μ) := by
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight_integrable
        H N hN beta hbeta).aestronglyMeasurable
  have hright :
      ∀ᵐ left ∂μ,
        AEStronglyMeasurable
          (fun right =>
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
              H N hN beta hbeta (left, right)) μ :=
    hglobal.prodMk_left
  filter_upwards [hright] with left hleft
  have hsplit : MeasurePreserving split μ (μTarget.prod μOff) := by
    simpa [split, μ, μTarget, μOff] using
      (periodicHypercubicEvenSpecialUnitarySpatialSliceTargetOffTargetHaar_measurePreserving
        H N target)
  have hsplitInv : MeasurePreserving split.symm (μTarget.prod μOff) μ :=
    hsplit.symm
  have hsplitReal :
      AEStronglyMeasurable
        (fun z =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointNormalizedWeight
            H N hN beta hbeta (left, split.symm z))
        (μTarget.prod μOff) :=
    hleft.comp_quasiMeasurePreserving hsplitInv.quasiMeasurePreserving
  have hsplitDensity :
      AEMeasurable
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity
          H N hN beta hbeta left target)
        (μTarget.prod μOff) := by
    apply AEMeasurable.ennreal_ofReal
    simpa [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointDensity, split] using
      hsplitReal.aemeasurable
  have hsections := hsplitDensity.aestronglyMeasurable.prodMk_right
  simpa [μTarget, μOff] using hsections

end

end MathlibAnalytic
end MGAP4D
