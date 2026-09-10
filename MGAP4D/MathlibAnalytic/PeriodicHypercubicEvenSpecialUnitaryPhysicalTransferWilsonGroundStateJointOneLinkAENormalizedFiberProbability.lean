import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointOneLinkAEFiberMass
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal

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

/-- Keep the singleton target subtype on the exact `Fintype` presentation used
by the canonical Haar coordinate split. -/
local instance periodicHypercubicEvenSpatialSliceTargetLinkFintypeForAENormalizedFiber
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Fintype (PeriodicHypercubicEvenSpatialSliceTargetLink H target) :=
  Subtype.fintype (fun e : PeriodicHypercubicEvenSpatialSliceLink H => e = target)

/-- The literal normalized target-factor measure in the canonical
`target × off-target` coordinates.  This is only a normalized density on the
singleton target-coordinate carrier; it is not identified here with an RCD or
with the Wilson one-link Doob conditional law. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (retained : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Measure
      (PeriodicHypercubicEvenSpatialSliceTargetLink H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  doobWeightedMeasure
    (Measure.pi
      (fun _ : PeriodicHypercubicEvenSpatialSliceTargetLink H target =>
        normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))
    (fun targetCfg =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity
        H N hN beta hbeta left target (targetCfg, retained))

/-- The split-coordinate target-fiber mass is exactly the generic Doob weight
mass used by the canonical normalization API. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass_eq_doobWeightMass
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (left : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (retained : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass
        H N hN beta hbeta left target retained =
      doobWeightMass
        (Measure.pi
          (fun _ : PeriodicHypercubicEvenSpatialSliceTargetLink H target =>
            normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))
        (fun targetCfg =>
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity
            H N hN beta hbeta left target (targetCfg, retained)) := by
  rfl

/-- For Haar-a.e. left boundary and Haar-a.e. retained off-target context, the
literal normalized split target fiber is an actual probability measure.

Both exceptional sets are retained exactly.  The proof uses only the canonical
AE-measurability receipt, the positive-finite split fiber mass receipt, and the
existing generic Doob weighted-measure normalization theorem. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure_ae_isProbabilityMeasure
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    ∀ᵐ left ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N),
      ∀ᵐ retained ∂(Measure.pi
        (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
          normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))),
        IsProbabilityMeasure
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetNormalizedFiberMeasure
            H N hN beta hbeta left target retained) := by
  let μTarget := Measure.pi
    (fun _ : PeriodicHypercubicEvenSpatialSliceTargetLink H target =>
      normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
  let μOff := Measure.pi
    (fun _ : PeriodicHypercubicEvenSpatialSliceOffTargetLink H target =>
      normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))
  have hfiberMeas :
      ∀ᵐ left ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N),
        ∀ᵐ retained ∂μOff,
          AEMeasurable
            (fun targetCfg :
                PeriodicHypercubicEvenSpatialSliceTargetLink H target →
                  Matrix.specialUnitaryGroup (Fin N) ℂ =>
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity
                H N hN beta hbeta left target (targetCfg, retained)) μTarget := by
    simpa [μTarget, μOff] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity_ae_targetFiber
        H N hN beta hbeta target)
  have hfiberMass :
      ∀ᵐ left ∂(periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N),
        ∀ᵐ retained ∂μOff,
          0 <
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass
                H N hN beta hbeta left target retained ∧
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass
                H N hN beta hbeta left target retained < ∞ := by
    simpa [μOff] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass_ae_pos_lt_top
        H N hN beta hbeta target)
  filter_upwards [hfiberMeas, hfiberMass] with left hleftMeas hleftMass
  filter_upwards [hleftMeas, hleftMass] with retained hmeas hmass
  let w :
      (PeriodicHypercubicEvenSpatialSliceTargetLink H target →
        Matrix.specialUnitaryGroup (Fin N) ℂ) → ENNReal :=
    fun targetCfg =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitDensity
        H N hN beta hbeta left target (targetCfg, retained)
  have hMassZero : doobWeightMass μTarget w ≠ 0 := by
    rw [← periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass_eq_doobWeightMass
      H N hN beta hbeta left target retained]
    exact ne_of_gt hmass.1
  have hMassTop : doobWeightMass μTarget w ≠ ∞ := by
    rw [← periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightJointSplitTargetFiberMass_eq_doobWeightMass
      H N hN beta hbeta left target retained]
    exact ne_of_lt hmass.2
  refine ⟨?_⟩
  change doobWeightedMeasure μTarget w Set.univ = 1
  exact doobWeightedMeasure_measure_univ μTarget w hmeas hMassZero hMassTop

end

end MathlibAnalytic
end MGAP4D
