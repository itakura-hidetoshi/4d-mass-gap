import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStatePairHaarQualitativeBoundaryCollapse
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance groundStateTwelveConstantCollapseTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance groundStateTwelveConstantCollapseCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance groundStateTwelveConstantCollapseSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance groundStateTwelveConstantCollapseMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance groundStateTwelveConstantCollapseBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance groundStateTwelveConstantCollapseSpatialSliceLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Exact qualitative identification of the twelve-color common-fixed sector.
A genuine ground-state joint `L²` vector is fixed by every right and left
spatial conditional expectation exactly when its represented real function is
almost everywhere constant for the genuine Wilson ground-state joint law.

The forward direction uses pair-Haar only for null-set/Fubini geometry and then
transports the resulting a.e. identity back by mutual absolute continuity.  No
pair-Haar `L²` or integrability transport, density bound, or norm equivalence is
used. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2_fixed_iff_ae_const
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (z : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta) :
    (∀ color : PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2
        H N hN beta hbeta color z = z) ↔
      ∃ c : ℝ,
        (z :
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ) =ᵐ[
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
            H N hN beta hbeta]
          fun _ => c := by
  constructor
  · intro hfixed
    have hmem :=
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2_fixed_iff_mem_rightSix_leftSix_retained
        H N hN beta hbeta z).1 hfixed
    have hfst :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightSixRetained_pairHaar_aestronglyMeasurable_fst
        H N hN beta hbeta z hmem.1
    have hsnd :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixRetained_pairHaar_aestronglyMeasurable_snd
        H N hN beta hbeta z hmem.2
    obtain ⟨c, hcPair⟩ :=
      periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaar_ae_eq_const_of_fst_snd_aestronglyMeasurable
        H N
        (z :
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
        hfst hsnd
    refine ⟨c, ?_⟩
    exact
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJoint_ae_eq_iff_pairHaar
        H N hN beta hbeta
        (z :
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
        (fun _ => c)).2 hcPair
  · rintro ⟨c, hc⟩
    apply
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2_fixed_iff_mem_rightSix_leftSix_retained
        H N hN beta hbeta z).2
    constructor
    · rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightSixRetainedLpMeas,
        Submodule.mem_iInf]
      intro k
      apply mem_lpMeas_iff_aestronglyMeasurable.mpr
      have hconst :
          AEStronglyMeasurable[
            periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
              H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm k)]
            (fun _ :
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
                PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N => c)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
              H N hN beta hbeta) :=
        aestronglyMeasurable_const
      exact hconst.congr hc.symm
    · rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixRetainedLpMeas,
        Submodule.mem_iInf]
      intro k
      apply mem_lpMeas_iff_aestronglyMeasurable.mpr
      have hconst :
          AEStronglyMeasurable[
            periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace
              H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm k)]
            (fun _ :
              PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
                PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N => c)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
              H N hN beta hbeta) :=
        aestronglyMeasurable_const
      exact hconst.congr hc.symm

end

end MathlibAnalytic
end MGAP4D
