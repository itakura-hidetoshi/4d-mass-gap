import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointTwelveSpatialCommonFixedGeometry
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

set_option maxHeartbeats 1000000

local instance groundStateTwelveSpatialPairHaarRetainedTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance groundStateTwelveSpatialPairHaarRetainedCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance groundStateTwelveSpatialPairHaarRetainedSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance groundStateTwelveSpatialPairHaarRetainedMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance groundStateTwelveSpatialPairHaarRetainedBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance groundStateTwelveSpatialPairHaarRetainedSpatialSliceLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Membership in the right-six retained intersection gives pair-Haar a.e.
strong measurability with respect to every right-update retained sigma-algebra.
The change of measure uses only the reverse absolute-continuity direction and
therefore introduces no quantitative density constant. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightSixRetained_aestronglyMeasurable_pairHaar
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (z : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta)
    (hz : z ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightSixRetainedLpMeas
        H N hN beta hbeta)
    (c : Fin 6) :
    AEStronglyMeasurable[
      periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
        H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)]
      (fun x => z x)
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  have hz' := hz
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightSixRetainedLpMeas,
    Submodule.mem_iInf] at hz'
  have hmeas :
      AEStronglyMeasurable[
        periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
          H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)]
        (fun x => z x)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta) :=
    mem_lpMeas_iff_aestronglyMeasurable.mp (hz' c)
  exact hmeas.mono_ac
    (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure_absolutelyContinuous_groundStateJointMeasure
      H N hN beta hbeta)

/-- Left-six counterpart of the pair-Haar retained-measurability transport. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixRetained_aestronglyMeasurable_pairHaar
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (z : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta)
    (hz : z ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixRetainedLpMeas
        H N hN beta hbeta)
    (c : Fin 6) :
    AEStronglyMeasurable[
      periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace
        H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)]
      (fun x => z x)
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  have hz' := hz
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixRetainedLpMeas,
    Submodule.mem_iInf] at hz'
  have hmeas :
      AEStronglyMeasurable[
        periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace
          H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)]
        (fun x => z x)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta) :=
    mem_lpMeas_iff_aestronglyMeasurable.mp (hz' c)
  exact hmeas.mono_ac
    (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure_absolutelyContinuous_groundStateJointMeasure
      H N hN beta hbeta)

/-- A twelve-color common-fixed vector is pair-Haar a.e. strongly measurable
with respect to every retained sigma-algebra in both six-color halves.  This
is the exact handoff from the actual Wilson joint law to the finite product
coordinate-elimination problem. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2_fixed_pairHaar_retained
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (z : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta)
    (hfixed :
      ∀ c : PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2
          H N hN beta hbeta c z = z) :
    (∀ c : Fin 6,
      AEStronglyMeasurable[
        periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
          H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)]
        (fun x => z x)
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)) ∧
    (∀ c : Fin 6,
      AEStronglyMeasurable[
        periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace
          H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)]
        (fun x => z x)
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N)) := by
  have hz :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2_fixed_iff_mem_rightSix_leftSix_retained
      H N hN beta hbeta z).1 hfixed
  constructor
  · intro c
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightSixRetained_aestronglyMeasurable_pairHaar
        H N hN beta hbeta z hz.1 c
  · intro c
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixRetained_aestronglyMeasurable_pairHaar
        H N hN beta hbeta z hz.2 c

end

end MathlibAnalytic
end MGAP4D
