import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointSixRetainedPairHaarBoundaryAEMeasurability
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance groundStateSixRetainedReverseTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance groundStateSixRetainedReverseCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance groundStateSixRetainedReverseSecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance groundStateSixRetainedReverseMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance groundStateSixRetainedReverseBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance groundStateSixRetainedReverseSpatialSliceLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- The six right-retained actual ground-state `L²` intersection is contained in
    the complete left-boundary `lpMeas` range.  Mutual absolute continuity is
    used only to transport a.e. strong measurability back from pair Haar. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightSixRetainedLpMeas_le_fst
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightSixRetainedLpMeas
        H N hN beta hbeta ≤
      lpMeas ℝ ℝ
        (MeasurableSpace.comap Prod.fst
          (inferInstance : MeasurableSpace
            (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)))
        2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta) := by
  intro z hz
  apply mem_lpMeas_iff_aestronglyMeasurable.mpr
  apply
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJoint_aestronglyMeasurable_iff_pairHaar
      H N hN beta hbeta
      (MeasurableSpace.comap Prod.fst
        (inferInstance : MeasurableSpace
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))) z).2
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightSixRetained_pairHaar_aestronglyMeasurable_fst
      H N hN beta hbeta z hz

/-- Left/right symmetric reverse inclusion for the six left-retained intersection. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixRetainedLpMeas_le_snd
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixRetainedLpMeas
        H N hN beta hbeta ≤
      lpMeas ℝ ℝ
        (MeasurableSpace.comap Prod.snd
          (inferInstance : MeasurableSpace
            (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)))
        2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta) := by
  intro z hz
  apply mem_lpMeas_iff_aestronglyMeasurable.mpr
  apply
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJoint_aestronglyMeasurable_iff_pairHaar
      H N hN beta hbeta
      (MeasurableSpace.comap Prod.snd
        (inferInstance : MeasurableSpace
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))) z).2
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixRetained_pairHaar_aestronglyMeasurable_snd
      H N hN beta hbeta z hz

end

end MathlibAnalytic
end MGAP4D
