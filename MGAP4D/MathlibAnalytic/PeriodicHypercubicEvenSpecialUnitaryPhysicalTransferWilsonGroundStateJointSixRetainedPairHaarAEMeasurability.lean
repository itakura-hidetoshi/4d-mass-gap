import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateJointTwelveSpatialCommonFixedGeometry
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance groundStateSixRetainedPairHaarAETopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance groundStateSixRetainedPairHaarAECompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance groundStateSixRetainedPairHaarAESecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance groundStateSixRetainedPairHaarAEMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance groundStateSixRetainedPairHaarAEBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance groundStateSixRetainedPairHaarAESpatialSliceLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- Mutual absolute continuity of the genuine Wilson joint law and spatial pair Haar
transports sub-sigma-algebra a.e. strong measurability in both directions.  This is
only a null-set statement and introduces no `L²` norm comparison. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJoint_aestronglyMeasurable_iff_pairHaar
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (m : MeasurableSpace
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N))
    (f :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ) :
    AEStronglyMeasurable[m] f
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta) ↔
      AEStronglyMeasurable[m] f
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  constructor
  · rintro ⟨g, hg, hfg⟩
    exact ⟨g, hg,
      (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure_absolutelyContinuous_groundStateJointMeasure
        H N hN beta hbeta).ae_eq hfg⟩
  · rintro ⟨g, hg, hfg⟩
    exact ⟨g, hg,
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_absolutelyContinuous_pairHaar
        H N hN beta hbeta).ae_eq hfg⟩

/-- Membership in the genuine right-six retained `L²` intersection gives, for the
same represented function, pair-Haar a.e. strong measurability with respect to
each of the six right-update retained sigma-algebras.  No common pointwise
representative is selected here. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightSixRetained_pairHaar_aestronglyMeasurable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (z : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta)
    (hz : z ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightSixRetainedLpMeas
        H N hN beta hbeta) :
    ∀ c : Fin 6,
      AEStronglyMeasurable[
        periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
          H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)]
        (z :
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightSixRetainedLpMeas,
    Submodule.mem_iInf] at hz
  intro c
  apply
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJoint_aestronglyMeasurable_iff_pairHaar
      H N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointSpatialColorMeasurableSpace
        H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)) z).1
  exact mem_lpMeas_iff_aestronglyMeasurable.mp (hz c)

/-- Left/right symmetric transport for the left-six retained `L²` intersection. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixRetained_pairHaar_aestronglyMeasurable
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (z : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
      H N hN beta hbeta)
    (hz : z ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixRetainedLpMeas
        H N hN beta hbeta) :
    ∀ c : Fin 6,
      AEStronglyMeasurable[
        periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace
          H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)]
        (z :
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
            PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
        (periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N) := by
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixRetainedLpMeas,
    Submodule.mem_iInf] at hz
  intro c
  apply
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJoint_aestronglyMeasurable_iff_pairHaar
      H N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryGroundStateJointLeftSpatialColorMeasurableSpace
        H N (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c)) z).1
  exact mem_lpMeas_iff_aestronglyMeasurable.mp (hz c)

end

end MathlibAnalytic
end MGAP4D
