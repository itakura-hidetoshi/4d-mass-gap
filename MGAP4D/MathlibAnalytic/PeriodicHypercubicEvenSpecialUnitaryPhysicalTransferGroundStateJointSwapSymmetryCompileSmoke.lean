import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSwapSymmetry

namespace MGAP4D.MathlibAnalytic

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

example
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    Measure.map Prod.swap
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
          H N hN beta hbeta) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_map_swap
    H N hN beta hbeta

example
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    MeasurePreserving Prod.swap
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
        H N hN beta hbeta) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure_swap_measurePreserving
    H N hN beta hbeta

end

end MGAP4D.MathlibAnalytic
