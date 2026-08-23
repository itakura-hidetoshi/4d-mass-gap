import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenEdgeSideClassification
import MGAP4D.MathlibAnalytic.FiniteInvolutiveEdgeBoundaryFiberedPiMeasure
import MGAP4D.MathlibAnalytic.SpecialUnitaryBorelReceipts
import MGAP4D.MathlibAnalytic.SpecialUnitaryTopologicalCompactReceipts

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

local instance positiveHalfBasicHaarSpecialUnitaryIsTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance positiveHalfBasicHaarSpecialUnitaryCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance positiveHalfBasicHaarSpecialUnitarySecondCountableTopology (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance positiveHalfBasicHaarSpecialUnitaryMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance positiveHalfBasicHaarSpecialUnitaryBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Product normalized Haar probability on the actual positive open-half
coordinates.  This is a basic coordinate measure, independent of the OS Gram
construction and of the transfer-operator layer. -/
noncomputable def periodicHypercubicEvenOpenHalfHaarMeasure
    (H N : ℕ) : Measure
      ((periodicHypercubicEvenEdgeOrbitPartition H).OpenHalfConfiguration
        (Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
  (periodicHypercubicEvenEdgeOrbitPartition H).openHalfPiMeasure
    (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))

/-- Product normalized Haar probability on the actual shared fixed-edge
boundary.  It lives at the same basic coordinate layer as the open-half Haar
law, so both OS and transfer bridges can import it without a high-layer cycle. -/
noncomputable def periodicHypercubicEvenBoundaryHaarMeasure
    (H N : ℕ) : Measure
      ((periodicHypercubicEvenEdgeOrbitPartition H).BoundaryConfiguration
        (Matrix.specialUnitaryGroup (Fin N) ℂ)) :=
  (periodicHypercubicEvenEdgeOrbitPartition H).boundaryPiMeasure
    (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ))

end

end MathlibAnalytic
end MGAP4D
