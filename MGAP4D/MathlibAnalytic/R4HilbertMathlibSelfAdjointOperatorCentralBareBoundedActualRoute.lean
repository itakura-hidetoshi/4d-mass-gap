import MGAP4D.MathlibAnalytic.R4HilbertMathlibSelfAdjointOperatorBareBoundedActualPackage
import MGAP4D.MathlibAnalytic.R4HilbertMathlibSelfAdjointOperatorBareBoundedActualRouteFromGeneratorCarrier
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace EuclideanYangMillsR4HilbertReconstructionQuotient

variable {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
variable {K : EuclideanYangMillsCompleteConstructionClosure S}
variable {R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K}
variable {A : EuclideanYangMillsR4GaugeActionClosure S K R4}
variable {G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A}
variable {H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G}
variable {N : EuclideanYangMillsR4SchwingerNPointFamilyClosure S K R4 A G H}
variable {F : EuclideanYangMillsR4CorrelationFunctionalClosure S K R4 A G H N}
variable {C : EuclideanYangMillsR4CorrelationStructureClosure S K R4 A G H N F}
variable (I : EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure S K R4 A G H N F C)
variable {O : EuclideanYangMillsR4HilbertReconstructionCarrierClosure S K R4 A G H N F C I}
variable {Q : EuclideanYangMillsR4HilbertReconstructionQuotientClosure S K R4 A G H N F C I O}
variable {P : EuclideanYangMillsR4HilbertReconstructionQuotientProjectionClosure S K R4 A G H N F C I O Q}
variable {R : EuclideanYangMillsR4HilbertReconstructionQuotientRepresentativeClosure S K R4 A G H N F C I O Q P}
variable {U : EuclideanYangMillsR4HilbertReconstructionQuotientSectionClosure S K R4 A G H N F C I O Q P R}
variable {J : EuclideanYangMillsR4HilbertReconstructionQuotientSectionInjectiveClosure S K R4 A G H N F C I O Q P R U}
variable {V : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeClosure S K R4 A G H N F C I O Q P R U J}
variable {W : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeUniqueClosure S K R4 A G H N F C I O Q P R U J V}
variable {X : EuclideanYangMillsR4HilbertReconstructionQuotientMapInjectiveClosure S K R4 A G H N F C I O Q P R U J V W}
variable {Y : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeRoundTripClosure S K R4 A G H N F C I O Q P R U J V W X}
variable {Z : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRepresentativeStableClosure S K R4 A G H N F C I O Q P R U J V W X Y}
variable {T : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRepresentativeProjectionClosure S K R4 A G H N F C I O Q P R U J V W X Y Z}
variable {E : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T}
variable {D : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivDataClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T E}
variable (TR : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivTransportClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T E D)

/-! Central supply for the bare bounded actual route. -/

/-- Central registry for the single installed witness that bare `M` has bounded
actual data.

Once this supply is installed, the existing
`R4HilbertMathlibSelfAdjointOperatorBareBoundedActualRoute I TR` class is supplied
from this central point.  Downstream bare-`M` entry points can then use their
original `[R4HilbertMathlibSelfAdjointOperatorBareBoundedActualRoute I TR]`
requirement without threading the upstream route data through every theorem. -/
class R4HilbertMathlibSelfAdjointOperatorCentralBareBoundedActualRouteSupply where
  bareBoundedActualRoute : R4HilbertMathlibSelfAdjointOperatorBareBoundedActualRoute I TR

/-- The central supply permanently installs the bare bounded actual route witness. -/
instance r4HilbertMathlibSelfAdjointOperator_bare_bounded_actual_route_from_central_supply
    [centralSupply :
      R4HilbertMathlibSelfAdjointOperatorCentralBareBoundedActualRouteSupply I TR] :
    R4HilbertMathlibSelfAdjointOperatorBareBoundedActualRoute I TR :=
  centralSupply.bareBoundedActualRoute

/-- Package an already constructed bare bounded actual route as the central supply. -/
def r4HilbertMathlibSelfAdjointOperator_central_supply_from_bare_bounded_actual_route
    (bareRoute : R4HilbertMathlibSelfAdjointOperatorBareBoundedActualRoute I TR) :
    R4HilbertMathlibSelfAdjointOperatorCentralBareBoundedActualRouteSupply I TR where
  bareBoundedActualRoute := bareRoute

/-- Central supply from Hamiltonian-domain coverage. -/
def r4HilbertMathlibSelfAdjointOperator_central_supply_from_hamiltonian_coverage
    (hBridge : r4HilbertMathlibSelfAdjointOperatorClosedGraphFullDomainToContinuousRepresentativeBridge I TR)
    (HC : ∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
      R4HilbertMathlibSelfAdjointOperatorHamiltonianDomainCoverageData I TR M) :
    R4HilbertMathlibSelfAdjointOperatorCentralBareBoundedActualRouteSupply I TR where
  bareBoundedActualRoute :=
    r4HilbertMathlibSelfAdjointOperator_bare_bounded_actual_route_from_hamiltonian_coverage I TR
      hBridge HC

/-- Central supply from Hamiltonian element coverage. -/
def r4HilbertMathlibSelfAdjointOperator_central_supply_from_hamiltonian_elements
    (hBridge : r4HilbertMathlibSelfAdjointOperatorClosedGraphFullDomainToContinuousRepresentativeBridge I TR)
    (EC : ∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
      R4HilbertMathlibSelfAdjointOperatorHamiltonianElementCoverageData I TR M) :
    R4HilbertMathlibSelfAdjointOperatorCentralBareBoundedActualRouteSupply I TR where
  bareBoundedActualRoute :=
    r4HilbertMathlibSelfAdjointOperator_bare_bounded_actual_route_from_hamiltonian_elements I TR
      hBridge EC

/-- Central supply from generator-lift coverage. -/
def r4HilbertMathlibSelfAdjointOperator_central_supply_from_generator_lift
    (hBridge : r4HilbertMathlibSelfAdjointOperatorClosedGraphFullDomainToContinuousRepresentativeBridge I TR)
    (glift : ∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
      R4HilbertMathlibSelfAdjointOperatorGeneratorLiftCoverageData I TR M) :
    R4HilbertMathlibSelfAdjointOperatorCentralBareBoundedActualRouteSupply I TR where
  bareBoundedActualRoute :=
    r4HilbertMathlibSelfAdjointOperator_bare_bounded_actual_route_from_generator_lift I TR
      hBridge glift

/-- Central supply from generator-carrier coverage. -/
def r4HilbertMathlibSelfAdjointOperator_central_supply_from_generator_carrier
    (hBridge : r4HilbertMathlibSelfAdjointOperatorClosedGraphFullDomainToContinuousRepresentativeBridge I TR)
    (gcover : ∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
      R4HilbertMathlibSelfAdjointOperatorGeneratorCarrierCoverageData I TR M) :
    R4HilbertMathlibSelfAdjointOperatorCentralBareBoundedActualRouteSupply I TR where
  bareBoundedActualRoute :=
    r4HilbertMathlibSelfAdjointOperator_bare_bounded_actual_route_from_generator_carrier I TR
      hBridge gcover

/-- With the central supply installed, bounded actual data is available from bare `M`. -/
def r4HilbertMathlibSelfAdjointOperator_central_supply_bare_M_bounded_actual_data
    [R4HilbertMathlibSelfAdjointOperatorCentralBareBoundedActualRouteSupply I TR]
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    R4HilbertMathlibSelfAdjointOperatorBoundedActualData I TR M :=
  r4HilbertMathlibSelfAdjointOperator_bare_M_bounded_actual_data I TR M

/-- With the central supply installed, the bare-`M` bounded actual data target is nonempty. -/
theorem r4HilbertMathlibSelfAdjointOperator_central_supply_bare_M_bounded_actual_nonempty
    [R4HilbertMathlibSelfAdjointOperatorCentralBareBoundedActualRouteSupply I TR]
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    Nonempty (R4HilbertMathlibSelfAdjointOperatorBoundedActualData I TR M) :=
  r4HilbertMathlibSelfAdjointOperator_bare_M_bounded_actual_nonempty I TR M

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
