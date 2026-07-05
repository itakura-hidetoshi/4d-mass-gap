import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivTransportTheorem
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Closure for selected section-range transport facts induced by the concrete `Equiv`. -/
structure EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivTransportClosure
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (K : EuclideanYangMillsCompleteConstructionClosure S)
    (R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K)
    (A : EuclideanYangMillsR4GaugeActionClosure S K R4)
    (G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A)
    (H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G)
    (N : EuclideanYangMillsR4SchwingerNPointFamilyClosure S K R4 A G H)
    (F : EuclideanYangMillsR4CorrelationFunctionalClosure S K R4 A G H N)
    (C : EuclideanYangMillsR4CorrelationStructureClosure S K R4 A G H N F)
    (I : EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure S K R4 A G H N F C)
    (O : EuclideanYangMillsR4HilbertReconstructionCarrierClosure S K R4 A G H N F C I)
    (Q : EuclideanYangMillsR4HilbertReconstructionQuotientClosure S K R4 A G H N F C I O)
    (P : EuclideanYangMillsR4HilbertReconstructionQuotientProjectionClosure S K R4 A G H N F C I O Q)
    (R : EuclideanYangMillsR4HilbertReconstructionQuotientRepresentativeClosure S K R4 A G H N F C I O Q P)
    (U : EuclideanYangMillsR4HilbertReconstructionQuotientSectionClosure S K R4 A G H N F C I O Q P R)
    (J : EuclideanYangMillsR4HilbertReconstructionQuotientSectionInjectiveClosure S K R4 A G H N F C I O Q P R U)
    (V : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeClosure S K R4 A G H N F C I O Q P R U J)
    (W : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeUniqueClosure S K R4 A G H N F C I O Q P R U J V)
    (X : EuclideanYangMillsR4HilbertReconstructionQuotientMapInjectiveClosure S K R4 A G H N F C I O Q P R U J V W)
    (Y : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeRoundTripClosure S K R4 A G H N F C I O Q P R U J V W X)
    (Z : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRepresentativeStableClosure S K R4 A G H N F C I O Q P R U J V W X Y)
    (T : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRepresentativeProjectionClosure S K R4 A G H N F C I O Q P R U J V W X Y Z)
    (E : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T)
    (D : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivDataClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T E) where
  sectionRangeEquivTransportModel :
    EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivTransportModel S K R4 A G H N F C I O Q P R U J V W X Y Z T E D
  sectionRangeEquivTransportOutputs : sectionRangeEquivTransportModel.sectionRangeEquivTransportOutputs
  forwardTransport : EuclideanYangMillsR4HilbertReconstructionQuotient.quotientCarrier I →
    EuclideanYangMillsR4HilbertReconstructionQuotient.selectedSectionRangeCarrier I X
  inverseTransport : EuclideanYangMillsR4HilbertReconstructionQuotient.selectedSectionRangeCarrier I X →
    EuclideanYangMillsR4HilbertReconstructionQuotient.quotientCarrier I
  forwardTransport_eq : forwardTransport = EuclideanYangMillsR4HilbertReconstructionQuotient.selectedSectionRangeForwardTransport I D
  inverseTransport_eq : inverseTransport = EuclideanYangMillsR4HilbertReconstructionQuotient.selectedSectionRangeInverseTransport I D
  forward_inverse_cancel : ∀ q, inverseTransport (forwardTransport q) = q
  inverse_forward_cancel : ∀ x, forwardTransport (inverseTransport x) = x
  equiv_apply : ∀ q, D.sectionRangeEquiv q = E.quotientToRange q
  equiv_symm_apply : ∀ x, D.sectionRangeEquiv.symm x = E.rangeToQuotient x
  reflectionPositive : S.measurePackage.reflectionPositive
  euclideanInvariant : G.orbitModel.euclideanInvariantConstruction
  gaugeInvariant : G.orbitModel.gaugeInvariantConstruction

namespace EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivTransportClosure

/-- Build the selected section-range transport closure from concrete `Equiv` data. -/
def ofSectionRangeEquivDataClosure
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine)
    (K : EuclideanYangMillsCompleteConstructionClosure S)
    (R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K)
    (A : EuclideanYangMillsR4GaugeActionClosure S K R4)
    (G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A)
    (H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G)
    (N : EuclideanYangMillsR4SchwingerNPointFamilyClosure S K R4 A G H)
    (F : EuclideanYangMillsR4CorrelationFunctionalClosure S K R4 A G H N)
    (C : EuclideanYangMillsR4CorrelationStructureClosure S K R4 A G H N F)
    (I : EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure S K R4 A G H N F C)
    (O : EuclideanYangMillsR4HilbertReconstructionCarrierClosure S K R4 A G H N F C I)
    (Q : EuclideanYangMillsR4HilbertReconstructionQuotientClosure S K R4 A G H N F C I O)
    (P : EuclideanYangMillsR4HilbertReconstructionQuotientProjectionClosure S K R4 A G H N F C I O Q)
    (R : EuclideanYangMillsR4HilbertReconstructionQuotientRepresentativeClosure S K R4 A G H N F C I O Q P)
    (U : EuclideanYangMillsR4HilbertReconstructionQuotientSectionClosure S K R4 A G H N F C I O Q P R)
    (J : EuclideanYangMillsR4HilbertReconstructionQuotientSectionInjectiveClosure S K R4 A G H N F C I O Q P R U)
    (V : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeClosure S K R4 A G H N F C I O Q P R U J)
    (W : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeUniqueClosure S K R4 A G H N F C I O Q P R U J V)
    (X : EuclideanYangMillsR4HilbertReconstructionQuotientMapInjectiveClosure S K R4 A G H N F C I O Q P R U J V W)
    (Y : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeRoundTripClosure S K R4 A G H N F C I O Q P R U J V W X)
    (Z : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRepresentativeStableClosure S K R4 A G H N F C I O Q P R U J V W X Y)
    (T : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRepresentativeProjectionClosure S K R4 A G H N F C I O Q P R U J V W X Y Z)
    (E : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T)
    (D : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivDataClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T E) :
    EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivTransportClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T E D :=
  let M := EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivTransportModel.ofSectionRangeEquivDataClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T E D
  { sectionRangeEquivTransportModel := M
    sectionRangeEquivTransportOutputs := EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivTransportModel.sectionRangeEquivTransportOutputs_holds M
    forwardTransport := M.forwardTransport
    inverseTransport := M.inverseTransport
    forwardTransport_eq := M.forwardTransport_eq
    inverseTransport_eq := M.inverseTransport_eq
    forward_inverse_cancel := M.forward_inverse_cancel
    inverse_forward_cancel := M.inverse_forward_cancel
    equiv_apply := M.equiv_apply
    equiv_symm_apply := M.equiv_symm_apply
    reflectionPositive := M.reflectionPositive
    euclideanInvariant := M.euclideanInvariant
    gaugeInvariant := M.gaugeInvariant }

/-- Build the selected section-range transport closure directly from the construction spine. -/
def ofSpine
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivTransportClosure S
      (EuclideanYangMillsCompleteConstructionClosure.ofSpine S)
      (EuclideanYangMillsR4GaugeFieldConstructionClosure.ofSpine S)
      (EuclideanYangMillsR4GaugeActionClosure.ofSpine S)
      (EuclideanYangMillsR4GaugeInvariantClosure.ofSpine S)
      (EuclideanYangMillsR4GaugeInvariantSchwingerClosure.ofSpine S)
      (EuclideanYangMillsR4SchwingerNPointFamilyClosure.ofSpine S)
      (EuclideanYangMillsR4CorrelationFunctionalClosure.ofSpine S)
      (EuclideanYangMillsR4CorrelationStructureClosure.ofSpine S)
      (EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure.ofSpine S)
      (EuclideanYangMillsR4HilbertReconstructionCarrierClosure.ofSpine S)
      (EuclideanYangMillsR4HilbertReconstructionQuotientClosure.ofSpine S)
      (EuclideanYangMillsR4HilbertReconstructionQuotientProjectionClosure.ofSpine S)
      (EuclideanYangMillsR4HilbertReconstructionQuotientRepresentativeClosure.ofSpine S)
      (EuclideanYangMillsR4HilbertReconstructionQuotientSectionClosure.ofSpine S)
      (EuclideanYangMillsR4HilbertReconstructionQuotientSectionInjectiveClosure.ofSpine S)
      (EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeClosure.ofSpine S)
      (EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeUniqueClosure.ofSpine S)
      (EuclideanYangMillsR4HilbertReconstructionQuotientMapInjectiveClosure.ofSpine S)
      (EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeRoundTripClosure.ofSpine S)
      (EuclideanYangMillsR4HilbertReconstructionQuotientSectionRepresentativeStableClosure.ofSpine S)
      (EuclideanYangMillsR4HilbertReconstructionQuotientSectionRepresentativeProjectionClosure.ofSpine S)
      (EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivClosure.ofSpine S)
      (EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivDataClosure.ofSpine S) :=
  ofSectionRangeEquivDataClosure S
    (EuclideanYangMillsCompleteConstructionClosure.ofSpine S)
    (EuclideanYangMillsR4GaugeFieldConstructionClosure.ofSpine S)
    (EuclideanYangMillsR4GaugeActionClosure.ofSpine S)
    (EuclideanYangMillsR4GaugeInvariantClosure.ofSpine S)
    (EuclideanYangMillsR4GaugeInvariantSchwingerClosure.ofSpine S)
    (EuclideanYangMillsR4SchwingerNPointFamilyClosure.ofSpine S)
    (EuclideanYangMillsR4CorrelationFunctionalClosure.ofSpine S)
    (EuclideanYangMillsR4CorrelationStructureClosure.ofSpine S)
    (EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure.ofSpine S)
    (EuclideanYangMillsR4HilbertReconstructionCarrierClosure.ofSpine S)
    (EuclideanYangMillsR4HilbertReconstructionQuotientClosure.ofSpine S)
    (EuclideanYangMillsR4HilbertReconstructionQuotientProjectionClosure.ofSpine S)
    (EuclideanYangMillsR4HilbertReconstructionQuotientRepresentativeClosure.ofSpine S)
    (EuclideanYangMillsR4HilbertReconstructionQuotientSectionClosure.ofSpine S)
    (EuclideanYangMillsR4HilbertReconstructionQuotientSectionInjectiveClosure.ofSpine S)
    (EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeClosure.ofSpine S)
    (EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeUniqueClosure.ofSpine S)
    (EuclideanYangMillsR4HilbertReconstructionQuotientMapInjectiveClosure.ofSpine S)
    (EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeRoundTripClosure.ofSpine S)
    (EuclideanYangMillsR4HilbertReconstructionQuotientSectionRepresentativeStableClosure.ofSpine S)
    (EuclideanYangMillsR4HilbertReconstructionQuotientSectionRepresentativeProjectionClosure.ofSpine S)
    (EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivClosure.ofSpine S)
    (EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivDataClosure.ofSpine S)

/-- Extract the bundled selected section-range transport outputs. -/
theorem sectionRangeEquivTransportOutputsHeld
    {S : EuclideanYangMillsContinuumMeasureConstructionSpine}
    {K : EuclideanYangMillsCompleteConstructionClosure S}
    {R4 : EuclideanYangMillsR4GaugeFieldConstructionClosure S K}
    {A : EuclideanYangMillsR4GaugeActionClosure S K R4}
    {G : EuclideanYangMillsR4GaugeInvariantClosure S K R4 A}
    {H : EuclideanYangMillsR4GaugeInvariantSchwingerClosure S K R4 A G}
    {N : EuclideanYangMillsR4SchwingerNPointFamilyClosure S K R4 A G H}
    {F : EuclideanYangMillsR4CorrelationFunctionalClosure S K R4 A G H N}
    {C : EuclideanYangMillsR4CorrelationStructureClosure S K R4 A G H N F}
    {I : EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure S K R4 A G H N F C}
    {O : EuclideanYangMillsR4HilbertReconstructionCarrierClosure S K R4 A G H N F C I}
    {Q : EuclideanYangMillsR4HilbertReconstructionQuotientClosure S K R4 A G H N F C I O}
    {P : EuclideanYangMillsR4HilbertReconstructionQuotientProjectionClosure S K R4 A G H N F C I O Q}
    {R : EuclideanYangMillsR4HilbertReconstructionQuotientRepresentativeClosure S K R4 A G H N F C I O Q P}
    {U : EuclideanYangMillsR4HilbertReconstructionQuotientSectionClosure S K R4 A G H N F C I O Q P R}
    {J : EuclideanYangMillsR4HilbertReconstructionQuotientSectionInjectiveClosure S K R4 A G H N F C I O Q P R U}
    {V : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeClosure S K R4 A G H N F C I O Q P R U J}
    {W : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeUniqueClosure S K R4 A G H N F C I O Q P R U J V}
    {X : EuclideanYangMillsR4HilbertReconstructionQuotientMapInjectiveClosure S K R4 A G H N F C I O Q P R U J V W}
    {Y : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeRoundTripClosure S K R4 A G H N F C I O Q P R U J V W X}
    {Z : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRepresentativeStableClosure S K R4 A G H N F C I O Q P R U J V W X Y}
    {T : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRepresentativeProjectionClosure S K R4 A G H N F C I O Q P R U J V W X Y Z}
    {E : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T}
    {D : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivDataClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T E}
    (TR : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivTransportClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T E D) :
    TR.sectionRangeEquivTransportModel.sectionRangeEquivTransportOutputs :=
  TR.sectionRangeEquivTransportOutputs

end EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivTransportClosure

end

end MathlibAnalytic
end MGAP4D
