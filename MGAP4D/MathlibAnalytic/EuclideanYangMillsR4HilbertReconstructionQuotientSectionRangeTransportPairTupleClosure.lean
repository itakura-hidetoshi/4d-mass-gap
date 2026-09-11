import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeTransportPairTupleTheorem
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Closure for tuple identities of quotient/selected-range transport pairs. -/
structure EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeTransportPairTupleClosure
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
    (D : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivDataClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T E)
    (TR : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivTransportClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T E D)
    (PCL : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeTransportPairClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T E D TR)
    (PPC : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeTransportPairProjectionClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T E D TR PCL) where
  transportPairTupleModel :
    EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeTransportPairTupleModel S K R4 A G H N F C I O Q P R U J V W X Y Z T E D TR PCL PPC
  sectionRangeTransportPairTupleOutputs : transportPairTupleModel.sectionRangeTransportPairTupleOutputs
  quotientPair_eq : ∀ q,
    EuclideanYangMillsR4HilbertReconstructionQuotient.quotientToTransportPair I TR q =
      (q, TR.forwardTransport q)
  rangePair_eq : ∀ x,
    EuclideanYangMillsR4HilbertReconstructionQuotient.rangeToTransportPair I TR x =
      (TR.inverseTransport x, x)
  quotientPair_fst : ∀ q,
    (EuclideanYangMillsR4HilbertReconstructionQuotient.quotientToTransportPair I TR q).1 = q
  quotientPair_snd : ∀ q,
    (EuclideanYangMillsR4HilbertReconstructionQuotient.quotientToTransportPair I TR q).2 = TR.forwardTransport q
  rangePair_fst : ∀ x,
    (EuclideanYangMillsR4HilbertReconstructionQuotient.rangeToTransportPair I TR x).1 = TR.inverseTransport x
  rangePair_snd : ∀ x,
    (EuclideanYangMillsR4HilbertReconstructionQuotient.rangeToTransportPair I TR x).2 = x
  reflectionPositive : S.measurePackage.reflectionPositive
  euclideanInvariant : G.orbitModel.euclideanInvariantConstruction
  gaugeInvariant : G.orbitModel.gaugeInvariantConstruction

namespace EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeTransportPairTupleClosure

/-- Build the transport-pair tuple closure from the projection closure. -/
def ofTransportPairProjectionClosure
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
    (D : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivDataClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T E)
    (TR : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivTransportClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T E D)
    (PCL : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeTransportPairClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T E D TR)
    (PPC : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeTransportPairProjectionClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T E D TR PCL) :
    EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeTransportPairTupleClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T E D TR PCL PPC :=
  let M := EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeTransportPairTupleModel.ofTransportPairProjectionClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T E D TR PCL PPC
  { transportPairTupleModel := M
    sectionRangeTransportPairTupleOutputs := EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeTransportPairTupleModel.sectionRangeTransportPairTupleOutputs_holds M
    quotientPair_eq := M.quotientPair_eq
    rangePair_eq := M.rangePair_eq
    quotientPair_fst := M.quotientPair_fst
    quotientPair_snd := M.quotientPair_snd
    rangePair_fst := M.rangePair_fst
    rangePair_snd := M.rangePair_snd
    reflectionPositive := M.reflectionPositive
    euclideanInvariant := M.euclideanInvariant
    gaugeInvariant := M.gaugeInvariant }

/-- Extract the bundled transport-pair tuple outputs. -/
theorem sectionRangeTransportPairTupleOutputsHeld
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
    {TR : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivTransportClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T E D}
    {PCL : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeTransportPairClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T E D TR}
    {PPC : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeTransportPairProjectionClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T E D TR PCL}
    (TPC : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeTransportPairTupleClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T E D TR PCL PPC) :
    TPC.transportPairTupleModel.sectionRangeTransportPairTupleOutputs :=
  TPC.sectionRangeTransportPairTupleOutputs

end EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeTransportPairTupleClosure

end

end MathlibAnalytic
end MGAP4D
