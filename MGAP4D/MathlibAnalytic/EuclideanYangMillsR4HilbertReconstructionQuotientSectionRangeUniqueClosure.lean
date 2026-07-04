import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeUniqueTheorem
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Closure for uniqueness of quotient-class witnesses for section-range elements. -/
structure EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeUniqueClosure
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
    (V : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeClosure S K R4 A G H N F C I O Q P R U J) where
  sectionRangeUniqueModel :
    EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeUniqueModel S K R4 A G H N F C I O Q P R U J V
  sectionRangeUniqueOutputs : sectionRangeUniqueModel.sectionRangeUniqueOutputs
  witnessUnique :
    ∀ {x : EuclideanYangMillsR4HilbertReconstructionQuotient.inputCarrier I}
      {q r : EuclideanYangMillsR4HilbertReconstructionQuotient.quotientCarrier I},
      x = EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSection I q →
        x = EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSection I r → q = r
  projectionUnique :
    ∀ {x : EuclideanYangMillsR4HilbertReconstructionQuotient.inputCarrier I}
      {q r : EuclideanYangMillsR4HilbertReconstructionQuotient.quotientCarrier I},
      x = EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSection I q →
        EuclideanYangMillsR4HilbertReconstructionQuotient.quotientMap I x = r → q = r
  fullWitnessUnique :
    ∀ {x : EuclideanYangMillsR4HilbertReconstructionQuotient.inputCarrier I}
      {q r : EuclideanYangMillsR4HilbertReconstructionQuotient.quotientCarrier I},
      (x = EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSection I q ∧
        EuclideanYangMillsR4HilbertReconstructionQuotient.quotientMap I x = q) →
        (x = EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSection I r ∧
          EuclideanYangMillsR4HilbertReconstructionQuotient.quotientMap I x = r) → q = r
  sectionInjective :
    Function.Injective (EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSection I)
  reflectionPositive : S.measurePackage.reflectionPositive
  euclideanInvariant : G.orbitModel.euclideanInvariantConstruction
  gaugeInvariant : G.orbitModel.gaugeInvariantConstruction

namespace EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeUniqueClosure

/-- Build the range-witness uniqueness closure from the section-range closure. -/
def ofSectionRangeClosure
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
    (V : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeClosure S K R4 A G H N F C I O Q P R U J) :
    EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeUniqueClosure S K R4 A G H N F C I O Q P R U J V :=
  let M := EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeUniqueModel.ofSectionRangeClosure S K R4 A G H N F C I O Q P R U J V
  { sectionRangeUniqueModel := M
    sectionRangeUniqueOutputs := EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeUniqueModel.sectionRangeUniqueOutputs_holds M
    witnessUnique := M.witnessUnique
    projectionUnique := M.projectionUnique
    fullWitnessUnique := M.fullWitnessUnique
    sectionInjective := M.sectionInjective
    reflectionPositive := M.reflectionPositive
    euclideanInvariant := M.euclideanInvariant
    gaugeInvariant := M.gaugeInvariant }

/-- Build the range-witness uniqueness closure directly from the construction spine. -/
def ofSpine
    (S : EuclideanYangMillsContinuumMeasureConstructionSpine) :
    EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeUniqueClosure S
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
      (EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeClosure.ofSpine S) :=
  ofSectionRangeClosure S
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

/-- Extract the bundled range-witness uniqueness outputs. -/
theorem sectionRangeUniqueOutputsHeld
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
    (W : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeUniqueClosure S K R4 A G H N F C I O Q P R U J V) :
    W.sectionRangeUniqueModel.sectionRangeUniqueOutputs :=
  W.sectionRangeUniqueOutputs

end EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeUniqueClosure

end

end MathlibAnalytic
end MGAP4D
