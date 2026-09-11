import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotientMapInjectiveClosure
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

/-- On the selected section range, applying the quotient map and then the quotient section returns the same representative. -/
theorem quotientSection_quotientMap_sectionRange
    (I : EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure S K R4 A G H N F C)
    {O : EuclideanYangMillsR4HilbertReconstructionCarrierClosure S K R4 A G H N F C I}
    {Q : EuclideanYangMillsR4HilbertReconstructionQuotientClosure S K R4 A G H N F C I O}
    {P : EuclideanYangMillsR4HilbertReconstructionQuotientProjectionClosure S K R4 A G H N F C I O Q}
    {R : EuclideanYangMillsR4HilbertReconstructionQuotientRepresentativeClosure S K R4 A G H N F C I O Q P}
    {U : EuclideanYangMillsR4HilbertReconstructionQuotientSectionClosure S K R4 A G H N F C I O Q P R}
    {J : EuclideanYangMillsR4HilbertReconstructionQuotientSectionInjectiveClosure S K R4 A G H N F C I O Q P R U}
    {V : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeClosure S K R4 A G H N F C I O Q P R U J}
    {W : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeUniqueClosure S K R4 A G H N F C I O Q P R U J V}
    (X : EuclideanYangMillsR4HilbertReconstructionQuotientMapInjectiveClosure S K R4 A G H N F C I O Q P R U J V W)
    {x : inputCarrier I} :
    x ∈ X.sectionRange → quotientSection I (quotientMap I x) = x := by
  intro hx
  have hxV : x ∈ V.sectionRange := by
    simpa [X.sectionRange_eq] using hx
  rcases V.rangeProjectsToWitness hxV with ⟨q, hxq, hqx⟩
  calc
    quotientSection I (quotientMap I x) = quotientSection I q := by rw [hqx]
    _ = x := hxq.symm

end EuclideanYangMillsR4HilbertReconstructionQuotient

/-- Model recording the quotient-section/quotient-map round trip on the selected section range.

This is a carrier-level transport surface.  It records that selected representatives
are stable under `quotientSection ∘ quotientMap`, which is the form needed before
transporting norm and inner-product data along the selected range. -/
structure EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeRoundTripModel
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
    (X : EuclideanYangMillsR4HilbertReconstructionQuotientMapInjectiveClosure S K R4 A G H N F C I O Q P R U J V W) where
  quotientMapInjectiveClosure :
    EuclideanYangMillsR4HilbertReconstructionQuotientMapInjectiveClosure S K R4 A G H N F C I O Q P R U J V W
  quotientMapInjectiveClosure_eq : quotientMapInjectiveClosure = X
  sectionRangeRoundTrip :
    ∀ {x : EuclideanYangMillsR4HilbertReconstructionQuotient.inputCarrier I},
      x ∈ X.sectionRange →
        EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSection I
          (EuclideanYangMillsR4HilbertReconstructionQuotient.quotientMap I x) = x
  quotientMapReflectsSectionRangeEq :
    ∀ {x y : EuclideanYangMillsR4HilbertReconstructionQuotient.inputCarrier I},
      x ∈ V.sectionRange → y ∈ V.sectionRange →
        EuclideanYangMillsR4HilbertReconstructionQuotient.quotientMap I x =
          EuclideanYangMillsR4HilbertReconstructionQuotient.quotientMap I y → x = y
  sectionRange_eq : X.sectionRange = V.sectionRange
  sectionInjective :
    Function.Injective (EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSection I)
  reflectionPositive : S.measurePackage.reflectionPositive
  euclideanInvariant : G.orbitModel.euclideanInvariantConstruction
  gaugeInvariant : G.orbitModel.gaugeInvariantConstruction

namespace EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeRoundTripModel

/-- Build the section-range round-trip model from the quotient-map faithfulness closure. -/
def ofQuotientMapInjectiveClosure
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
    (X : EuclideanYangMillsR4HilbertReconstructionQuotientMapInjectiveClosure S K R4 A G H N F C I O Q P R U J V W) :
    EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeRoundTripModel S K R4 A G H N F C I O Q P R U J V W X :=
  { quotientMapInjectiveClosure := X
    quotientMapInjectiveClosure_eq := rfl
    sectionRangeRoundTrip :=
      EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSection_quotientMap_sectionRange I X
    quotientMapReflectsSectionRangeEq := X.quotientMapReflectsSectionRangeEq
    sectionRange_eq := X.sectionRange_eq
    sectionInjective := X.sectionInjective
    reflectionPositive := X.reflectionPositive
    euclideanInvariant := X.euclideanInvariant
    gaugeInvariant := X.gaugeInvariant }

end EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeRoundTripModel

end

end MathlibAnalytic
end MGAP4D
