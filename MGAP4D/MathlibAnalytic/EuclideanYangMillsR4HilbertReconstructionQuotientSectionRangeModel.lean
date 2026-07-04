import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotientSectionInjectiveClosure
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

/-- The range of the quotient section inside the raw reconstruction input carrier. -/
def quotientSectionRange
    (I : EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure S K R4 A G H N F C) :
    Set (inputCarrier I) :=
  Set.range (quotientSection I)

/-- Each quotient class has its selected representative in the quotient-section range. -/
theorem quotientSection_mem_range
    (I : EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure S K R4 A G H N F C)
    (q : quotientCarrier I) :
    quotientSection I q ∈ quotientSectionRange I :=
  ⟨q, rfl⟩

/-- Membership in the quotient-section range is exactly having a quotient-class preimage. -/
theorem quotientSectionRange_hasClass
    (I : EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure S K R4 A G H N F C)
    {x : inputCarrier I} :
    x ∈ quotientSectionRange I → ∃ q : quotientCarrier I, quotientSection I q = x := by
  intro hx
  exact hx

/-- Any element of the quotient-section range projects to its witnessing quotient class. -/
theorem quotientSectionRange_projects_to_witness
    (I : EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure S K R4 A G H N F C)
    {x : inputCarrier I} :
    x ∈ quotientSectionRange I →
      ∃ q : quotientCarrier I, x = quotientSection I q ∧ quotientMap I x = q := by
  intro hx
  rcases hx with ⟨q, rfl⟩
  exact ⟨q, rfl, quotientSection_projects I q⟩

end EuclideanYangMillsR4HilbertReconstructionQuotient

/-- Range model for the quotient section stage.

This packages the selected section representatives as a named subset of the raw
reconstruction input carrier.  The named range remains a carrier-level object. -/
structure EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeModel
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
    (J : EuclideanYangMillsR4HilbertReconstructionQuotientSectionInjectiveClosure S K R4 A G H N F C I O Q P R U) where
  sectionInjectiveClosure :
    EuclideanYangMillsR4HilbertReconstructionQuotientSectionInjectiveClosure S K R4 A G H N F C I O Q P R U
  sectionInjectiveClosure_eq : sectionInjectiveClosure = J
  sectionRange : Set (EuclideanYangMillsR4HilbertReconstructionQuotient.inputCarrier I)
  sectionRange_eq :
    sectionRange = EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSectionRange I
  sectionMemRange :
    ∀ q : EuclideanYangMillsR4HilbertReconstructionQuotient.quotientCarrier I,
      EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSection I q ∈ sectionRange
  rangeHasClass :
    ∀ {x : EuclideanYangMillsR4HilbertReconstructionQuotient.inputCarrier I},
      x ∈ sectionRange →
        ∃ q : EuclideanYangMillsR4HilbertReconstructionQuotient.quotientCarrier I,
          EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSection I q = x
  rangeProjectsToWitness :
    ∀ {x : EuclideanYangMillsR4HilbertReconstructionQuotient.inputCarrier I},
      x ∈ sectionRange →
        ∃ q : EuclideanYangMillsR4HilbertReconstructionQuotient.quotientCarrier I,
          x = EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSection I q ∧
            EuclideanYangMillsR4HilbertReconstructionQuotient.quotientMap I x = q
  sectionInjective :
    Function.Injective (EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSection I)
  reflectionPositive : S.measurePackage.reflectionPositive
  euclideanInvariant : G.orbitModel.euclideanInvariantConstruction
  gaugeInvariant : G.orbitModel.gaugeInvariantConstruction

namespace EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeModel

/-- Build the quotient-section range model from the quotient-section injectivity closure. -/
def ofSectionInjectiveClosure
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
    (J : EuclideanYangMillsR4HilbertReconstructionQuotientSectionInjectiveClosure S K R4 A G H N F C I O Q P R U) :
    EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeModel S K R4 A G H N F C I O Q P R U J :=
  { sectionInjectiveClosure := J
    sectionInjectiveClosure_eq := rfl
    sectionRange := EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSectionRange I
    sectionRange_eq := rfl
    sectionMemRange := EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSection_mem_range I
    rangeHasClass := EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSectionRange_hasClass I
    rangeProjectsToWitness := EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSectionRange_projects_to_witness I
    sectionInjective := J.sectionInjective
    reflectionPositive := J.reflectionPositive
    euclideanInvariant := J.euclideanInvariant
    gaugeInvariant := J.gaugeInvariant }

end EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeModel

end

end MathlibAnalytic
end MGAP4D
