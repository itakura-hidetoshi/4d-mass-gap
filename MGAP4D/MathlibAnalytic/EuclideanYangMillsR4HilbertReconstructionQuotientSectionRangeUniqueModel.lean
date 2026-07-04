import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeClosure
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

/-- A section-range element has at most one quotient-class witness by section injectivity. -/
theorem quotientSectionRange_witness_unique
    (I : EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure S K R4 A G H N F C)
    {x : inputCarrier I} {q r : quotientCarrier I} :
    x = quotientSection I q → x = quotientSection I r → q = r := by
  intro hq hr
  exact quotientSection_injective I (by rw [← hq, ← hr])

/-- If a range element is a selected representative for `q` and projects to `r`, then `q = r`. -/
theorem quotientSectionRange_projection_unique
    (I : EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure S K R4 A G H N F C)
    {x : inputCarrier I} {q r : quotientCarrier I} :
    x = quotientSection I q → quotientMap I x = r → q = r := by
  intro hq hr
  calc
    q = quotientMap I (quotientSection I q) := (quotientSection_projects I q).symm
    _ = quotientMap I x := by rw [← hq]
    _ = r := hr

/-- Two full range witnesses for the same input-carrier element have the same quotient class. -/
theorem quotientSectionRange_full_witness_unique
    (I : EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure S K R4 A G H N F C)
    {x : inputCarrier I} {q r : quotientCarrier I} :
    (x = quotientSection I q ∧ quotientMap I x = q) →
      (x = quotientSection I r ∧ quotientMap I x = r) → q = r := by
  intro hq hr
  exact quotientSectionRange_witness_unique I hq.1 hr.1

end EuclideanYangMillsR4HilbertReconstructionQuotient

/-- Uniqueness model for quotient classes witnessing elements of the section range. -/
structure EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeUniqueModel
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
  sectionRangeClosure :
    EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeClosure S K R4 A G H N F C I O Q P R U J
  sectionRangeClosure_eq : sectionRangeClosure = V
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

namespace EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeUniqueModel

/-- Build the section-range uniqueness model from the section-range closure. -/
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
    EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeUniqueModel S K R4 A G H N F C I O Q P R U J V :=
  { sectionRangeClosure := V
    sectionRangeClosure_eq := rfl
    witnessUnique := EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSectionRange_witness_unique I
    projectionUnique := EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSectionRange_projection_unique I
    fullWitnessUnique := EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSectionRange_full_witness_unique I
    sectionInjective := V.sectionInjective
    reflectionPositive := V.reflectionPositive
    euclideanInvariant := V.euclideanInvariant
    gaugeInvariant := V.gaugeInvariant }

end EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeUniqueModel

end

end MathlibAnalytic
end MGAP4D
