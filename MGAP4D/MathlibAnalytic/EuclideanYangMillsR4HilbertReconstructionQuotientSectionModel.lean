import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotientRepresentativeClosure
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

/-- The representative choice, regarded as an explicit section of the quotient map. -/
def quotientSection
    (I : EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure S K R4 A G H N F C) :
    quotientCarrier I → inputCarrier I :=
  quotientRepresentativeChoice I

/-- The quotient section projects back to the quotient class it starts from. -/
theorem quotientSection_projects
    (I : EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure S K R4 A G H N F C)
    (q : quotientCarrier I) :
    quotientMap I (quotientSection I q) = q :=
  quotientRepresentativeChoice_projects I q

/-- The quotient section is a right inverse to the canonical quotient map. -/
theorem quotientSection_rightInverse
    (I : EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure S K R4 A G H N F C) :
    Function.RightInverse (quotientSection I) (quotientMap I) :=
  quotientSection_projects I

/-- The existence of a quotient section induces surjectivity of the quotient map. -/
theorem quotientMap_surjective_of_section
    (I : EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure S K R4 A G H N F C) :
    Function.Surjective (quotientMap I) := by
  intro q
  exact ⟨quotientSection I q, quotientSection_projects I q⟩

end EuclideanYangMillsR4HilbertReconstructionQuotient

/-- Section model for the separated quotient stage.

This names the representative choice as a section of the quotient projection and
packages the equation saying that projecting the chosen representative returns
the original quotient class. -/
structure EuclideanYangMillsR4HilbertReconstructionQuotientSectionModel
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
    (R : EuclideanYangMillsR4HilbertReconstructionQuotientRepresentativeClosure S K R4 A G H N F C I O Q P) where
  representativeClosure :
    EuclideanYangMillsR4HilbertReconstructionQuotientRepresentativeClosure S K R4 A G H N F C I O Q P
  representativeClosure_eq : representativeClosure = R
  sectionMap :
    EuclideanYangMillsR4HilbertReconstructionQuotient.quotientCarrier I →
      EuclideanYangMillsR4HilbertReconstructionQuotient.inputCarrier I
  sectionMap_eq :
    sectionMap = EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSection I
  sectionProjects :
    ∀ q : EuclideanYangMillsR4HilbertReconstructionQuotient.quotientCarrier I,
      EuclideanYangMillsR4HilbertReconstructionQuotient.quotientMap I (sectionMap q) = q
  sectionRightInverse :
    Function.RightInverse sectionMap
      (EuclideanYangMillsR4HilbertReconstructionQuotient.quotientMap I)
  sectionSurjectivity :
    Function.Surjective (EuclideanYangMillsR4HilbertReconstructionQuotient.quotientMap I)
  reflectionPositive : S.measurePackage.reflectionPositive
  euclideanInvariant : G.orbitModel.euclideanInvariantConstruction
  gaugeInvariant : G.orbitModel.gaugeInvariantConstruction

namespace EuclideanYangMillsR4HilbertReconstructionQuotientSectionModel

/-- Build the section model from the representative-choice closure. -/
def ofRepresentativeClosure
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
    (R : EuclideanYangMillsR4HilbertReconstructionQuotientRepresentativeClosure S K R4 A G H N F C I O Q P) :
    EuclideanYangMillsR4HilbertReconstructionQuotientSectionModel S K R4 A G H N F C I O Q P R :=
  { representativeClosure := R
    representativeClosure_eq := rfl
    sectionMap := EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSection I
    sectionMap_eq := rfl
    sectionProjects := EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSection_projects I
    sectionRightInverse := EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSection_rightInverse I
    sectionSurjectivity := EuclideanYangMillsR4HilbertReconstructionQuotient.quotientMap_surjective_of_section I
    reflectionPositive := R.reflectionPositive
    euclideanInvariant := R.euclideanInvariant
    gaugeInvariant := R.gaugeInvariant }

end EuclideanYangMillsR4HilbertReconstructionQuotientSectionModel

end

end MathlibAnalytic
end MGAP4D
