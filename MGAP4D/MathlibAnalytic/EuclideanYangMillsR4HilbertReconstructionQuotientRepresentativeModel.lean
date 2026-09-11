import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotientProjectionClosure
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

/-- Noncomputable representative choice for each quotient class. -/
def quotientRepresentativeChoice
    (I : EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure S K R4 A G H N F C) :
    quotientCarrier I → inputCarrier I :=
  fun q => Classical.choose (quotientClass_hasRepresentative I q)

/-- The chosen representative projects back to the original quotient class. -/
theorem quotientRepresentativeChoice_projects
    (I : EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure S K R4 A G H N F C)
    (q : quotientCarrier I) :
    quotientMap I (quotientRepresentativeChoice I q) = q :=
  Classical.choose_spec (quotientClass_hasRepresentative I q)

/-- The representative choice is a right inverse to the canonical quotient map. -/
theorem quotientRepresentativeChoice_rightInverse
    (I : EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure S K R4 A G H N F C) :
    Function.RightInverse (quotientRepresentativeChoice I) (quotientMap I) :=
  quotientRepresentativeChoice_projects I

end EuclideanYangMillsR4HilbertReconstructionQuotient

/-- Representative-choice model for the separated quotient stage.

This remains a carrier-level construction.  It records a noncomputable choice of
representative for each quotient class and proves that the chosen representative
projects back to the original class. -/
structure EuclideanYangMillsR4HilbertReconstructionQuotientRepresentativeModel
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
    (P : EuclideanYangMillsR4HilbertReconstructionQuotientProjectionClosure S K R4 A G H N F C I O Q) where
  projectionClosure : EuclideanYangMillsR4HilbertReconstructionQuotientProjectionClosure S K R4 A G H N F C I O Q
  projectionClosure_eq : projectionClosure = P
  representativeChoice :
    EuclideanYangMillsR4HilbertReconstructionQuotient.quotientCarrier I →
      EuclideanYangMillsR4HilbertReconstructionQuotient.inputCarrier I
  representativeChoice_eq :
    representativeChoice = EuclideanYangMillsR4HilbertReconstructionQuotient.quotientRepresentativeChoice I
  representativeProjects :
    ∀ q : EuclideanYangMillsR4HilbertReconstructionQuotient.quotientCarrier I,
      EuclideanYangMillsR4HilbertReconstructionQuotient.quotientMap I (representativeChoice q) = q
  representativeRightInverse :
    Function.RightInverse representativeChoice
      (EuclideanYangMillsR4HilbertReconstructionQuotient.quotientMap I)
  reflectionPositive : S.measurePackage.reflectionPositive
  euclideanInvariant : G.orbitModel.euclideanInvariantConstruction
  gaugeInvariant : G.orbitModel.gaugeInvariantConstruction

namespace EuclideanYangMillsR4HilbertReconstructionQuotientRepresentativeModel

/-- Build the representative-choice model from the quotient projection closure. -/
def ofProjectionClosure
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
    (P : EuclideanYangMillsR4HilbertReconstructionQuotientProjectionClosure S K R4 A G H N F C I O Q) :
    EuclideanYangMillsR4HilbertReconstructionQuotientRepresentativeModel S K R4 A G H N F C I O Q P :=
  { projectionClosure := P
    projectionClosure_eq := rfl
    representativeChoice :=
      EuclideanYangMillsR4HilbertReconstructionQuotient.quotientRepresentativeChoice I
    representativeChoice_eq := rfl
    representativeProjects :=
      EuclideanYangMillsR4HilbertReconstructionQuotient.quotientRepresentativeChoice_projects I
    representativeRightInverse :=
      EuclideanYangMillsR4HilbertReconstructionQuotient.quotientRepresentativeChoice_rightInverse I
    reflectionPositive := P.reflectionPositive
    euclideanInvariant := P.euclideanInvariant
    gaugeInvariant := P.gaugeInvariant }

end EuclideanYangMillsR4HilbertReconstructionQuotientRepresentativeModel

end

end MathlibAnalytic
end MGAP4D
