import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotientSectionClosure
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

/-- The quotient section is injective because projecting it returns the original quotient class. -/
theorem quotientSection_injective
    (I : EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure S K R4 A G H N F C) :
    Function.Injective (quotientSection I) := by
  intro q r hqr
  calc
    q = quotientMap I (quotientSection I q) := (quotientSection_projects I q).symm
    _ = quotientMap I (quotientSection I r) := by rw [hqr]
    _ = r := quotientSection_projects I r

/-- If two chosen section representatives agree, then the quotient classes agree. -/
theorem quotientSection_eq_reflects_class
    (I : EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure S K R4 A G H N F C)
    {q r : quotientCarrier I} :
    quotientSection I q = quotientSection I r → q = r :=
  quotientSection_injective I

end EuclideanYangMillsR4HilbertReconstructionQuotient

/-- Injectivity model for the quotient section stage.

This packages the fact that the selected quotient section embeds quotient classes
faithfully into the raw reconstruction input carrier. -/
structure EuclideanYangMillsR4HilbertReconstructionQuotientSectionInjectiveModel
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
    (U : EuclideanYangMillsR4HilbertReconstructionQuotientSectionClosure S K R4 A G H N F C I O Q P R) where
  sectionClosure :
    EuclideanYangMillsR4HilbertReconstructionQuotientSectionClosure S K R4 A G H N F C I O Q P R
  sectionClosure_eq : sectionClosure = U
  sectionInjective :
    Function.Injective (EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSection I)
  sectionEqReflectsClass :
    ∀ {q r : EuclideanYangMillsR4HilbertReconstructionQuotient.quotientCarrier I},
      EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSection I q =
        EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSection I r → q = r
  sectionProjects :
    ∀ q : EuclideanYangMillsR4HilbertReconstructionQuotient.quotientCarrier I,
      EuclideanYangMillsR4HilbertReconstructionQuotient.quotientMap I
        (EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSection I q) = q
  reflectionPositive : S.measurePackage.reflectionPositive
  euclideanInvariant : G.orbitModel.euclideanInvariantConstruction
  gaugeInvariant : G.orbitModel.gaugeInvariantConstruction

namespace EuclideanYangMillsR4HilbertReconstructionQuotientSectionInjectiveModel

/-- Build the quotient-section injectivity model from the quotient-section closure. -/
def ofSectionClosure
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
    (U : EuclideanYangMillsR4HilbertReconstructionQuotientSectionClosure S K R4 A G H N F C I O Q P R) :
    EuclideanYangMillsR4HilbertReconstructionQuotientSectionInjectiveModel S K R4 A G H N F C I O Q P R U :=
  { sectionClosure := U
    sectionClosure_eq := rfl
    sectionInjective := EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSection_injective I
    sectionEqReflectsClass :=
      fun {q} {r} hqr =>
        EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSection_eq_reflects_class I hqr
    sectionProjects := EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSection_projects I
    reflectionPositive := U.reflectionPositive
    euclideanInvariant := U.euclideanInvariant
    gaugeInvariant := U.gaugeInvariant }

end EuclideanYangMillsR4HilbertReconstructionQuotientSectionInjectiveModel

end

end MathlibAnalytic
end MGAP4D
