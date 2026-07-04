import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeUniqueClosure
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

/-- The equality quotient map reflects input-carrier equality. -/
theorem quotientMap_reflects_input_eq
    (I : EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure S K R4 A G H N F C)
    {x y : inputCarrier I} :
    quotientMap I x = quotientMap I y → x = y := by
  intro h
  simpa [separationRelation] using (Quot.exact h)

/-- The equality quotient map is injective on the reconstruction input carrier. -/
theorem quotientMap_injective
    (I : EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure S K R4 A G H N F C) :
    Function.Injective (quotientMap I) := by
  intro x y hxy
  exact quotientMap_reflects_input_eq I hxy

end EuclideanYangMillsR4HilbertReconstructionQuotient

/-- Model recording that the current equality quotient map is injective.

This is still a carrier-level reconstruction layer.  It fixes that the present
separation relation is equality, so quotient equality reflects equality of the
input carrier.  Later norm and inner-product transport layers can use this as a
faithful quotient interface, without claiming completion of the physical Hilbert
space. -/
structure EuclideanYangMillsR4HilbertReconstructionQuotientMapInjectiveModel
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
    (W : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeUniqueClosure S K R4 A G H N F C I O Q P R U J V) where
  sectionRangeUniqueClosure :
    EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeUniqueClosure S K R4 A G H N F C I O Q P R U J V
  sectionRangeUniqueClosure_eq : sectionRangeUniqueClosure = W
  quotientMapReflectsInputEq :
    ∀ {x y : EuclideanYangMillsR4HilbertReconstructionQuotient.inputCarrier I},
      EuclideanYangMillsR4HilbertReconstructionQuotient.quotientMap I x =
        EuclideanYangMillsR4HilbertReconstructionQuotient.quotientMap I y → x = y
  quotientMapInjective :
    Function.Injective (EuclideanYangMillsR4HilbertReconstructionQuotient.quotientMap I)
  sectionInjective :
    Function.Injective (EuclideanYangMillsR4HilbertReconstructionQuotient.quotientSection I)
  reflectionPositive : S.measurePackage.reflectionPositive
  euclideanInvariant : G.orbitModel.euclideanInvariantConstruction
  gaugeInvariant : G.orbitModel.gaugeInvariantConstruction

namespace EuclideanYangMillsR4HilbertReconstructionQuotientMapInjectiveModel

/-- Build the quotient-map injectivity model from the section-range uniqueness closure. -/
def ofSectionRangeUniqueClosure
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
    (W : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeUniqueClosure S K R4 A G H N F C I O Q P R U J V) :
    EuclideanYangMillsR4HilbertReconstructionQuotientMapInjectiveModel S K R4 A G H N F C I O Q P R U J V W :=
  { sectionRangeUniqueClosure := W
    sectionRangeUniqueClosure_eq := rfl
    quotientMapReflectsInputEq :=
      EuclideanYangMillsR4HilbertReconstructionQuotient.quotientMap_reflects_input_eq I
    quotientMapInjective :=
      EuclideanYangMillsR4HilbertReconstructionQuotient.quotientMap_injective I
    sectionInjective := W.sectionInjective
    reflectionPositive := W.reflectionPositive
    euclideanInvariant := W.euclideanInvariant
    gaugeInvariant := W.gaugeInvariant }

end EuclideanYangMillsR4HilbertReconstructionQuotientMapInjectiveModel

end

end MathlibAnalytic
end MGAP4D
