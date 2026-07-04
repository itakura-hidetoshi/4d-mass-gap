import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionQuotientClosure
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

/-- The canonical quotient map is surjective: every quotient class has a representative. -/
theorem quotientMap_surjective
    (I : EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure S K R4 A G H N F C) :
    Function.Surjective (quotientMap I) := by
  intro q
  refine Quot.inductionOn q ?_
  intro x
  exact ⟨x, rfl⟩

/-- Every quotient class has a representative in the raw reconstruction input carrier. -/
theorem quotientClass_hasRepresentative
    (I : EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure S K R4 A G H N F C)
    (q : quotientCarrier I) :
    ∃ x : inputCarrier I, quotientMap I x = q :=
  quotientMap_surjective I q

end EuclideanYangMillsR4HilbertReconstructionQuotient

/-- Projection model for the separated quotient stage.

This packages the canonical map from the raw reconstruction input carrier to the
separated quotient carrier, together with the representative-existence theorem
obtained by quotient induction. -/
structure EuclideanYangMillsR4HilbertReconstructionQuotientProjectionModel
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
    (Q : EuclideanYangMillsR4HilbertReconstructionQuotientClosure S K R4 A G H N F C I O) where
  quotientClosure : EuclideanYangMillsR4HilbertReconstructionQuotientClosure S K R4 A G H N F C I O
  quotientClosure_eq : quotientClosure = Q
  quotientMapSurjective :
    Function.Surjective (EuclideanYangMillsR4HilbertReconstructionQuotient.quotientMap I)
  quotientRepresentative :
    ∀ q : EuclideanYangMillsR4HilbertReconstructionQuotient.quotientCarrier I,
      ∃ x : EuclideanYangMillsR4HilbertReconstructionQuotient.inputCarrier I,
        EuclideanYangMillsR4HilbertReconstructionQuotient.quotientMap I x = q
  reflectionPositive : S.measurePackage.reflectionPositive
  euclideanInvariant : G.orbitModel.euclideanInvariantConstruction
  gaugeInvariant : G.orbitModel.gaugeInvariantConstruction

namespace EuclideanYangMillsR4HilbertReconstructionQuotientProjectionModel

/-- Build the quotient projection model from the quotient closure. -/
def ofQuotientClosure
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
    (Q : EuclideanYangMillsR4HilbertReconstructionQuotientClosure S K R4 A G H N F C I O) :
    EuclideanYangMillsR4HilbertReconstructionQuotientProjectionModel S K R4 A G H N F C I O Q :=
  { quotientClosure := Q
    quotientClosure_eq := rfl
    quotientMapSurjective :=
      EuclideanYangMillsR4HilbertReconstructionQuotient.quotientMap_surjective I
    quotientRepresentative :=
      EuclideanYangMillsR4HilbertReconstructionQuotient.quotientClass_hasRepresentative I
    reflectionPositive := Q.reflectionPositive
    euclideanInvariant := Q.euclideanInvariant
    gaugeInvariant := Q.gaugeInvariant }

end EuclideanYangMillsR4HilbertReconstructionQuotientProjectionModel

end

end MathlibAnalytic
end MGAP4D
