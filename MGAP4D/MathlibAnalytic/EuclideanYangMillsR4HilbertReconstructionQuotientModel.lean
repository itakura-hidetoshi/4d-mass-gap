import MGAP4D.MathlibAnalytic.EuclideanYangMillsR4HilbertReconstructionCarrierClosure
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

/-- Raw carrier for the next separated reconstruction step. -/
def inputCarrier
    (I : EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure S K R4 A G H N F C) :
    Type :=
  Sigma I.inputModel.reconstructionInputCarrier

/-- Minimal equality relation on the reconstruction input carrier. -/
def separationRelation
    (I : EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure S K R4 A G H N F C) :
    inputCarrier I → inputCarrier I → Prop :=
  Eq

/-- The minimal relation is an equivalence relation. -/
theorem separationRelation_equivalence
    (I : EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure S K R4 A G H N F C) :
    Equivalence (separationRelation I) := by
  constructor
  · intro x
    rfl
  · intro x y hxy
    simpa [separationRelation] using hxy.symm
  · intro x y z hxy hyz
    simpa [separationRelation] using hxy.trans hyz

/-- Canonical equality setoid on the reconstruction input carrier. -/
def separationSetoid
    (I : EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure S K R4 A G H N F C) :
    Setoid (inputCarrier I) where
  r := separationRelation I
  iseqv := separationRelation_equivalence I

/-- Quotient carrier produced by the separation relation.

The accompanying `separationSetoid` records the equivalence proof.  The carrier
itself uses Lean's kernel-level `Quot`, whose constructor and soundness theorem
have a stable explicit relation argument. -/
def quotientCarrier
    (I : EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure S K R4 A G H N F C) :
    Type :=
  Quot (separationRelation I)

/-- Canonical map into the quotient carrier. -/
def quotientMap
    (I : EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure S K R4 A G H N F C) :
    inputCarrier I → quotientCarrier I :=
  Quot.mk (separationRelation I)

/-- The quotient map respects the separation relation. -/
theorem quotientMap_respects
    (I : EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure S K R4 A G H N F C)
    {x y : inputCarrier I} (hxy : separationRelation I x y) :
    quotientMap I x = quotientMap I y :=
  Quot.sound hxy

/-- Nonemptiness passes from the input carrier to the quotient carrier. -/
theorem quotientCarrier_nonempty_of_input_nonempty
    (I : EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure S K R4 A G H N F C) :
    Nonempty (inputCarrier I) → Nonempty (quotientCarrier I) := by
  intro h
  rcases h with ⟨x⟩
  exact ⟨quotientMap I x⟩

end EuclideanYangMillsR4HilbertReconstructionQuotient

/-- Separated quotient model for the R4 Hilbert reconstruction carrier. -/
structure EuclideanYangMillsR4HilbertReconstructionQuotientModel
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
    (O : EuclideanYangMillsR4HilbertReconstructionCarrierClosure S K R4 A G H N F C I) where
  carrierClosure : EuclideanYangMillsR4HilbertReconstructionCarrierClosure S K R4 A G H N F C I
  carrierClosure_eq : carrierClosure = O
  inputCarrier_eq :
    EuclideanYangMillsR4HilbertReconstructionQuotient.inputCarrier I =
      Sigma I.inputModel.reconstructionInputCarrier
  separationSetoidCarrier :
    Setoid (EuclideanYangMillsR4HilbertReconstructionQuotient.inputCarrier I)
  separationSetoidCarrier_eq :
    separationSetoidCarrier = EuclideanYangMillsR4HilbertReconstructionQuotient.separationSetoid I
  separationEquivalence :
    Equivalence (EuclideanYangMillsR4HilbertReconstructionQuotient.separationRelation I)
  quotientNonempty :
    Nonempty (EuclideanYangMillsR4HilbertReconstructionQuotient.inputCarrier I) →
      Nonempty (EuclideanYangMillsR4HilbertReconstructionQuotient.quotientCarrier I)
  reflectionPositive : S.measurePackage.reflectionPositive
  euclideanInvariant : G.orbitModel.euclideanInvariantConstruction
  gaugeInvariant : G.orbitModel.gaugeInvariantConstruction

namespace EuclideanYangMillsR4HilbertReconstructionQuotientModel

/-- Build the quotient model from the previous carrier closure. -/
def ofCarrierClosure
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
    (O : EuclideanYangMillsR4HilbertReconstructionCarrierClosure S K R4 A G H N F C I) :
    EuclideanYangMillsR4HilbertReconstructionQuotientModel S K R4 A G H N F C I O :=
  { carrierClosure := O
    carrierClosure_eq := rfl
    inputCarrier_eq := rfl
    separationSetoidCarrier := EuclideanYangMillsR4HilbertReconstructionQuotient.separationSetoid I
    separationSetoidCarrier_eq := rfl
    separationEquivalence :=
      EuclideanYangMillsR4HilbertReconstructionQuotient.separationRelation_equivalence I
    quotientNonempty :=
      EuclideanYangMillsR4HilbertReconstructionQuotient.quotientCarrier_nonempty_of_input_nonempty I
    reflectionPositive := O.reflectionPositive
    euclideanInvariant := O.euclideanInvariant
    gaugeInvariant := O.gaugeInvariant }

end EuclideanYangMillsR4HilbertReconstructionQuotientModel

end

end MathlibAnalytic
end MGAP4D
