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

/-- On the selected section range, quotient-map equality reflects input-carrier equality. -/
theorem quotientMap_reflects_sectionRange_eq
    (I : EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure S K R4 A G H N F C)
    {O : EuclideanYangMillsR4HilbertReconstructionCarrierClosure S K R4 A G H N F C I}
    {Q : EuclideanYangMillsR4HilbertReconstructionQuotientClosure S K R4 A G H N F C I O}
    {P : EuclideanYangMillsR4HilbertReconstructionQuotientProjectionClosure S K R4 A G H N F C I O Q}
    {R : EuclideanYangMillsR4HilbertReconstructionQuotientRepresentativeClosure S K R4 A G H N F C I O Q P}
    {U : EuclideanYangMillsR4HilbertReconstructionQuotientSectionClosure S K R4 A G H N F C I O Q P R}
    {J : EuclideanYangMillsR4HilbertReconstructionQuotientSectionInjectiveClosure S K R4 A G H N F C I O Q P R U}
    (V : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeClosure S K R4 A G H N F C I O Q P R U J)
    {x y : inputCarrier I} :
    x ∈ V.sectionRange → y ∈ V.sectionRange →
      quotientMap I x = quotientMap I y → x = y := by
  intro hx hy hxy
  rcases V.rangeProjectsToWitness hx with ⟨q, hxq, hqx⟩
  rcases V.rangeProjectsToWitness hy with ⟨r, hyr, hry⟩
  have hqr : q = r := by
    calc
      q = quotientMap I x := hqx.symm
      _ = quotientMap I y := hxy
      _ = r := hry
  calc
    x = quotientSection I q := hxq
    _ = quotientSection I r := by rw [hqr]
    _ = y := hyr.symm

end EuclideanYangMillsR4HilbertReconstructionQuotient

/-- Model recording that the quotient map is faithful on the selected section range.

This is still a carrier-level reconstruction layer.  It uses the already-built
section range and range-witness projection facts to fix a faithful transport
surface for later norm and inner-product layers, without claiming completion of
the physical Hilbert space. -/
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
  quotientMapReflectsSectionRangeEq :
    ∀ {x y : EuclideanYangMillsR4HilbertReconstructionQuotient.inputCarrier I},
      x ∈ V.sectionRange → y ∈ V.sectionRange →
        EuclideanYangMillsR4HilbertReconstructionQuotient.quotientMap I x =
          EuclideanYangMillsR4HilbertReconstructionQuotient.quotientMap I y → x = y
  sectionRange : Set (EuclideanYangMillsR4HilbertReconstructionQuotient.inputCarrier I)
  sectionRange_eq : sectionRange = V.sectionRange
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
    quotientMapReflectsSectionRangeEq :=
      EuclideanYangMillsR4HilbertReconstructionQuotient.quotientMap_reflects_sectionRange_eq I V
    sectionRange := V.sectionRange
    sectionRange_eq := rfl
    sectionInjective := W.sectionInjective
    reflectionPositive := W.reflectionPositive
    euclideanInvariant := W.euclideanInvariant
    gaugeInvariant := W.gaugeInvariant }

end EuclideanYangMillsR4HilbertReconstructionQuotientMapInjectiveModel

end

end MathlibAnalytic
end MGAP4D
