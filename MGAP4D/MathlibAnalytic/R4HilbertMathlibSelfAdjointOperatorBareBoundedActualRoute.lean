import MGAP4D.MathlibAnalytic.R4HilbertMathlibSelfAdjointOperatorUnconditionalBoundedActualPackage
import Mathlib.Analysis.InnerProductSpace.LinearPMap
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
variable (I : EuclideanYangMillsR4ReflectionPositiveReconstructionInputClosure S K R4 A G H N F C)
variable {O : EuclideanYangMillsR4HilbertReconstructionCarrierClosure S K R4 A G H N F C I}
variable {Q : EuclideanYangMillsR4HilbertReconstructionQuotientClosure S K R4 A G H N F C I O}
variable {P : EuclideanYangMillsR4HilbertReconstructionQuotientProjectionClosure S K R4 A G H N F C I O Q}
variable {R : EuclideanYangMillsR4HilbertReconstructionQuotientRepresentativeClosure S K R4 A G H N F C I O Q P}
variable {U : EuclideanYangMillsR4HilbertReconstructionQuotientSectionClosure S K R4 A G H N F C I O Q P R}
variable {J : EuclideanYangMillsR4HilbertReconstructionQuotientSectionInjectiveClosure S K R4 A G H N F C I O Q P R U}
variable {V : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeClosure S K R4 A G H N F C I O Q P R U J}
variable {W : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeUniqueClosure S K R4 A G H N F C I O Q P R U J V}
variable {X : EuclideanYangMillsR4HilbertReconstructionQuotientMapInjectiveClosure S K R4 A G H N F C I O Q P R U J V W}
variable {Y : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeRoundTripClosure S K R4 A G H N F C I O Q P R U J V W X}
variable {Z : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRepresentativeStableClosure S K R4 A G H N F C I O Q P R U J V W X Y}
variable {T : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRepresentativeProjectionClosure S K R4 A G H N F C I O Q P R U J V W X Y Z}
variable {E : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T}
variable {D : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivDataClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T E}
variable (TR : EuclideanYangMillsR4HilbertReconstructionQuotientSectionRangeEquivTransportClosure S K R4 A G H N F C I O Q P R U J V W X Y Z T E D)

/-! Bare-`M` bounded actual route.

This layer moves the public boundedness entry point from an explicit route-family
or unconditional-route argument to a bare actual R4 mathlib operator datum
`M : R4HilbertMathlibSelfAdjointOperatorData I TR`.  The construction witness is
kept as an implicit route class, so downstream theorem statements can mention
only the concrete operator datum `M` at the call site. -/

/-- Global construction witness that every actual R4 mathlib self-adjoint operator
carries bounded actual data. -/
class R4HilbertMathlibSelfAdjointOperatorBareBoundedActualRoute where
  boundedActualData :
    ∀ (M : R4HilbertMathlibSelfAdjointOperatorData I TR),
      R4HilbertMathlibSelfAdjointOperatorBoundedActualData I TR M

/-- An existing unconditional bounded route supplies the bare-`M` route witness. -/
def r4HilbertMathlibSelfAdjointOperator_bare_bounded_actual_route_from_unconditional
    (hRoute : r4HilbertMathlibSelfAdjointOperatorUnconditionalBoundedRoute I TR) :
    R4HilbertMathlibSelfAdjointOperatorBareBoundedActualRoute I TR where
  boundedActualData := fun M =>
    r4HilbertMathlibSelfAdjointOperator_unconditional_route_to_bounded_actual_data I TR
      hRoute M

/-- Bare-`M` access to bounded actual data for the actual R4 operator. -/
def r4HilbertMathlibSelfAdjointOperator_bare_M_bounded_actual_data
    [bareRoute : R4HilbertMathlibSelfAdjointOperatorBareBoundedActualRoute I TR]
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    R4HilbertMathlibSelfAdjointOperatorBoundedActualData I TR M :=
  bareRoute.boundedActualData M

/-- Bare-`M` boundedness: the actual R4 operator is represented by a continuous
linear map on the full carrier. -/
theorem r4HilbertMathlibSelfAdjointOperator_bare_M_top_representative
    [bareRoute : R4HilbertMathlibSelfAdjointOperatorBareBoundedActualRoute I TR]
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    (letI : NormedAddCommGroup
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
    letI : InnerProductSpace ℝ
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
    ∃ (B : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData →L[ℝ]
          r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData),
      B.toPMap ⊤ = M.mathlibOperator) :=
  r4HilbertMathlibSelfAdjointOperator_bounded_actual_top_representative I TR M
    (r4HilbertMathlibSelfAdjointOperator_bare_M_bounded_actual_data I TR M)

/-- Bare-`M` nonempty bounded actual package. -/
theorem r4HilbertMathlibSelfAdjointOperator_bare_M_bounded_actual_nonempty
    [bareRoute : R4HilbertMathlibSelfAdjointOperatorBareBoundedActualRoute I TR]
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    Nonempty (R4HilbertMathlibSelfAdjointOperatorBoundedActualData I TR M) :=
  ⟨r4HilbertMathlibSelfAdjointOperator_bare_M_bounded_actual_data I TR M⟩

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
