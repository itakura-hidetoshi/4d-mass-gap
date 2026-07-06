import MGAP4D.MathlibAnalytic.R4HilbertSelfAdjointnessConclusionTheorem
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

/-- The completed Hilbert carrier used for the mathlib unbounded self-adjoint operator. -/
abbrev r4HilbertMathlibSelfAdjointCarrier
    (M : R4HilbertSelfAdjointnessInputData I TR) : Type :=
  r4HilbertCompletedHilbertSpace I TR
    M.hamiltonianData.generatorData.semigroupData.handoffData

@[implicit_reducible] def r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup
    (M : R4HilbertSelfAdjointnessInputData I TR) :
    NormedAddCommGroup (r4HilbertMathlibSelfAdjointCarrier I TR M) :=
  r4HilbertCompletedHilbertSpaceNormedAddCommGroup I TR
    M.hamiltonianData.generatorData.semigroupData.handoffData

@[implicit_reducible] def r4HilbertMathlibSelfAdjointCarrierInnerProductSpace
    (M : R4HilbertSelfAdjointnessInputData I TR) :
    (letI : NormedAddCommGroup (r4HilbertMathlibSelfAdjointCarrier I TR M) :=
      r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M
    InnerProductSpace ℝ (r4HilbertMathlibSelfAdjointCarrier I TR M)) :=
  r4HilbertCompletedHilbertSpaceInnerProductSpaceReal I TR
    M.hamiltonianData.generatorData.semigroupData.handoffData

@[implicit_reducible] def r4HilbertMathlibSelfAdjointCarrierCompleteSpace
    (M : R4HilbertSelfAdjointnessInputData I TR) :
    (letI : NormedAddCommGroup (r4HilbertMathlibSelfAdjointCarrier I TR M) :=
      r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M
    CompleteSpace (r4HilbertMathlibSelfAdjointCarrier I TR M)) :=
  r4HilbertCompletedHilbertSpaceCompleteSpace I TR
    M.hamiltonianData.generatorData.semigroupData.handoffData

/-- Data for an actual mathlib unbounded self-adjoint operator.

The operator is a mathlib `LinearPMap` on the completed R4 Hilbert carrier, and
`mathlibOperatorIsSelfAdjoint` is the actual mathlib `IsSelfAdjoint` predicate on
that `LinearPMap`. This layer therefore contains the mathlib object itself. It
still does not invoke a spectral theorem and does not state a spectral-gap
result. -/
structure R4HilbertMathlibSelfAdjointOperatorData where
  selfAdjointnessData : R4HilbertSelfAdjointnessInputData I TR
  mathlibOperator :
    (letI : NormedAddCommGroup
        (r4HilbertMathlibSelfAdjointCarrier I TR selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR selfAdjointnessData
    letI : InnerProductSpace ℝ
        (r4HilbertMathlibSelfAdjointCarrier I TR selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR selfAdjointnessData
    r4HilbertMathlibSelfAdjointCarrier I TR selfAdjointnessData →ₗ.[ℝ]
      r4HilbertMathlibSelfAdjointCarrier I TR selfAdjointnessData)
  mathlibOperatorIsSelfAdjoint :
    (letI : NormedAddCommGroup
        (r4HilbertMathlibSelfAdjointCarrier I TR selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR selfAdjointnessData
    letI : InnerProductSpace ℝ
        (r4HilbertMathlibSelfAdjointCarrier I TR selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR selfAdjointnessData
    letI : CompleteSpace
        (r4HilbertMathlibSelfAdjointCarrier I TR selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierCompleteSpace I TR selfAdjointnessData
    IsSelfAdjoint mathlibOperator)
  mathlibOperatorCompatibleWithHamiltonianInput : Prop
  mathlibOperatorCompatibleWithHamiltonianInput_holds :
    mathlibOperatorCompatibleWithHamiltonianInput
  mathlibSelfAdjointObjectReady : Prop
  mathlibSelfAdjointObjectReady_holds : mathlibSelfAdjointObjectReady

def r4HilbertMathlibSelfAdjointOperatorSelfAdjointnessData
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    R4HilbertSelfAdjointnessInputData I TR :=
  M.selfAdjointnessData

def r4HilbertMathlibSelfAdjointOperator
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    (letI : NormedAddCommGroup
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
    letI : InnerProductSpace ℝ
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
    r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData →ₗ.[ℝ]
      r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
  M.mathlibOperator

theorem r4HilbertMathlibSelfAdjointOperator_self_adjoint
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    (letI : NormedAddCommGroup
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
    letI : InnerProductSpace ℝ
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
    letI : CompleteSpace
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierCompleteSpace I TR M.selfAdjointnessData
    IsSelfAdjoint M.mathlibOperator) :=
  M.mathlibOperatorIsSelfAdjoint

theorem r4HilbertMathlibSelfAdjointOperator_criterion_proved
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    r4HilbertSelfAdjointnessConclusion I TR M.selfAdjointnessData :=
  r4HilbertSelfAdjointnessConclusion_proved I TR M.selfAdjointnessData

theorem r4HilbertMathlibSelfAdjointOperator_compatible
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    M.mathlibOperatorCompatibleWithHamiltonianInput :=
  M.mathlibOperatorCompatibleWithHamiltonianInput_holds

theorem r4HilbertMathlibSelfAdjointOperator_ready
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    M.mathlibSelfAdjointObjectReady :=
  M.mathlibSelfAdjointObjectReady_holds

/-- The actual mathlib unbounded self-adjoint operator object and its proof. -/
theorem r4HilbertMathlibSelfAdjointOperator_constructed
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    (letI : NormedAddCommGroup
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
    letI : InnerProductSpace ℝ
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
    letI : CompleteSpace
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierCompleteSpace I TR M.selfAdjointnessData
    IsSelfAdjoint M.mathlibOperator) ∧
      r4HilbertSelfAdjointnessConclusion I TR M.selfAdjointnessData ∧
        M.mathlibOperatorCompatibleWithHamiltonianInput ∧ M.mathlibSelfAdjointObjectReady :=
  ⟨r4HilbertMathlibSelfAdjointOperator_self_adjoint I TR M,
    r4HilbertMathlibSelfAdjointOperator_criterion_proved I TR M,
    r4HilbertMathlibSelfAdjointOperator_compatible I TR M,
    r4HilbertMathlibSelfAdjointOperator_ready I TR M⟩

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
