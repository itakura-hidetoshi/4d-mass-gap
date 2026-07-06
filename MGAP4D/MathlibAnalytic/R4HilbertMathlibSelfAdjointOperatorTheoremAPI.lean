import MGAP4D.MathlibAnalytic.R4HilbertMathlibSelfAdjointOperator
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

/-- Theorem-facing API package for the mathlib R4 self-adjoint operator object.

This layer deliberately repackages the object-level facts from
`R4HilbertMathlibSelfAdjointOperatorData` without deriving a spectral theorem and
without stating a spectral-gap result. The purpose is to give later handoff layers
a stable theorem API carrying the actual mathlib `LinearPMap` self-adjointness
predicate, the prior criterion conclusion, compatibility, and readiness. -/
structure R4HilbertMathlibSelfAdjointOperatorTheoremAPIData
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) where
  operatorSelfAdjoint :
    (letI : NormedAddCommGroup
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
    letI : InnerProductSpace ℝ
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
    letI : CompleteSpace
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierCompleteSpace I TR M.selfAdjointnessData
    IsSelfAdjoint M.mathlibOperator)
  criterionConclusion : r4HilbertSelfAdjointnessConclusion I TR M.selfAdjointnessData
  compatibleWithHamiltonianInput : M.mathlibOperatorCompatibleWithHamiltonianInput
  objectReady : M.mathlibSelfAdjointObjectReady

/-- Build the theorem-facing API package from the object-level data. -/
def r4HilbertMathlibSelfAdjointOperatorTheoremAPI
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    R4HilbertMathlibSelfAdjointOperatorTheoremAPIData I TR M where
  operatorSelfAdjoint := r4HilbertMathlibSelfAdjointOperator_self_adjoint I TR M
  criterionConclusion := r4HilbertMathlibSelfAdjointOperator_criterion_proved I TR M
  compatibleWithHamiltonianInput := r4HilbertMathlibSelfAdjointOperator_compatible I TR M
  objectReady := r4HilbertMathlibSelfAdjointOperator_ready I TR M

/-- The self-adjointness input data behind the theorem-facing mathlib object API. -/
def r4HilbertMathlibSelfAdjointOperatorTheoremAPISelfAdjointnessData
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    R4HilbertSelfAdjointnessInputData I TR :=
  M.selfAdjointnessData

/-- The mathlib `LinearPMap` exposed by the theorem-facing API. -/
def r4HilbertMathlibSelfAdjointOperatorTheoremAPIOperator
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

/-- The theorem API exposes the actual mathlib `IsSelfAdjoint` predicate. -/
theorem r4HilbertMathlibSelfAdjointOperatorTheoremAPI_self_adjoint
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
  (r4HilbertMathlibSelfAdjointOperatorTheoremAPI I TR M).operatorSelfAdjoint

/-- The theorem API keeps the prior criterion-level conclusion available. -/
theorem r4HilbertMathlibSelfAdjointOperatorTheoremAPI_criterion_proved
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    r4HilbertSelfAdjointnessConclusion I TR M.selfAdjointnessData :=
  (r4HilbertMathlibSelfAdjointOperatorTheoremAPI I TR M).criterionConclusion

/-- The theorem API keeps the Hamiltonian-input compatibility witness available. -/
theorem r4HilbertMathlibSelfAdjointOperatorTheoremAPI_compatible
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    M.mathlibOperatorCompatibleWithHamiltonianInput :=
  (r4HilbertMathlibSelfAdjointOperatorTheoremAPI I TR M).compatibleWithHamiltonianInput

/-- The theorem API keeps the mathlib self-adjoint object readiness witness available. -/
theorem r4HilbertMathlibSelfAdjointOperatorTheoremAPI_ready
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) :
    M.mathlibSelfAdjointObjectReady :=
  (r4HilbertMathlibSelfAdjointOperatorTheoremAPI I TR M).objectReady

/-- Combined theorem-facing handoff for the mathlib self-adjoint operator object. -/
theorem r4HilbertMathlibSelfAdjointOperatorTheoremAPI_constructed
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
  ⟨r4HilbertMathlibSelfAdjointOperatorTheoremAPI_self_adjoint I TR M,
    r4HilbertMathlibSelfAdjointOperatorTheoremAPI_criterion_proved I TR M,
    r4HilbertMathlibSelfAdjointOperatorTheoremAPI_compatible I TR M,
    r4HilbertMathlibSelfAdjointOperatorTheoremAPI_ready I TR M⟩

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
