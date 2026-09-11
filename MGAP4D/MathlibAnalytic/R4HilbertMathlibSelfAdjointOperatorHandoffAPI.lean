import MGAP4D.MathlibAnalytic.R4HilbertMathlibSelfAdjointOperatorTheoremAPI
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

/-- Handoff API data for carrying the mathlib self-adjoint R4 operator object toward
later spectral-theorem input layers.

This structure keeps the actual mathlib `LinearPMap`/`IsSelfAdjoint` theorem API
available and adds only readiness and compatibility witnesses for a future
spectral-theorem input layer. It does not state a spectral theorem, construct a
spectral projection, introduce functional calculus, or assert a spectral gap. -/
structure R4HilbertMathlibSelfAdjointOperatorHandoffData
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) where
  theoremAPI : R4HilbertMathlibSelfAdjointOperatorTheoremAPIData I TR M
  mathlibSelfAdjointOperatorHandoffReady : Prop
  mathlibSelfAdjointOperatorHandoffReady_holds : mathlibSelfAdjointOperatorHandoffReady
  spectralTheoremInputCompatible : Prop
  spectralTheoremInputCompatible_holds : spectralTheoremInputCompatible

/-- The theorem API package carried by the handoff layer. -/
def r4HilbertMathlibSelfAdjointOperatorHandoffTheoremAPI
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (Handoff : R4HilbertMathlibSelfAdjointOperatorHandoffData I TR M) :
    R4HilbertMathlibSelfAdjointOperatorTheoremAPIData I TR M :=
  Handoff.theoremAPI

/-- The self-adjointness input data carried by the handoff layer. -/
def r4HilbertMathlibSelfAdjointOperatorHandoffSelfAdjointnessData
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (_Handoff : R4HilbertMathlibSelfAdjointOperatorHandoffData I TR M) :
    R4HilbertSelfAdjointnessInputData I TR :=
  M.selfAdjointnessData

/-- The mathlib `LinearPMap` carried by the handoff layer. -/
def r4HilbertMathlibSelfAdjointOperatorHandoffOperator
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (_Handoff : R4HilbertMathlibSelfAdjointOperatorHandoffData I TR M) :
    (letI : NormedAddCommGroup
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
    letI : InnerProductSpace ℝ
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
    r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData →ₗ.[ℝ]
      r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
  M.mathlibOperator

/-- The handoff layer exposes the actual mathlib `IsSelfAdjoint` predicate. -/
theorem r4HilbertMathlibSelfAdjointOperatorHandoff_self_adjoint
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (Handoff : R4HilbertMathlibSelfAdjointOperatorHandoffData I TR M) :
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
  Handoff.theoremAPI.operatorSelfAdjoint

/-- The handoff layer keeps the criterion-level self-adjointness conclusion. -/
theorem r4HilbertMathlibSelfAdjointOperatorHandoff_criterion_proved
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (Handoff : R4HilbertMathlibSelfAdjointOperatorHandoffData I TR M) :
    r4HilbertSelfAdjointnessConclusion I TR M.selfAdjointnessData :=
  Handoff.theoremAPI.criterionConclusion

/-- The handoff layer keeps compatibility with the Hamiltonian input. -/
theorem r4HilbertMathlibSelfAdjointOperatorHandoff_compatible
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (Handoff : R4HilbertMathlibSelfAdjointOperatorHandoffData I TR M) :
    M.mathlibOperatorCompatibleWithHamiltonianInput :=
  Handoff.theoremAPI.compatibleWithHamiltonianInput

/-- The handoff layer keeps the mathlib self-adjoint object readiness witness. -/
theorem r4HilbertMathlibSelfAdjointOperatorHandoff_object_ready
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (Handoff : R4HilbertMathlibSelfAdjointOperatorHandoffData I TR M) :
    M.mathlibSelfAdjointObjectReady :=
  Handoff.theoremAPI.objectReady

/-- The handoff package is ready as a handoff object. -/
theorem r4HilbertMathlibSelfAdjointOperatorHandoff_ready
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (Handoff : R4HilbertMathlibSelfAdjointOperatorHandoffData I TR M) :
    Handoff.mathlibSelfAdjointOperatorHandoffReady :=
  Handoff.mathlibSelfAdjointOperatorHandoffReady_holds

/-- The handoff package is compatible with a future spectral-theorem input layer. -/
theorem r4HilbertMathlibSelfAdjointOperatorHandoff_spectral_theorem_input_compatible
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (Handoff : R4HilbertMathlibSelfAdjointOperatorHandoffData I TR M) :
    Handoff.spectralTheoremInputCompatible :=
  Handoff.spectralTheoremInputCompatible_holds

/-- Combined handoff theorem for the mathlib self-adjoint R4 operator object.

This theorem is still prior to the spectral theorem. It only packages the actual
mathlib self-adjoint operator predicate together with the criterion conclusion,
Hamiltonian compatibility, object readiness, handoff readiness, and compatibility
with a later spectral-theorem input layer. -/
theorem r4HilbertMathlibSelfAdjointOperatorHandoff_constructed
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (Handoff : R4HilbertMathlibSelfAdjointOperatorHandoffData I TR M) :
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
        M.mathlibOperatorCompatibleWithHamiltonianInput ∧
          M.mathlibSelfAdjointObjectReady ∧
            Handoff.mathlibSelfAdjointOperatorHandoffReady ∧
              Handoff.spectralTheoremInputCompatible :=
  ⟨r4HilbertMathlibSelfAdjointOperatorHandoff_self_adjoint I TR Handoff,
    r4HilbertMathlibSelfAdjointOperatorHandoff_criterion_proved I TR Handoff,
    r4HilbertMathlibSelfAdjointOperatorHandoff_compatible I TR Handoff,
    r4HilbertMathlibSelfAdjointOperatorHandoff_object_ready I TR Handoff,
    r4HilbertMathlibSelfAdjointOperatorHandoff_ready I TR Handoff,
    r4HilbertMathlibSelfAdjointOperatorHandoff_spectral_theorem_input_compatible I TR Handoff⟩

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
