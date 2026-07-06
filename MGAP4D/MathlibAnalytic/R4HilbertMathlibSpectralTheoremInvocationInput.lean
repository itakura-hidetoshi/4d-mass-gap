import MGAP4D.MathlibAnalytic.R4HilbertMathlibSpectralTheoremObjectHandoff
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

/-- Input package for a later R4 mathlib spectral-theorem invocation layer.

This structure receives the object handoff package and records that the
invocation-facing input is ready. It still does not state or invoke a spectral
theorem, construct a spectral measure, introduce functional calculus, construct
spectral projections, or assert a spectral gap. -/
structure R4HilbertMathlibSpectralTheoremInvocationInputData
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) where
  objectHandoff : R4HilbertMathlibSpectralTheoremObjectHandoffData I TR M
  spectralTheoremInvocationInputReady : Prop
  spectralTheoremInvocationInputReady_holds : spectralTheoremInvocationInputReady
  spectralTheoremInvocationStillDeferred : Prop
  spectralTheoremInvocationStillDeferred_holds : spectralTheoremInvocationStillDeferred
  spectralMeasureConstructionStillDeferred : Prop
  spectralMeasureConstructionStillDeferred_holds : spectralMeasureConstructionStillDeferred
  spectralGapAssertionStillDeferred : Prop
  spectralGapAssertionStillDeferred_holds : spectralGapAssertionStillDeferred

/-- The object handoff package carried by the invocation input layer. -/
def r4HilbertMathlibSpectralTheoremInvocationInputHandoff
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (Inv : R4HilbertMathlibSpectralTheoremInvocationInputData I TR M) :
    R4HilbertMathlibSpectralTheoremObjectHandoffData I TR M :=
  Inv.objectHandoff

/-- The object API package carried by the invocation input layer. -/
def r4HilbertMathlibSpectralTheoremInvocationInputObjectAPI
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (Inv : R4HilbertMathlibSpectralTheoremInvocationInputData I TR M) :
    R4HilbertMathlibSpectralTheoremObjectAPIData I TR M :=
  Inv.objectHandoff.objectAPI

/-- The mathlib `LinearPMap` exposed by the invocation input layer. -/
def r4HilbertMathlibSpectralTheoremInvocationInputOperator
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (_Inv : R4HilbertMathlibSpectralTheoremInvocationInputData I TR M) :
    (letI : NormedAddCommGroup
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
    letI : InnerProductSpace ℝ
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
    r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData →ₗ.[ℝ]
      r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
  M.mathlibOperator

/-- The invocation input layer carries the actual mathlib self-adjointness predicate. -/
theorem r4HilbertMathlibSpectralTheoremInvocationInput_self_adjoint
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (Inv : R4HilbertMathlibSpectralTheoremInvocationInputData I TR M) :
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
  r4HilbertMathlibSpectralTheoremObjectHandoff_self_adjoint I TR Inv.objectHandoff

/-- The invocation input layer keeps the criterion-level self-adjointness conclusion. -/
theorem r4HilbertMathlibSpectralTheoremInvocationInput_criterion_proved
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (Inv : R4HilbertMathlibSpectralTheoremInvocationInputData I TR M) :
    r4HilbertSelfAdjointnessConclusion I TR M.selfAdjointnessData :=
  r4HilbertMathlibSpectralTheoremObjectHandoff_criterion_proved I TR Inv.objectHandoff

/-- The invocation input layer keeps Hamiltonian-input compatibility. -/
theorem r4HilbertMathlibSpectralTheoremInvocationInput_compatible
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (Inv : R4HilbertMathlibSpectralTheoremInvocationInputData I TR M) :
    M.mathlibOperatorCompatibleWithHamiltonianInput :=
  r4HilbertMathlibSpectralTheoremObjectHandoff_compatible I TR Inv.objectHandoff

/-- The object handoff package carried by the invocation input is ready. -/
theorem r4HilbertMathlibSpectralTheoremInvocationInput_handoff_ready
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (Inv : R4HilbertMathlibSpectralTheoremInvocationInputData I TR M) :
    Inv.objectHandoff.spectralTheoremObjectHandoffReady :=
  r4HilbertMathlibSpectralTheoremObjectHandoff_ready I TR Inv.objectHandoff

/-- The object handoff package confirms spectral-theorem invocation remains deferred. -/
theorem r4HilbertMathlibSpectralTheoremInvocationInput_handoff_invocation_deferred
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (Inv : R4HilbertMathlibSpectralTheoremInvocationInputData I TR M) :
    Inv.objectHandoff.spectralTheoremInvocationDeferred :=
  r4HilbertMathlibSpectralTheoremObjectHandoff_invocation_deferred I TR Inv.objectHandoff

/-- The object handoff package confirms spectral-gap assertions remain deferred. -/
theorem r4HilbertMathlibSpectralTheoremInvocationInput_handoff_gap_deferred
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (Inv : R4HilbertMathlibSpectralTheoremInvocationInputData I TR M) :
    Inv.objectHandoff.spectralGapAssertionDeferred :=
  r4HilbertMathlibSpectralTheoremObjectHandoff_gap_deferred I TR Inv.objectHandoff

/-- The invocation input package itself is ready. -/
theorem r4HilbertMathlibSpectralTheoremInvocationInput_ready
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (Inv : R4HilbertMathlibSpectralTheoremInvocationInputData I TR M) :
    Inv.spectralTheoremInvocationInputReady :=
  Inv.spectralTheoremInvocationInputReady_holds

/-- The actual spectral-theorem invocation is still deferred at this input layer. -/
theorem r4HilbertMathlibSpectralTheoremInvocationInput_invocation_deferred
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (Inv : R4HilbertMathlibSpectralTheoremInvocationInputData I TR M) :
    Inv.spectralTheoremInvocationStillDeferred :=
  Inv.spectralTheoremInvocationStillDeferred_holds

/-- Spectral-measure construction is still deferred at this input layer. -/
theorem r4HilbertMathlibSpectralTheoremInvocationInput_measure_deferred
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (Inv : R4HilbertMathlibSpectralTheoremInvocationInputData I TR M) :
    Inv.spectralMeasureConstructionStillDeferred :=
  Inv.spectralMeasureConstructionStillDeferred_holds

/-- Spectral-gap assertions are still deferred at this input layer. -/
theorem r4HilbertMathlibSpectralTheoremInvocationInput_gap_deferred
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (Inv : R4HilbertMathlibSpectralTheoremInvocationInputData I TR M) :
    Inv.spectralGapAssertionStillDeferred :=
  Inv.spectralGapAssertionStillDeferred_holds

/-- Combined input theorem for a later R4 mathlib spectral-theorem invocation layer. -/
theorem r4HilbertMathlibSpectralTheoremInvocationInput_constructed
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (Inv : R4HilbertMathlibSpectralTheoremInvocationInputData I TR M) :
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
          Inv.objectHandoff.spectralTheoremObjectHandoffReady ∧
            Inv.objectHandoff.spectralTheoremInvocationDeferred ∧
              Inv.objectHandoff.spectralGapAssertionDeferred ∧
                Inv.spectralTheoremInvocationInputReady ∧
                  Inv.spectralTheoremInvocationStillDeferred ∧
                    Inv.spectralMeasureConstructionStillDeferred ∧
                      Inv.spectralGapAssertionStillDeferred :=
  ⟨r4HilbertMathlibSpectralTheoremInvocationInput_self_adjoint I TR Inv,
    r4HilbertMathlibSpectralTheoremInvocationInput_criterion_proved I TR Inv,
    r4HilbertMathlibSpectralTheoremInvocationInput_compatible I TR Inv,
    r4HilbertMathlibSpectralTheoremInvocationInput_handoff_ready I TR Inv,
    r4HilbertMathlibSpectralTheoremInvocationInput_handoff_invocation_deferred I TR Inv,
    r4HilbertMathlibSpectralTheoremInvocationInput_handoff_gap_deferred I TR Inv,
    r4HilbertMathlibSpectralTheoremInvocationInput_ready I TR Inv,
    r4HilbertMathlibSpectralTheoremInvocationInput_invocation_deferred I TR Inv,
    r4HilbertMathlibSpectralTheoremInvocationInput_measure_deferred I TR Inv,
    r4HilbertMathlibSpectralTheoremInvocationInput_gap_deferred I TR Inv⟩

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
