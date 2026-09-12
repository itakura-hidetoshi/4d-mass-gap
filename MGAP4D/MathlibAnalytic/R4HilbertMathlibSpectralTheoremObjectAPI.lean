import MGAP4D.MathlibAnalytic.R4HilbertMathlibSpectralTheoremInput
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

/-- Readiness API for a later R4 mathlib spectral-theorem object layer.

This structure receives the spectral-theorem input package and records that the
object-facing layer is ready to hand off the mathlib self-adjoint operator. It
still does not state or invoke a spectral theorem, construct a spectral measure,
introduce functional calculus, construct spectral projections, or assert a
spectral gap. -/
structure R4HilbertMathlibSpectralTheoremObjectAPIData
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) where
  spectralTheoremInput : R4HilbertMathlibSpectralTheoremInputData I TR M
  spectralTheoremObjectReady : Prop
  spectralTheoremObjectReady_holds : spectralTheoremObjectReady
  spectralTheoremObjectSeparatedFromGap : Prop
  spectralTheoremObjectSeparatedFromGap_holds : spectralTheoremObjectSeparatedFromGap
  spectralTheoremObjectMeasureDeferred : Prop
  spectralTheoremObjectMeasureDeferred_holds : spectralTheoremObjectMeasureDeferred

/-- The spectral-theorem input package carried by the object API layer. -/
def r4HilbertMathlibSpectralTheoremObjectAPIInput
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (Obj : R4HilbertMathlibSpectralTheoremObjectAPIData I TR M) :
    R4HilbertMathlibSpectralTheoremInputData I TR M :=
  Obj.spectralTheoremInput

/-- The self-adjointness input data carried by the object API layer. -/
def r4HilbertMathlibSpectralTheoremObjectAPISelfAdjointnessData
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (_Obj : R4HilbertMathlibSpectralTheoremObjectAPIData I TR M) :
    R4HilbertSelfAdjointnessInputData I TR :=
  M.selfAdjointnessData

/-- The mathlib `LinearPMap` exposed by the object API layer. -/
def r4HilbertMathlibSpectralTheoremObjectAPIOperator
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (_Obj : R4HilbertMathlibSpectralTheoremObjectAPIData I TR M) :
    (letI : NormedAddCommGroup
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
    letI : InnerProductSpace ℝ
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
    r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData →ₗ.[ℝ]
      r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
  M.mathlibOperator

/-- The object API layer carries the actual mathlib `IsSelfAdjoint` predicate. -/
theorem r4HilbertMathlibSpectralTheoremObjectAPI_self_adjoint
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (Obj : R4HilbertMathlibSpectralTheoremObjectAPIData I TR M) :
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
  r4HilbertMathlibSpectralTheoremInput_self_adjoint I TR Obj.spectralTheoremInput

/-- The object API layer keeps the criterion-level self-adjointness conclusion. -/
theorem r4HilbertMathlibSpectralTheoremObjectAPI_criterion_proved
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (Obj : R4HilbertMathlibSpectralTheoremObjectAPIData I TR M) :
    r4HilbertSelfAdjointnessConclusion I TR M.selfAdjointnessData :=
  r4HilbertMathlibSpectralTheoremInput_criterion_proved I TR Obj.spectralTheoremInput

/-- The object API layer keeps Hamiltonian-input compatibility. -/
theorem r4HilbertMathlibSpectralTheoremObjectAPI_compatible
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (Obj : R4HilbertMathlibSpectralTheoremObjectAPIData I TR M) :
    M.mathlibOperatorCompatibleWithHamiltonianInput :=
  r4HilbertMathlibSpectralTheoremInput_compatible I TR Obj.spectralTheoremInput

/-- The object API layer keeps spectral-theorem input readiness. -/
theorem r4HilbertMathlibSpectralTheoremObjectAPI_input_ready
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (Obj : R4HilbertMathlibSpectralTheoremObjectAPIData I TR M) :
    Obj.spectralTheoremInput.spectralTheoremInputReady :=
  r4HilbertMathlibSpectralTheoremInput_ready I TR Obj.spectralTheoremInput

/-- The object API layer keeps the input-level separation from gap assertions. -/
theorem r4HilbertMathlibSpectralTheoremObjectAPI_input_separated_from_gap
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (Obj : R4HilbertMathlibSpectralTheoremObjectAPIData I TR M) :
    Obj.spectralTheoremInput.spectralTheoremInputSeparatedFromGap :=
  r4HilbertMathlibSpectralTheoremInput_separated_from_gap I TR Obj.spectralTheoremInput

/-- The object API layer keeps the input-level spectral-measure deferral. -/
theorem r4HilbertMathlibSpectralTheoremObjectAPI_input_measure_deferred
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (Obj : R4HilbertMathlibSpectralTheoremObjectAPIData I TR M) :
    Obj.spectralTheoremInput.spectralMeasureConstructionDeferred :=
  r4HilbertMathlibSpectralTheoremInput_measure_deferred I TR Obj.spectralTheoremInput

/-- The object API layer itself is ready. -/
theorem r4HilbertMathlibSpectralTheoremObjectAPI_ready
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (Obj : R4HilbertMathlibSpectralTheoremObjectAPIData I TR M) :
    Obj.spectralTheoremObjectReady :=
  Obj.spectralTheoremObjectReady_holds

/-- The object API layer is still separated from spectral-gap assertions. -/
theorem r4HilbertMathlibSpectralTheoremObjectAPI_separated_from_gap
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (Obj : R4HilbertMathlibSpectralTheoremObjectAPIData I TR M) :
    Obj.spectralTheoremObjectSeparatedFromGap :=
  Obj.spectralTheoremObjectSeparatedFromGap_holds

/-- Spectral-measure construction remains deferred at the object API layer. -/
theorem r4HilbertMathlibSpectralTheoremObjectAPI_measure_deferred
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (Obj : R4HilbertMathlibSpectralTheoremObjectAPIData I TR M) :
    Obj.spectralTheoremObjectMeasureDeferred :=
  Obj.spectralTheoremObjectMeasureDeferred_holds

/-- Combined object API theorem for the later R4 mathlib spectral-theorem layer. -/
theorem r4HilbertMathlibSpectralTheoremObjectAPI_constructed
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (Obj : R4HilbertMathlibSpectralTheoremObjectAPIData I TR M) :
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
          Obj.spectralTheoremInput.spectralTheoremInputReady ∧
            Obj.spectralTheoremInput.spectralTheoremInputSeparatedFromGap ∧
              Obj.spectralTheoremInput.spectralMeasureConstructionDeferred ∧
                Obj.spectralTheoremObjectReady ∧
                  Obj.spectralTheoremObjectSeparatedFromGap ∧
                    Obj.spectralTheoremObjectMeasureDeferred :=
  ⟨r4HilbertMathlibSpectralTheoremObjectAPI_self_adjoint I TR Obj,
    r4HilbertMathlibSpectralTheoremObjectAPI_criterion_proved I TR Obj,
    r4HilbertMathlibSpectralTheoremObjectAPI_compatible I TR Obj,
    r4HilbertMathlibSpectralTheoremObjectAPI_input_ready I TR Obj,
    r4HilbertMathlibSpectralTheoremObjectAPI_input_separated_from_gap I TR Obj,
    r4HilbertMathlibSpectralTheoremObjectAPI_input_measure_deferred I TR Obj,
    r4HilbertMathlibSpectralTheoremObjectAPI_ready I TR Obj,
    r4HilbertMathlibSpectralTheoremObjectAPI_separated_from_gap I TR Obj,
    r4HilbertMathlibSpectralTheoremObjectAPI_measure_deferred I TR Obj⟩

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
