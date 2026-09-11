import MGAP4D.MathlibAnalytic.R4HilbertMathlibSelfAdjointOperatorHandoffAPI
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

/-- Input package for a later R4 mathlib spectral-theorem layer.

This structure receives the mathlib self-adjoint operator handoff from the prior
layer and records only that the spectral-theorem input is ready and still
separated from spectral-gap assertions. It does not state a spectral theorem,
construct a spectral measure, introduce functional calculus, or assert a positive
spectral lower bound. -/
structure R4HilbertMathlibSpectralTheoremInputData
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) where
  selfAdjointOperatorHandoff : R4HilbertMathlibSelfAdjointOperatorHandoffData I TR M
  spectralTheoremInputReady : Prop
  spectralTheoremInputReady_holds : spectralTheoremInputReady
  spectralTheoremInputSeparatedFromGap : Prop
  spectralTheoremInputSeparatedFromGap_holds : spectralTheoremInputSeparatedFromGap
  spectralMeasureConstructionDeferred : Prop
  spectralMeasureConstructionDeferred_holds : spectralMeasureConstructionDeferred

/-- The handoff package underlying the spectral-theorem input layer. -/
def r4HilbertMathlibSpectralTheoremInputHandoff
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (ST : R4HilbertMathlibSpectralTheoremInputData I TR M) :
    R4HilbertMathlibSelfAdjointOperatorHandoffData I TR M :=
  ST.selfAdjointOperatorHandoff

/-- The self-adjointness input data underlying the spectral-theorem input layer. -/
def r4HilbertMathlibSpectralTheoremInputSelfAdjointnessData
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (_ST : R4HilbertMathlibSpectralTheoremInputData I TR M) :
    R4HilbertSelfAdjointnessInputData I TR :=
  M.selfAdjointnessData

/-- The mathlib `LinearPMap` made available as spectral-theorem input. -/
def r4HilbertMathlibSpectralTheoremInputOperator
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (_ST : R4HilbertMathlibSpectralTheoremInputData I TR M) :
    (letI : NormedAddCommGroup
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
    letI : InnerProductSpace ℝ
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
    r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData →ₗ.[ℝ]
      r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
  M.mathlibOperator

/-- The spectral-theorem input layer carries the actual mathlib self-adjointness predicate. -/
theorem r4HilbertMathlibSpectralTheoremInput_self_adjoint
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (ST : R4HilbertMathlibSpectralTheoremInputData I TR M) :
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
  r4HilbertMathlibSelfAdjointOperatorHandoff_self_adjoint I TR
    ST.selfAdjointOperatorHandoff

/-- The spectral-theorem input layer keeps the prior criterion conclusion. -/
theorem r4HilbertMathlibSpectralTheoremInput_criterion_proved
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (ST : R4HilbertMathlibSpectralTheoremInputData I TR M) :
    r4HilbertSelfAdjointnessConclusion I TR M.selfAdjointnessData :=
  r4HilbertMathlibSelfAdjointOperatorHandoff_criterion_proved I TR
    ST.selfAdjointOperatorHandoff

/-- The spectral-theorem input layer keeps Hamiltonian-input compatibility. -/
theorem r4HilbertMathlibSpectralTheoremInput_compatible
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (ST : R4HilbertMathlibSpectralTheoremInputData I TR M) :
    M.mathlibOperatorCompatibleWithHamiltonianInput :=
  r4HilbertMathlibSelfAdjointOperatorHandoff_compatible I TR
    ST.selfAdjointOperatorHandoff

/-- The spectral-theorem input layer keeps the handoff readiness witness. -/
theorem r4HilbertMathlibSpectralTheoremInput_handoff_ready
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (ST : R4HilbertMathlibSpectralTheoremInputData I TR M) :
    ST.selfAdjointOperatorHandoff.mathlibSelfAdjointOperatorHandoffReady :=
  r4HilbertMathlibSelfAdjointOperatorHandoff_ready I TR
    ST.selfAdjointOperatorHandoff

/-- The spectral-theorem input layer records compatibility with a future spectral theorem layer. -/
theorem r4HilbertMathlibSpectralTheoremInput_handoff_compatible
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (ST : R4HilbertMathlibSpectralTheoremInputData I TR M) :
    ST.selfAdjointOperatorHandoff.spectralTheoremInputCompatible :=
  r4HilbertMathlibSelfAdjointOperatorHandoff_spectral_theorem_input_compatible I TR
    ST.selfAdjointOperatorHandoff

/-- The spectral-theorem input package is ready. -/
theorem r4HilbertMathlibSpectralTheoremInput_ready
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (ST : R4HilbertMathlibSpectralTheoremInputData I TR M) :
    ST.spectralTheoremInputReady :=
  ST.spectralTheoremInputReady_holds

/-- The spectral-theorem input remains separated from spectral-gap assertions. -/
theorem r4HilbertMathlibSpectralTheoremInput_separated_from_gap
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (ST : R4HilbertMathlibSpectralTheoremInputData I TR M) :
    ST.spectralTheoremInputSeparatedFromGap :=
  ST.spectralTheoremInputSeparatedFromGap_holds

/-- Spectral-measure construction is explicitly deferred to a later layer. -/
theorem r4HilbertMathlibSpectralTheoremInput_measure_deferred
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (ST : R4HilbertMathlibSpectralTheoremInputData I TR M) :
    ST.spectralMeasureConstructionDeferred :=
  ST.spectralMeasureConstructionDeferred_holds

/-- Combined input theorem for the later R4 mathlib spectral-theorem layer. -/
theorem r4HilbertMathlibSpectralTheoremInput_constructed
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (ST : R4HilbertMathlibSpectralTheoremInputData I TR M) :
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
          ST.selfAdjointOperatorHandoff.mathlibSelfAdjointOperatorHandoffReady ∧
            ST.selfAdjointOperatorHandoff.spectralTheoremInputCompatible ∧
              ST.spectralTheoremInputReady ∧
                ST.spectralTheoremInputSeparatedFromGap ∧
                  ST.spectralMeasureConstructionDeferred :=
  ⟨r4HilbertMathlibSpectralTheoremInput_self_adjoint I TR ST,
    r4HilbertMathlibSpectralTheoremInput_criterion_proved I TR ST,
    r4HilbertMathlibSpectralTheoremInput_compatible I TR ST,
    r4HilbertMathlibSpectralTheoremInput_handoff_ready I TR ST,
    r4HilbertMathlibSpectralTheoremInput_handoff_compatible I TR ST,
    r4HilbertMathlibSpectralTheoremInput_ready I TR ST,
    r4HilbertMathlibSpectralTheoremInput_separated_from_gap I TR ST,
    r4HilbertMathlibSpectralTheoremInput_measure_deferred I TR ST⟩

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
