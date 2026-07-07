import MGAP4D.MathlibAnalytic.R4HilbertMathlibSelfAdjointOperatorContinuousSelfAdjointRepresentative
import MGAP4D.MathlibAnalytic.R4HilbertMathlibSpectralTheoremInvocationInput
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

/-! Spectral invocation route using the bounded continuous representative. -/

/-- Combine the spectral-theorem invocation input layer with the continuous
self-adjoint representative supplied by the bounded actual route.

This is the first spectral-side package in which the invocation-facing input and
the actual bounded continuous representative are available together. It does not
claim a spectral measure, functional calculus, spectral projection, or spectral
gap. -/
theorem r4HilbertMathlibSpectralInvocationInput_unconditional_route_continuous_representative_package
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (hRoute : r4HilbertMathlibSelfAdjointOperatorUnconditionalBoundedRoute I TR)
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
    IsSelfAdjoint M.mathlibOperator ∧
      r4HilbertSelfAdjointnessConclusion I TR M.selfAdjointnessData ∧
        M.mathlibOperatorCompatibleWithHamiltonianInput ∧
          Inv.objectHandoff.spectralTheoremObjectHandoffReady ∧
            Inv.objectHandoff.spectralTheoremInvocationDeferred ∧
              Inv.objectHandoff.spectralGapAssertionDeferred ∧
                Inv.spectralTheoremInvocationInputReady ∧
                  Inv.spectralTheoremInvocationStillDeferred ∧
                    Inv.spectralMeasureConstructionStillDeferred ∧
                      Inv.spectralGapAssertionStillDeferred ∧
                        ∃ (B : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData →L[ℝ]
                            r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData),
                          B.toPMap ⊤ = M.mathlibOperator ∧
                            B.adjoint = B ∧
                            ∀ x y : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData,
                              inner ℝ (B x) y = inner ℝ x (B y)) := by
  letI : NormedAddCommGroup
      (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
    r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
  letI : InnerProductSpace ℝ
      (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
    r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
  letI : CompleteSpace
      (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
    r4HilbertMathlibSelfAdjointCarrierCompleteSpace I TR M.selfAdjointnessData
  refine ⟨
    r4HilbertMathlibSpectralTheoremInvocationInput_self_adjoint I TR Inv,
    r4HilbertMathlibSpectralTheoremInvocationInput_criterion_proved I TR Inv,
    r4HilbertMathlibSpectralTheoremInvocationInput_compatible I TR Inv,
    r4HilbertMathlibSpectralTheoremInvocationInput_handoff_ready I TR Inv,
    r4HilbertMathlibSpectralTheoremInvocationInput_handoff_invocation_deferred I TR Inv,
    r4HilbertMathlibSpectralTheoremInvocationInput_handoff_gap_deferred I TR Inv,
    r4HilbertMathlibSpectralTheoremInvocationInput_ready I TR Inv,
    r4HilbertMathlibSpectralTheoremInvocationInput_invocation_deferred I TR Inv,
    r4HilbertMathlibSpectralTheoremInvocationInput_measure_deferred I TR Inv,
    r4HilbertMathlibSpectralTheoremInvocationInput_gap_deferred I TR Inv,
    ?_⟩
  exact r4HilbertMathlibSelfAdjointOperator_unconditional_route_continuous_self_adjoint_representative
    I TR hRoute M

/-- The same package, retaining the actual-operator action formulas for later
functional-calculus and spectral-measure routing. -/
theorem r4HilbertMathlibSpectralInvocationInput_unconditional_route_continuous_action_package
    {M : R4HilbertMathlibSelfAdjointOperatorData I TR}
    (hRoute : r4HilbertMathlibSelfAdjointOperatorUnconditionalBoundedRoute I TR)
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
    Inv.spectralTheoremInvocationInputReady ∧
      Inv.spectralTheoremInvocationStillDeferred ∧
        Inv.spectralMeasureConstructionStillDeferred ∧
          Inv.spectralGapAssertionStillDeferred ∧
            ∃ (B : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData →L[ℝ]
                r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData),
              B.toPMap ⊤ = M.mathlibOperator ∧
                B.adjoint = B ∧
                (∀ x : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData,
                  x ∈ M.mathlibOperator.domain) ∧
                (∀ (x : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData)
                    (hx : x ∈ M.mathlibOperator.domain),
                  M.mathlibOperator ⟨x, hx⟩ = B x) ∧
                (∀ (x y : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData)
                    (hx : x ∈ M.mathlibOperator.domain),
                  inner ℝ (M.mathlibOperator ⟨x, hx⟩) y = inner ℝ x (B y)) ∧
                (∀ x y : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData,
                  inner ℝ (B x) y = inner ℝ x (B y))) := by
  letI : NormedAddCommGroup
      (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
    r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
  letI : InnerProductSpace ℝ
      (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
    r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
  letI : CompleteSpace
      (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
    r4HilbertMathlibSelfAdjointCarrierCompleteSpace I TR M.selfAdjointnessData
  refine ⟨
    r4HilbertMathlibSpectralTheoremInvocationInput_ready I TR Inv,
    r4HilbertMathlibSpectralTheoremInvocationInput_invocation_deferred I TR Inv,
    r4HilbertMathlibSpectralTheoremInvocationInput_measure_deferred I TR Inv,
    r4HilbertMathlibSpectralTheoremInvocationInput_gap_deferred I TR Inv,
    ?_⟩
  exact r4HilbertMathlibSelfAdjointOperator_unconditional_route_continuous_self_adjoint_action_package
    I TR hRoute M

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
