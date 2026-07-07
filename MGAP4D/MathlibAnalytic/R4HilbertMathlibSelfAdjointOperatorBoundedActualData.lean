import MGAP4D.MathlibAnalytic.R4HilbertMathlibSelfAdjointOperatorBoundedRealizationDischargeBridge
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

/-! Bounded actual data for the R4 mathlib self-adjoint operator. -/

/-- Companion data asserting that the actual R4 mathlib operator is realized by a
continuous linear representative on the full carrier.

This is the precise additional datum needed to make the actual R4 operator
bounded without carrying the older dense-submodule existence hypothesis around
as a theorem argument. -/
structure R4HilbertMathlibSelfAdjointOperatorBoundedActualData
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR) where
  continuousRepresentative :
    (letI : NormedAddCommGroup
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
    letI : InnerProductSpace ℝ
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
    r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData →L[ℝ]
      r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData)
  continuousRepresentative_eq_actual :
    (letI : NormedAddCommGroup
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
    letI : InnerProductSpace ℝ
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
    continuousRepresentative.toPMap ⊤ = M.mathlibOperator)

/-- The bounded actual data supplies the direct full-domain continuous
representative target. -/
theorem r4HilbertMathlibSelfAdjointOperator_bounded_actual_top_representative
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR)
    (BD : R4HilbertMathlibSelfAdjointOperatorBoundedActualData I TR M) :
    (letI : NormedAddCommGroup
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
    letI : InnerProductSpace ℝ
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
    ∃ (B : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData →L[ℝ]
          r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData),
      B.toPMap ⊤ = M.mathlibOperator) := by
  letI : NormedAddCommGroup
      (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
    r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
  letI : InnerProductSpace ℝ
      (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
    r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
  exact ⟨BD.continuousRepresentative, BD.continuousRepresentative_eq_actual⟩

/-- With bounded actual data, the full actual bounded representative package is
available without a separate existential bounded-realization theorem argument. -/
theorem r4HilbertMathlibSelfAdjointOperator_bounded_actual_package
    (M : R4HilbertMathlibSelfAdjointOperatorData I TR)
    (BD : R4HilbertMathlibSelfAdjointOperatorBoundedActualData I TR M) :
    (letI : NormedAddCommGroup
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierNormedAddCommGroup I TR M.selfAdjointnessData
    letI : InnerProductSpace ℝ
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierInnerProductSpace I TR M.selfAdjointnessData
    letI : CompleteSpace
        (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData) :=
      r4HilbertMathlibSelfAdjointCarrierCompleteSpace I TR M.selfAdjointnessData
    ∃ (B : r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData →L[ℝ]
          r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData),
      B.toPMap ⊤ = M.mathlibOperator ∧
        B.adjoint.toPMap ⊤ = M.mathlibOperator ∧
        B.toPMap ⊤ = B.adjoint.toPMap ⊤ ∧
        B.adjoint.toPMap ⊤ = B.toPMap ⊤ ∧
        B.adjoint = B ∧
        (B.toPMap ⊤).domain = ⊤ ∧
        (B.adjoint.toPMap ⊤).domain = ⊤ ∧
        M.mathlibOperator.domain = ⊤ ∧
        Dense (M.mathlibOperator.domain : Set
          (r4HilbertMathlibSelfAdjointCarrier I TR M.selfAdjointnessData)) ∧
        M.mathlibOperator.IsClosed ∧
        LinearPMap.adjoint M.mathlibOperator = M.mathlibOperator ∧
        M.mathlibOperator = LinearPMap.adjoint M.mathlibOperator ∧
        (LinearPMap.adjoint M.mathlibOperator).domain = M.mathlibOperator.domain ∧
        (LinearPMap.adjoint M.mathlibOperator).graph = M.mathlibOperator.graph ∧
        M.mathlibOperator.graph = M.mathlibOperator.graph.adjoint ∧
        M.mathlibOperator.graph.adjoint.toLinearPMap = M.mathlibOperator ∧
        M.mathlibOperator.IsFormalAdjoint M.mathlibOperator ∧
        M.mathlibOperator ≤ LinearPMap.adjoint M.mathlibOperator ∧
        LinearPMap.adjoint M.mathlibOperator ≤ M.mathlibOperator ∧
        (B.toPMap ⊤).graph = M.mathlibOperator.graph ∧
        (B.adjoint.toPMap ⊤).graph = M.mathlibOperator.graph ∧
        M.mathlibOperator.graph = (B.toPMap ⊤).graph ∧
        M.mathlibOperator.graph = (B.adjoint.toPMap ⊤).graph ∧
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
  have hTopRepresentative :=
    r4HilbertMathlibSelfAdjointOperator_bounded_actual_top_representative I TR M BD
  exact r4HilbertMathlibSelfAdjointOperator_actual_continuous_top_representative_package
    I TR M hTopRepresentative

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
