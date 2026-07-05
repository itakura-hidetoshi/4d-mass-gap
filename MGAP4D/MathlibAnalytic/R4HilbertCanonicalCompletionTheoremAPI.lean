import MGAP4D.MathlibAnalytic.R4HilbertCanonicalCompletionRouteData
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

def r4HilbertCanonicalCompletionTheoremCarrier
    (M : R4HilbertCanonicalCompletionRouteData I TR) : Type :=
  r4HilbertCanonicalCompletionCarrier I TR M

def r4HilbertCanonicalCompletionTheoremMap
    (M : R4HilbertCanonicalCompletionRouteData I TR) :
    r4HilbertCompletedActualPreCarrier I TR M.theoremData →
      r4HilbertCanonicalCompletionTheoremCarrier I TR M :=
  r4HilbertCanonicalCompletionMap I TR M

def r4HilbertCanonicalCompletionTheoremInnerProductSpaceData
    (M : R4HilbertCanonicalCompletionRouteData I TR) :
    (letI : NormedAddCommGroup (r4HilbertCanonicalCompletionTheoremCarrier I TR M) :=
      r4HilbertCanonicalCompletionNormedAddCommGroup I TR M
    letI : NormedSpace ℝ (r4HilbertCanonicalCompletionTheoremCarrier I TR M) :=
      M.canonicalNormedSpaceReal
    InnerProductSpace ℝ (r4HilbertCanonicalCompletionTheoremCarrier I TR M)) :=
  r4HilbertCanonicalCompletionInnerProductSpaceReal I TR M

theorem r4HilbertCanonicalCompletionTheorem_complete_space
    (M : R4HilbertCanonicalCompletionRouteData I TR) :
    (letI : NormedAddCommGroup (r4HilbertCanonicalCompletionTheoremCarrier I TR M) :=
      r4HilbertCanonicalCompletionNormedAddCommGroup I TR M
    CompleteSpace (r4HilbertCanonicalCompletionTheoremCarrier I TR M)) :=
  r4HilbertCanonicalCompletion_complete_space I TR M

theorem r4HilbertCanonicalCompletionTheorem_dense
    (M : R4HilbertCanonicalCompletionRouteData I TR) :
    (letI : NormedAddCommGroup (r4HilbertCanonicalCompletionTheoremCarrier I TR M) :=
      r4HilbertCanonicalCompletionNormedAddCommGroup I TR M
    DenseRange (r4HilbertCanonicalCompletionTheoremMap I TR M)) :=
  r4HilbertCanonicalCompletion_dense I TR M

theorem r4HilbertCanonicalCompletionTheorem_continuous
    (M : R4HilbertCanonicalCompletionRouteData I TR) :
    (letI : NormedAddCommGroup (r4HilbertCompletedActualPreCarrier I TR M.theoremData) :=
      M.theoremData.completedData.preCompletionData.instNormedAddCommGroup
    letI : NormedAddCommGroup (r4HilbertCanonicalCompletionTheoremCarrier I TR M) :=
      r4HilbertCanonicalCompletionNormedAddCommGroup I TR M
    Continuous (r4HilbertCanonicalCompletionTheoremMap I TR M)) :=
  r4HilbertCanonicalCompletion_continuous I TR M

theorem r4HilbertCanonicalCompletionTheorem_left_inverse
    (M : R4HilbertCanonicalCompletionRouteData I TR) :
    M.canonicalLeftInverse :=
  r4HilbertCanonicalCompletion_left_inverse I TR M

theorem r4HilbertCanonicalCompletionTheorem_right_inverse
    (M : R4HilbertCanonicalCompletionRouteData I TR) :
    M.canonicalRightInverse :=
  r4HilbertCanonicalCompletion_right_inverse I TR M

theorem r4HilbertCanonicalCompletionTheorem_compatible
    (M : R4HilbertCanonicalCompletionRouteData I TR) :
    M.canonicalCompatibleWithCompletedMap :=
  r4HilbertCanonicalCompletion_compatible I TR M

theorem r4HilbertCanonicalCompletionTheorem_route_ready
    (M : R4HilbertCanonicalCompletionRouteData I TR) :
    M.canonicalRouteReady :=
  r4HilbertCanonicalCompletion_route_ready I TR M

theorem r4HilbertCanonicalCompletionTheorem_complete_dense_continuous_bundle
    (M : R4HilbertCanonicalCompletionRouteData I TR) :
    (letI : NormedAddCommGroup (r4HilbertCanonicalCompletionTheoremCarrier I TR M) :=
      r4HilbertCanonicalCompletionNormedAddCommGroup I TR M
    CompleteSpace (r4HilbertCanonicalCompletionTheoremCarrier I TR M)) ∧
      (letI : NormedAddCommGroup (r4HilbertCanonicalCompletionTheoremCarrier I TR M) :=
        r4HilbertCanonicalCompletionNormedAddCommGroup I TR M
      DenseRange (r4HilbertCanonicalCompletionTheoremMap I TR M)) ∧
        (letI : NormedAddCommGroup (r4HilbertCompletedActualPreCarrier I TR M.theoremData) :=
          M.theoremData.completedData.preCompletionData.instNormedAddCommGroup
        letI : NormedAddCommGroup (r4HilbertCanonicalCompletionTheoremCarrier I TR M) :=
          r4HilbertCanonicalCompletionNormedAddCommGroup I TR M
        Continuous (r4HilbertCanonicalCompletionTheoremMap I TR M)) :=
  ⟨r4HilbertCanonicalCompletionTheorem_complete_space I TR M,
    r4HilbertCanonicalCompletionTheorem_dense I TR M,
    r4HilbertCanonicalCompletionTheorem_continuous I TR M⟩

theorem r4HilbertCanonicalCompletionTheorem_comparison_bundle
    (M : R4HilbertCanonicalCompletionRouteData I TR) :
    M.canonicalLeftInverse ∧ M.canonicalRightInverse ∧
      M.canonicalCompatibleWithCompletedMap ∧ M.canonicalRouteReady :=
  ⟨r4HilbertCanonicalCompletionTheorem_left_inverse I TR M,
    r4HilbertCanonicalCompletionTheorem_right_inverse I TR M,
    r4HilbertCanonicalCompletionTheorem_compatible I TR M,
    r4HilbertCanonicalCompletionTheorem_route_ready I TR M⟩

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
