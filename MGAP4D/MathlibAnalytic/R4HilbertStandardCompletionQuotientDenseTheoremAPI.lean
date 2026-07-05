import MGAP4D.MathlibAnalytic.R4HilbertStandardCompletionQuotientDenseData
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

def r4HilbertStandardCompletionQuotientDenseTheoremRouteData
    (M : R4HilbertStandardCompletionQuotientDenseData I TR) :
    R4HilbertCompletedDenseRangeData I TR :=
  M.routeData

def r4HilbertStandardCompletionQuotientDenseTheoremCarrier
    (M : R4HilbertStandardCompletionQuotientDenseData I TR) : Type :=
  r4HilbertStandardCompletionCarrier I TR M.routeData

def r4HilbertStandardCompletionQuotientDenseTheoremPreMap
    (M : R4HilbertStandardCompletionQuotientDenseData I TR) :
    r4HilbertCompletedActualPreCarrier I TR M.routeData →
      r4HilbertStandardCompletionQuotientDenseTheoremCarrier I TR M :=
  r4HilbertStandardCompletionMap I TR M.routeData

def r4HilbertStandardCompletionQuotientDenseTheoremQuotientMap
    (M : R4HilbertStandardCompletionQuotientDenseData I TR) :
    quotientCarrier I →
      r4HilbertStandardCompletionQuotientDenseTheoremCarrier I TR M :=
  r4HilbertStandardCompletionQuotientDenseMap I TR M

theorem r4HilbertStandardCompletionQuotientDenseTheorem_inner_product_nonempty
    (M : R4HilbertStandardCompletionQuotientDenseData I TR) :
    Nonempty
      (letI : NormedAddCommGroup (r4HilbertStandardCompletionCarrier I TR M.routeData) :=
        r4HilbertStandardCompletionNormedAddCommGroup I TR M.routeData
      InnerProductSpace ℝ (r4HilbertStandardCompletionCarrier I TR M.routeData)) :=
  r4HilbertStandardCompletion_inner_product_nonempty I TR M.routeData

theorem r4HilbertStandardCompletionQuotientDenseTheorem_complete_space
    (M : R4HilbertStandardCompletionQuotientDenseData I TR) :
    (letI : NormedAddCommGroup (r4HilbertStandardCompletionCarrier I TR M.routeData) :=
      r4HilbertStandardCompletionNormedAddCommGroup I TR M.routeData
    CompleteSpace (r4HilbertStandardCompletionCarrier I TR M.routeData)) :=
  r4HilbertStandardCompletion_complete_space I TR M.routeData

theorem r4HilbertStandardCompletionQuotientDenseTheorem_pre_dense
    (M : R4HilbertStandardCompletionQuotientDenseData I TR) :
    (letI : NormedAddCommGroup (r4HilbertStandardCompletionCarrier I TR M.routeData) :=
      r4HilbertStandardCompletionNormedAddCommGroup I TR M.routeData
    DenseRange (r4HilbertStandardCompletionMap I TR M.routeData)) :=
  r4HilbertStandardCompletion_dense I TR M.routeData

theorem r4HilbertStandardCompletionQuotientDenseTheorem_quotient_dense
    (M : R4HilbertStandardCompletionQuotientDenseData I TR) :
    (letI : NormedAddCommGroup (r4HilbertStandardCompletionCarrier I TR M.routeData) :=
      r4HilbertStandardCompletionNormedAddCommGroup I TR M.routeData
    DenseRange (r4HilbertStandardCompletionQuotientDenseMap I TR M)) :=
  r4HilbertStandardCompletion_quotient_dense_actual I TR M

theorem r4HilbertStandardCompletionQuotientDenseTheorem_quotient_factors
    (M : R4HilbertStandardCompletionQuotientDenseData I TR)
    (q : quotientCarrier I) :
    r4HilbertStandardCompletionQuotientDenseMap I TR M q =
      r4HilbertStandardCompletionMap I TR M.routeData
        (M.routeData.completedData.preCompletionData.quotientToPreHilbert q) :=
  r4HilbertStandardCompletion_quotient_dense_factors I TR M q

theorem r4HilbertStandardCompletionQuotientDenseTheorem_route_ready
    (M : R4HilbertStandardCompletionQuotientDenseData I TR) :
    M.routeData.completedData.preCompletionData.preCompletionReady ∧
      M.routeData.completedData.completedHilbertReady ∧
        M.routeData.completedDenseRangeReady ∧ M.quotientToStandardDenseReady :=
  r4HilbertStandardCompletion_quotient_dense_route_bundle I TR M

theorem r4HilbertStandardCompletionQuotientDenseTheorem_constructed
    (M : R4HilbertStandardCompletionQuotientDenseData I TR) :
    Nonempty
      (letI : NormedAddCommGroup (r4HilbertStandardCompletionCarrier I TR M.routeData) :=
        r4HilbertStandardCompletionNormedAddCommGroup I TR M.routeData
      InnerProductSpace ℝ (r4HilbertStandardCompletionCarrier I TR M.routeData)) ∧
      (letI : NormedAddCommGroup (r4HilbertStandardCompletionCarrier I TR M.routeData) :=
        r4HilbertStandardCompletionNormedAddCommGroup I TR M.routeData
      CompleteSpace (r4HilbertStandardCompletionCarrier I TR M.routeData)) ∧
        (letI : NormedAddCommGroup (r4HilbertStandardCompletionCarrier I TR M.routeData) :=
          r4HilbertStandardCompletionNormedAddCommGroup I TR M.routeData
        DenseRange (r4HilbertStandardCompletionMap I TR M.routeData)) ∧
          (letI : NormedAddCommGroup (r4HilbertStandardCompletionCarrier I TR M.routeData) :=
            r4HilbertStandardCompletionNormedAddCommGroup I TR M.routeData
          DenseRange (r4HilbertStandardCompletionQuotientDenseMap I TR M)) :=
  r4HilbertStandardCompletion_hilbert_quotient_dense_constructed I TR M

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
