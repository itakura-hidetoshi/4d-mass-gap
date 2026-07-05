import MGAP4D.MathlibAnalytic.R4HilbertStandardCompletionQuotientRouteAPI
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

/-- Data upgrading the standard completion quotient route with actual dense
range of the quotient-to-standard-completion map. -/
structure R4HilbertStandardCompletionQuotientDenseData where
  routeData : R4HilbertCompletedDenseRangeData I TR
  quotientToStandardDenseActual :
    (letI : NormedAddCommGroup (r4HilbertStandardCompletionCarrier I TR routeData) :=
      r4HilbertStandardCompletionNormedAddCommGroup I TR routeData
    DenseRange (r4HilbertStandardCompletionQuotientMap I TR routeData))
  quotientToStandardDenseReady : Prop
  quotientToStandardDenseReady_holds : quotientToStandardDenseReady

def r4HilbertStandardCompletionQuotientDenseRouteData
    (M : R4HilbertStandardCompletionQuotientDenseData I TR) :
    R4HilbertCompletedDenseRangeData I TR :=
  M.routeData

def r4HilbertStandardCompletionQuotientDenseMap
    (M : R4HilbertStandardCompletionQuotientDenseData I TR) :
    quotientCarrier I → r4HilbertStandardCompletionCarrier I TR M.routeData :=
  r4HilbertStandardCompletionQuotientMap I TR M.routeData

theorem r4HilbertStandardCompletion_quotient_dense_actual
    (M : R4HilbertStandardCompletionQuotientDenseData I TR) :
    (letI : NormedAddCommGroup (r4HilbertStandardCompletionCarrier I TR M.routeData) :=
      r4HilbertStandardCompletionNormedAddCommGroup I TR M.routeData
    DenseRange (r4HilbertStandardCompletionQuotientDenseMap I TR M)) :=
  M.quotientToStandardDenseActual

theorem r4HilbertStandardCompletion_quotient_dense_ready
    (M : R4HilbertStandardCompletionQuotientDenseData I TR) :
    M.quotientToStandardDenseReady :=
  M.quotientToStandardDenseReady_holds

theorem r4HilbertStandardCompletion_quotient_dense_factors
    (M : R4HilbertStandardCompletionQuotientDenseData I TR)
    (q : quotientCarrier I) :
    r4HilbertStandardCompletionQuotientDenseMap I TR M q =
      r4HilbertStandardCompletionMap I TR M.routeData
        (M.routeData.completedData.preCompletionData.quotientToPreHilbert q) :=
  rfl

theorem r4HilbertStandardCompletion_quotient_dense_route_bundle
    (M : R4HilbertStandardCompletionQuotientDenseData I TR) :
    M.routeData.completedData.preCompletionData.preCompletionReady ∧
      M.routeData.completedData.completedHilbertReady ∧
        M.routeData.completedDenseRangeReady ∧ M.quotientToStandardDenseReady :=
  ⟨r4HilbertStandardCompletion_pre_completion_ready I TR M.routeData,
    r4HilbertCompleted_hilbert_ready I TR M.routeData.completedData,
    r4HilbertCompletedDense_completed_dense_ready I TR M.routeData,
    r4HilbertStandardCompletion_quotient_dense_ready I TR M⟩

theorem r4HilbertStandardCompletion_hilbert_quotient_dense_constructed
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
  ⟨r4HilbertStandardCompletion_inner_product_nonempty I TR M.routeData,
    r4HilbertStandardCompletion_complete_space I TR M.routeData,
    r4HilbertStandardCompletion_dense I TR M.routeData,
    r4HilbertStandardCompletion_quotient_dense_actual I TR M⟩

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
