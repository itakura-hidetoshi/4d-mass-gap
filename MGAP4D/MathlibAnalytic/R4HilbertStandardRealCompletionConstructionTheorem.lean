import MGAP4D.MathlibAnalytic.R4HilbertStandardCompletionQuotientDenseTheoremAPI
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

/-- The standard real Hilbert completion carrier constructed from the R4
pre-Hilbert carrier. -/
def r4HilbertStandardRealCompletionConstructionCarrier
    (M : R4HilbertStandardCompletionQuotientDenseData I TR) : Type :=
  r4HilbertStandardCompletionCarrier I TR M.routeData

/-- The standard dense embedding of the R4 pre-Hilbert carrier into the
constructed real Hilbert completion. -/
def r4HilbertStandardRealCompletionConstructionPreMap
    (M : R4HilbertStandardCompletionQuotientDenseData I TR) :
    r4HilbertCompletedActualPreCarrier I TR M.routeData →
      r4HilbertStandardRealCompletionConstructionCarrier I TR M :=
  r4HilbertStandardCompletionMap I TR M.routeData

/-- The quotient-to-completion map for the constructed standard real Hilbert
completion. -/
def r4HilbertStandardRealCompletionConstructionQuotientMap
    (M : R4HilbertStandardCompletionQuotientDenseData I TR) :
    quotientCarrier I → r4HilbertStandardRealCompletionConstructionCarrier I TR M :=
  r4HilbertStandardCompletionQuotientMap I TR M.routeData

/-- The standard real Hilbert completion construction theorem for the R4
reflection-positive quotient route.

It states that the constructed carrier is the mathlib uniform completion of the
pre-Hilbert carrier, carries real inner-product and complete-space structure,
and receives dense maps both from the pre-Hilbert carrier and from the quotient
carrier. -/
theorem r4HilbertStandardRealCompletionConstruction_theorem
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
          DenseRange (r4HilbertStandardCompletionQuotientMap I TR M.routeData)) ∧
            r4HilbertStandardCompletionCarrier I TR M.routeData =
              (letI : NormedAddCommGroup
                  (r4HilbertCompletedActualPreCarrier I TR M.routeData) :=
                M.routeData.completedData.preCompletionData.instNormedAddCommGroup
              UniformSpace.Completion
                (r4HilbertCompletedActualPreCarrier I TR M.routeData)) ∧
              (∀ q : quotientCarrier I,
                r4HilbertStandardCompletionQuotientMap I TR M.routeData q =
                  r4HilbertStandardCompletionMap I TR M.routeData
                    (M.routeData.completedData.preCompletionData.quotientToPreHilbert q)) ∧
                (M.routeData.completedData.preCompletionData.preCompletionReady ∧
                  M.routeData.completedData.completedHilbertReady ∧
                    M.routeData.completedDenseRangeReady ∧ M.quotientToStandardDenseReady) :=
  ⟨r4HilbertStandardCompletionQuotientDenseTheorem_inner_product_nonempty I TR M,
    r4HilbertStandardCompletionQuotientDenseTheorem_complete_space I TR M,
    r4HilbertStandardCompletionQuotientDenseTheorem_pre_dense I TR M,
    r4HilbertStandardCompletionQuotientDenseTheorem_quotient_map_dense I TR M,
    r4HilbertStandardCompletion_carrier_eq_uniform_completion I TR M.routeData,
    r4HilbertStandardCompletionQuotientDenseTheorem_quotient_factors I TR M,
    r4HilbertStandardCompletionQuotientDenseTheorem_route_ready I TR M⟩

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
