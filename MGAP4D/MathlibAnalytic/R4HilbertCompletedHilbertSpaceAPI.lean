import MGAP4D.MathlibAnalytic.R4HilbertStandardRealCompletionConstructionTheorem
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

/-- The completed real Hilbert space obtained by completing the R4
pre-Hilbert carrier. -/
abbrev r4HilbertCompletedHilbertSpace
    (M : R4HilbertStandardCompletionQuotientDenseData I TR) : Type :=
  r4HilbertStandardCompletionCarrier I TR M.routeData

/-- The dense embedding of the pre-Hilbert carrier into the completed Hilbert space. -/
def r4HilbertCompletedHilbertSpacePreMap
    (M : R4HilbertStandardCompletionQuotientDenseData I TR) :
    r4HilbertCompletedActualPreCarrier I TR M.routeData →
      r4HilbertCompletedHilbertSpace I TR M :=
  r4HilbertStandardCompletionMap I TR M.routeData

/-- The quotient map into the completed Hilbert space. -/
def r4HilbertCompletedHilbertSpaceQuotientMap
    (M : R4HilbertStandardCompletionQuotientDenseData I TR) :
    quotientCarrier I → r4HilbertCompletedHilbertSpace I TR M :=
  r4HilbertStandardCompletionQuotientMap I TR M.routeData

@[implicit_reducible] def r4HilbertCompletedHilbertSpaceNormedAddCommGroup
    (M : R4HilbertStandardCompletionQuotientDenseData I TR) :
    NormedAddCommGroup (r4HilbertCompletedHilbertSpace I TR M) :=
  r4HilbertStandardCompletionNormedAddCommGroup I TR M.routeData

@[implicit_reducible] def r4HilbertCompletedHilbertSpaceInnerProductSpaceReal
    (M : R4HilbertStandardCompletionQuotientDenseData I TR) :
    (letI : NormedAddCommGroup (r4HilbertCompletedHilbertSpace I TR M) :=
      r4HilbertCompletedHilbertSpaceNormedAddCommGroup I TR M
    InnerProductSpace ℝ (r4HilbertCompletedHilbertSpace I TR M)) :=
  r4HilbertStandardCompletionInnerProductSpaceReal I TR M.routeData

@[implicit_reducible] def r4HilbertCompletedHilbertSpaceCompleteSpace
    (M : R4HilbertStandardCompletionQuotientDenseData I TR) :
    (letI : NormedAddCommGroup (r4HilbertCompletedHilbertSpace I TR M) :=
      r4HilbertCompletedHilbertSpaceNormedAddCommGroup I TR M
    CompleteSpace (r4HilbertCompletedHilbertSpace I TR M)) :=
  r4HilbertStandardCompletionCompleteSpace I TR M.routeData

theorem r4HilbertCompletedHilbertSpace_inner_product_nonempty
    (M : R4HilbertStandardCompletionQuotientDenseData I TR) :
    Nonempty
      (letI : NormedAddCommGroup (r4HilbertCompletedHilbertSpace I TR M) :=
        r4HilbertCompletedHilbertSpaceNormedAddCommGroup I TR M
      InnerProductSpace ℝ (r4HilbertCompletedHilbertSpace I TR M)) :=
  ⟨r4HilbertCompletedHilbertSpaceInnerProductSpaceReal I TR M⟩

theorem r4HilbertCompletedHilbertSpace_complete
    (M : R4HilbertStandardCompletionQuotientDenseData I TR) :
    (letI : NormedAddCommGroup (r4HilbertCompletedHilbertSpace I TR M) :=
      r4HilbertCompletedHilbertSpaceNormedAddCommGroup I TR M
    CompleteSpace (r4HilbertCompletedHilbertSpace I TR M)) :=
  r4HilbertCompletedHilbertSpaceCompleteSpace I TR M

theorem r4HilbertCompletedHilbertSpace_pre_dense
    (M : R4HilbertStandardCompletionQuotientDenseData I TR) :
    (letI : NormedAddCommGroup (r4HilbertCompletedHilbertSpace I TR M) :=
      r4HilbertCompletedHilbertSpaceNormedAddCommGroup I TR M
    DenseRange (r4HilbertCompletedHilbertSpacePreMap I TR M)) :=
  r4HilbertStandardCompletionQuotientDenseTheorem_pre_dense I TR M

theorem r4HilbertCompletedHilbertSpace_quotient_dense
    (M : R4HilbertStandardCompletionQuotientDenseData I TR) :
    (letI : NormedAddCommGroup (r4HilbertCompletedHilbertSpace I TR M) :=
      r4HilbertCompletedHilbertSpaceNormedAddCommGroup I TR M
    DenseRange (r4HilbertCompletedHilbertSpaceQuotientMap I TR M)) :=
  r4HilbertStandardCompletionQuotientDenseTheorem_quotient_map_dense I TR M

theorem r4HilbertCompletedHilbertSpace_eq_uniform_completion
    (M : R4HilbertStandardCompletionQuotientDenseData I TR) :
    r4HilbertCompletedHilbertSpace I TR M =
      (letI : NormedAddCommGroup
          (r4HilbertCompletedActualPreCarrier I TR M.routeData) :=
        M.routeData.completedData.preCompletionData.instNormedAddCommGroup
      UniformSpace.Completion (r4HilbertCompletedActualPreCarrier I TR M.routeData)) :=
  r4HilbertStandardCompletion_carrier_eq_uniform_completion I TR M.routeData

theorem r4HilbertCompletedHilbertSpace_quotient_factors
    (M : R4HilbertStandardCompletionQuotientDenseData I TR)
    (q : quotientCarrier I) :
    r4HilbertCompletedHilbertSpaceQuotientMap I TR M q =
      r4HilbertCompletedHilbertSpacePreMap I TR M
        (M.routeData.completedData.preCompletionData.quotientToPreHilbert q) :=
  r4HilbertStandardCompletionQuotientDenseTheorem_quotient_factors I TR M q

/-- The completed R4 Hilbert space object: a real inner-product space that is
complete, is the mathlib completion of the pre-Hilbert carrier, and receives
dense maps from both the pre-Hilbert carrier and the quotient carrier. -/
theorem r4HilbertCompletedHilbertSpace_constructed
    (M : R4HilbertStandardCompletionQuotientDenseData I TR) :
    Nonempty
      (letI : NormedAddCommGroup (r4HilbertCompletedHilbertSpace I TR M) :=
        r4HilbertCompletedHilbertSpaceNormedAddCommGroup I TR M
      InnerProductSpace ℝ (r4HilbertCompletedHilbertSpace I TR M)) ∧
      (letI : NormedAddCommGroup (r4HilbertCompletedHilbertSpace I TR M) :=
        r4HilbertCompletedHilbertSpaceNormedAddCommGroup I TR M
      CompleteSpace (r4HilbertCompletedHilbertSpace I TR M)) ∧
        (letI : NormedAddCommGroup (r4HilbertCompletedHilbertSpace I TR M) :=
          r4HilbertCompletedHilbertSpaceNormedAddCommGroup I TR M
        DenseRange (r4HilbertCompletedHilbertSpacePreMap I TR M)) ∧
          (letI : NormedAddCommGroup (r4HilbertCompletedHilbertSpace I TR M) :=
            r4HilbertCompletedHilbertSpaceNormedAddCommGroup I TR M
          DenseRange (r4HilbertCompletedHilbertSpaceQuotientMap I TR M)) ∧
            r4HilbertCompletedHilbertSpace I TR M =
              (letI : NormedAddCommGroup
                  (r4HilbertCompletedActualPreCarrier I TR M.routeData) :=
                M.routeData.completedData.preCompletionData.instNormedAddCommGroup
              UniformSpace.Completion
                (r4HilbertCompletedActualPreCarrier I TR M.routeData)) :=
  ⟨r4HilbertCompletedHilbertSpace_inner_product_nonempty I TR M,
    r4HilbertCompletedHilbertSpace_complete I TR M,
    r4HilbertCompletedHilbertSpace_pre_dense I TR M,
    r4HilbertCompletedHilbertSpace_quotient_dense I TR M,
    r4HilbertCompletedHilbertSpace_eq_uniform_completion I TR M⟩

end EuclideanYangMillsR4HilbertReconstructionQuotient

end

end MathlibAnalytic
end MGAP4D
