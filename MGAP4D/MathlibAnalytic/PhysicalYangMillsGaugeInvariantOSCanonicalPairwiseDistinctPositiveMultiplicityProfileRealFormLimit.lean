import MGAP4D.MathlibAnalytic.ContinuousLinearMapPairwiseDistinctPositiveMultiplicityProfileConfluentBinomialNormalForm
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalArbitraryPositiveMultiplicityProfileRealFormLimit

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace LinearPMap
open StandardRealHilbertComplexification

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- Natural pairwise scalar distinctness for a below-half-mass positive
multiplicity profile. -/
def VacuumSemigroupGapSlope.BelowHalfMassPositiveMultiplicityProfilePairwiseDistinct
    {T : P.StronglyContinuousPhysicalSemigroup}
    (G : T.VacuumSemigroupGapSlope)
    (first : ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)
    (tail : List (ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)) : Prop :=
  ContinuousLinearMap.positiveMultiplicityProfilePairwiseDistinct
    (fun sigma : G.BelowHalfMassShift => sigma.1) first tail

/-- Pairwise scalar distinctness of the original below-half-mass shifts implies
the recursive compatibility required by every flattened adjoin step. -/
theorem VacuumSemigroupGapSlope.resolventPositiveMultiplicityProfileCompatible_of_pairwise
    {T : P.StronglyContinuousPhysicalSemigroup}
    (G : T.VacuumSemigroupGapSlope)
    (first : ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)
    (tail : List (ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift))
    (hPairwise :
      G.BelowHalfMassPositiveMultiplicityProfilePairwiseDistinct first tail) :
    ContinuousLinearMap.positiveMultiplicityProfileCompatible
      (fun sigma : G.BelowHalfMassShift => sigma.1) first tail := by
  exact ContinuousLinearMap.positiveMultiplicityProfileCompatible_of_pairwise
    (fun sigma : G.BelowHalfMassShift => sigma.1) first tail hPairwise

/-- At finite time, pairwise scalar distinctness alone identifies the flattened
normal form with the successive mixed resolvent product. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventPositiveMultiplicityProfileNormalForm_eq_product_of_pairwise
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    (first : ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)
    (tail : List (ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift))
    (hPairwise :
      G.BelowHalfMassPositiveMultiplicityProfilePairwiseDistinct first tail) :
    G.admissibleRescaledDefectResolventPositiveMultiplicityProfileNormalForm
        hInnerSymmetric tau first tail =
      G.admissibleRescaledDefectResolventPositiveMultiplicityProfileProduct
        hInnerSymmetric tau first tail := by
  exact
    G.admissibleRescaledDefectResolventPositiveMultiplicityProfileNormalForm_eq_product
      T hInnerSymmetric tau first tail
      (G.resolventPositiveMultiplicityProfileCompatible_of_pairwise
        first tail hPairwise)

/-- In the continuum, pairwise scalar distinctness alone identifies the
flattened normal form with the mixed resolvent product. -/
theorem VacuumSemigroupGapSlope.continuumResolventPositiveMultiplicityProfileNormalForm_eq_product_of_pairwise
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (first : ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)
    (tail : List (ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift))
    (hPairwise :
      G.BelowHalfMassPositiveMultiplicityProfilePairwiseDistinct first tail) :
    G.continuumResolventPositiveMultiplicityProfileNormalForm
        T hP hInnerSymmetric hSelf first tail =
      G.continuumResolventPositiveMultiplicityProfileProduct
        T hP hInnerSymmetric hSelf first tail := by
  exact
    G.continuumResolventPositiveMultiplicityProfileNormalForm_eq_product
      T hP hInnerSymmetric hSelf first tail
      (G.resolventPositiveMultiplicityProfileCompatible_of_pairwise
        first tail hPairwise)

/-- Pairwise-distinct arbitrary-length mixed products inherit the full actual
OS real-form strong-limit package without a recursive compatibility hypothesis. -/
theorem VacuumSemigroupGapSlope.canonicalPairwiseDistinctPositiveMultiplicityProfileProductRealFormStrongLimitPackage
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (first : ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)
    (tail : List (ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift))
    (hPairwise :
      G.BelowHalfMassPositiveMultiplicityProfilePairwiseDistinct first tail) :
    G.PositiveMultiplicityProfileProductRealFormStatement
      T hP hInnerSymmetric hSelf first tail := by
  exact
    G.canonicalPositiveMultiplicityProfileProductRealFormStrongLimitPackage
      T hP hInnerSymmetric hSelf first tail
      (G.resolventPositiveMultiplicityProfileCompatible_of_pairwise
        first tail hPairwise)

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
