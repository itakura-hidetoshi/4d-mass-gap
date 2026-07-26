import MGAP4D.MathlibAnalytic.ContinuousLinearMapCanonicalPositivePowerJetCoefficientMap
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalPositiveMultiplicityProfilePermutationInvariantRealFormLimit

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

/-- Canonical node-order coefficient map of an arbitrary below-half-mass
positive multiplicity profile. -/
noncomputable def VacuumSemigroupGapSlope.resolventPositiveMultiplicityProfileCoefficientMap
    {T : P.StronglyContinuousPhysicalSemigroup}
    (G : T.VacuumSemigroupGapSlope)
    (first : ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)
    (tail : List (ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)) :
    ContinuousLinearMap.PositivePowerJetCoefficientMap
      G.BelowHalfMassShift :=
  ContinuousLinearMap.positiveMultiplicityProfileCoefficientMap
    (fun sigma : G.BelowHalfMassShift => sigma.1) first tail

/-- Finite-time canonical coefficient-map normal form. -/
noncomputable def VacuumSemigroupGapSlope.admissibleRescaledDefectResolventPositiveMultiplicityProfileCanonicalCoefficientNormalForm
    {T : P.StronglyContinuousPhysicalSemigroup}
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    (first : ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)
    (tail : List (ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)) :
    P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert :=
  ContinuousLinearMap.PositivePowerJetCoefficientMap.eval
    (G.resolventPositiveMultiplicityProfileCoefficientMap first tail)
    (fun sigma : G.BelowHalfMassShift =>
      G.admissibleRescaledDefectResolvent
        hInnerSymmetric tau sigma.property)

/-- Continuum canonical coefficient-map normal form. -/
noncomputable def VacuumSemigroupGapSlope.continuumResolventPositiveMultiplicityProfileCanonicalCoefficientNormalForm
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (first : ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)
    (tail : List (ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)) :
    P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert :=
  ContinuousLinearMap.PositivePowerJetCoefficientMap.eval
    (G.resolventPositiveMultiplicityProfileCoefficientMap first tail)
    (fun sigma : G.BelowHalfMassShift =>
      G.vacuumOrthogonalContinuumRealResolvent
        T hP hInnerSymmetric hSelf sigma.property)

/-- Canonical coefficient aggregation leaves the finite-time flattened normal
form unchanged as an operator. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventPositiveMultiplicityProfileCanonicalCoefficientNormalForm_eq_normalForm
    {T : P.StronglyContinuousPhysicalSemigroup}
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    (first : ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)
    (tail : List (ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)) :
    G.admissibleRescaledDefectResolventPositiveMultiplicityProfileCanonicalCoefficientNormalForm
        hInnerSymmetric tau first tail =
      G.admissibleRescaledDefectResolventPositiveMultiplicityProfileNormalForm
        hInnerSymmetric tau first tail := by
  simpa [
    VacuumSemigroupGapSlope.admissibleRescaledDefectResolventPositiveMultiplicityProfileCanonicalCoefficientNormalForm,
    VacuumSemigroupGapSlope.resolventPositiveMultiplicityProfileCoefficientMap,
    ContinuousLinearMap.positiveMultiplicityProfileCoefficientMap,
    VacuumSemigroupGapSlope.admissibleRescaledDefectResolventPositiveMultiplicityProfileNormalForm,
    VacuumSemigroupGapSlope.admissibleRescaledDefectResolventFinsetJetCombination,
    ContinuousLinearMap.FinitePositivePowerJetData.eval,
    ContinuousLinearMap.finitePositivePowerJetCombination] using
    (G.resolventPositiveMultiplicityProfileData first tail).coefficientMap_eval_eq
      (fun sigma : G.BelowHalfMassShift =>
        G.admissibleRescaledDefectResolvent
          hInnerSymmetric tau sigma.property)

/-- Canonical coefficient aggregation leaves the continuum flattened normal
form unchanged as an operator. -/
theorem VacuumSemigroupGapSlope.continuumResolventPositiveMultiplicityProfileCanonicalCoefficientNormalForm_eq_normalForm
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (first : ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)
    (tail : List (ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)) :
    G.continuumResolventPositiveMultiplicityProfileCanonicalCoefficientNormalForm
        T hP hInnerSymmetric hSelf first tail =
      G.continuumResolventPositiveMultiplicityProfileNormalForm
        T hP hInnerSymmetric hSelf first tail := by
  simpa [
    VacuumSemigroupGapSlope.continuumResolventPositiveMultiplicityProfileCanonicalCoefficientNormalForm,
    VacuumSemigroupGapSlope.resolventPositiveMultiplicityProfileCoefficientMap,
    ContinuousLinearMap.positiveMultiplicityProfileCoefficientMap,
    VacuumSemigroupGapSlope.continuumResolventPositiveMultiplicityProfileNormalForm,
    VacuumSemigroupGapSlope.continuumResolventFinsetJetCombination,
    ContinuousLinearMap.FinitePositivePowerJetData.eval,
    ContinuousLinearMap.finitePositivePowerJetCombination] using
    (G.resolventPositiveMultiplicityProfileData first tail).coefficientMap_eval_eq
      (fun sigma : G.BelowHalfMassShift =>
        G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf sigma.property)

/-- At finite time, pairwise scalar distinctness identifies the canonical
coefficient-map normal form with the mixed resolvent product. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventPositiveMultiplicityProfileCanonicalCoefficientNormalForm_eq_product_of_pairwise
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
    G.admissibleRescaledDefectResolventPositiveMultiplicityProfileCanonicalCoefficientNormalForm
        hInnerSymmetric tau first tail =
      G.admissibleRescaledDefectResolventPositiveMultiplicityProfileProduct
        hInnerSymmetric tau first tail := by
  rw [G.admissibleRescaledDefectResolventPositiveMultiplicityProfileCanonicalCoefficientNormalForm_eq_normalForm
    hInnerSymmetric tau first tail]
  exact
    G.admissibleRescaledDefectResolventPositiveMultiplicityProfileNormalForm_eq_product_of_pairwise
      T hInnerSymmetric tau first tail hPairwise

/-- In the continuum, pairwise scalar distinctness identifies the canonical
coefficient-map normal form with the mixed resolvent product. -/
theorem VacuumSemigroupGapSlope.continuumResolventPositiveMultiplicityProfileCanonicalCoefficientNormalForm_eq_product_of_pairwise
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
    G.continuumResolventPositiveMultiplicityProfileCanonicalCoefficientNormalForm
        T hP hInnerSymmetric hSelf first tail =
      G.continuumResolventPositiveMultiplicityProfileProduct
        T hP hInnerSymmetric hSelf first tail := by
  rw [G.continuumResolventPositiveMultiplicityProfileCanonicalCoefficientNormalForm_eq_normalForm
    T hP hInnerSymmetric hSelf first tail]
  exact
    G.continuumResolventPositiveMultiplicityProfileNormalForm_eq_product_of_pairwise
      T hP hInnerSymmetric hSelf first tail hPairwise

/-- Canonical coefficient-map normal forms converge pointwise strongly after
diagonal complexification. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventPositiveMultiplicityProfileCanonicalCoefficientNormalFormDiagonalComplexification_tendsto_continuum
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (first : ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)
    (tail : List (ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift))
    (z : StandardRealHilbertComplexification P.VacuumOrthogonalHilbert) :
    Tendsto
      (fun tau : G.AdmissibleRescaledDefectTime =>
        diagonalComplexification
          (G.admissibleRescaledDefectResolventPositiveMultiplicityProfileCanonicalCoefficientNormalForm
            hInnerSymmetric tau first tail) z)
      G.admissibleRescaledDefectTimeFilter
      (𝓝
        (diagonalComplexification
          (G.continuumResolventPositiveMultiplicityProfileCanonicalCoefficientNormalForm
            T hP hInnerSymmetric hSelf first tail) z)) := by
  simpa only [
    G.admissibleRescaledDefectResolventPositiveMultiplicityProfileCanonicalCoefficientNormalForm_eq_normalForm,
    G.continuumResolventPositiveMultiplicityProfileCanonicalCoefficientNormalForm_eq_normalForm] using
    G.admissibleRescaledDefectResolventPositiveMultiplicityProfileNormalFormDiagonalComplexification_tendsto_continuum
      T hP hInnerSymmetric hSelf first tail z

/-- The continuum canonical coefficient-map normal form lies in the closed
diagonal real-form star subalgebra. -/
theorem VacuumSemigroupGapSlope.continuumResolventPositiveMultiplicityProfileCanonicalCoefficientNormalFormDiagonalComplexification_mem_realForm
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (first : ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)
    (tail : List (ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)) :
    diagonalComplexification
        (G.continuumResolventPositiveMultiplicityProfileCanonicalCoefficientNormalForm
          T hP hInnerSymmetric hSelf first tail) ∈
      diagonalComplexificationStarSubalgebra
        (H := P.VacuumOrthogonalHilbert) := by
  rw [G.continuumResolventPositiveMultiplicityProfileCanonicalCoefficientNormalForm_eq_normalForm
    T hP hInnerSymmetric hSelf first tail]
  exact
    G.continuumResolventPositiveMultiplicityProfileNormalFormDiagonalComplexification_mem_realForm
      T hP hInnerSymmetric hSelf first tail

/-- The canonical coefficient-map package is the existing arbitrary-profile
real-form package transported through the exact canonical aggregation equalities. -/
def VacuumSemigroupGapSlope.PositiveMultiplicityProfileCanonicalCoefficientRealFormStatement
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (first : ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)
    (tail : List (ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)) : Prop :=
  G.PositiveMultiplicityProfileRealFormStatement
    T hP hInnerSymmetric hSelf first tail

/-- Full actual OS real-form strong-limit package for the canonical aggregated
node-order coefficient-map representation. -/
theorem VacuumSemigroupGapSlope.canonicalPositiveMultiplicityProfileCoefficientMapRealFormStrongLimitPackage
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (first : ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)
    (tail : List (ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)) :
    G.PositiveMultiplicityProfileCanonicalCoefficientRealFormStatement
      T hP hInnerSymmetric hSelf first tail := by
  exact
    G.canonicalPositiveMultiplicityProfileRealFormStrongLimitPackage
      T hP hInnerSymmetric hSelf first tail

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
