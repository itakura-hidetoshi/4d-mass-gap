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
  (G.resolventPositiveMultiplicityProfileCoefficientMap first tail).eval
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
  (G.resolventPositiveMultiplicityProfileCoefficientMap first tail).eval
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
  calc
    G.admissibleRescaledDefectResolventPositiveMultiplicityProfileCanonicalCoefficientNormalForm
        hInnerSymmetric tau first tail =
      G.admissibleRescaledDefectResolventPositiveMultiplicityProfileNormalForm
        hInnerSymmetric tau first tail :=
      G.admissibleRescaledDefectResolventPositiveMultiplicityProfileCanonicalCoefficientNormalForm_eq_normalForm
        hInnerSymmetric tau first tail
    _ = G.admissibleRescaledDefectResolventPositiveMultiplicityProfileProduct
        hInnerSymmetric tau first tail :=
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
  calc
    G.continuumResolventPositiveMultiplicityProfileCanonicalCoefficientNormalForm
        T hP hInnerSymmetric hSelf first tail =
      G.continuumResolventPositiveMultiplicityProfileNormalForm
        T hP hInnerSymmetric hSelf first tail :=
      G.continuumResolventPositiveMultiplicityProfileCanonicalCoefficientNormalForm_eq_normalForm
        T hP hInnerSymmetric hSelf first tail
    _ = G.continuumResolventPositiveMultiplicityProfileProduct
        T hP hInnerSymmetric hSelf first tail :=
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

/-- The real bounded operator underlying the canonical coefficient-map complex
strong limit exists uniquely. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventPositiveMultiplicityProfileCanonicalCoefficientNormalFormDiagonalComplexification_existsUnique_real_limit
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (first : ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)
    (tail : List (ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)) :
    ∃! R : P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert,
      diagonalComplexification R =
        diagonalComplexification
          (G.continuumResolventPositiveMultiplicityProfileCanonicalCoefficientNormalForm
            T hP hInnerSymmetric hSelf first tail) := by
  rw [G.continuumResolventPositiveMultiplicityProfileCanonicalCoefficientNormalForm_eq_normalForm
    T hP hInnerSymmetric hSelf first tail]
  exact
    G.admissibleRescaledDefectResolventPositiveMultiplicityProfileNormalFormDiagonalComplexification_existsUnique_real_limit
      T hP hInnerSymmetric hSelf first tail

/-- Result proposition for the canonical coefficient-map real-form package. -/
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
  (∀ z : StandardRealHilbertComplexification P.VacuumOrthogonalHilbert,
    Tendsto
      (fun tau : G.AdmissibleRescaledDefectTime =>
        diagonalComplexification
          (G.admissibleRescaledDefectResolventPositiveMultiplicityProfileCanonicalCoefficientNormalForm
            hInnerSymmetric tau first tail) z)
      G.admissibleRescaledDefectTimeFilter
      (𝓝
        (diagonalComplexification
          (G.continuumResolventPositiveMultiplicityProfileCanonicalCoefficientNormalForm
            T hP hInnerSymmetric hSelf first tail) z))) ∧
  diagonalComplexification
      (G.continuumResolventPositiveMultiplicityProfileCanonicalCoefficientNormalForm
        T hP hInnerSymmetric hSelf first tail) ∈
    diagonalComplexificationStarSubalgebra
      (H := P.VacuumOrthogonalHilbert) ∧
  ∃! R : P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert,
    diagonalComplexification R =
      diagonalComplexification
        (G.continuumResolventPositiveMultiplicityProfileCanonicalCoefficientNormalForm
          T hP hInnerSymmetric hSelf first tail)

/-- Full actual OS real-form strong-limit package for the canonical aggregated
node-order coefficient-map normal form. -/
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
  constructor
  · intro z
    exact
      G.admissibleRescaledDefectResolventPositiveMultiplicityProfileCanonicalCoefficientNormalFormDiagonalComplexification_tendsto_continuum
        T hP hInnerSymmetric hSelf first tail z
  constructor
  · exact
      G.continuumResolventPositiveMultiplicityProfileCanonicalCoefficientNormalFormDiagonalComplexification_mem_realForm
        T hP hInnerSymmetric hSelf first tail
  · exact
      G.admissibleRescaledDefectResolventPositiveMultiplicityProfileCanonicalCoefficientNormalFormDiagonalComplexification_existsUnique_real_limit
        T hP hInnerSymmetric hSelf first tail

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
