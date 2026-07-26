import MGAP4D.MathlibAnalytic.ContinuousLinearMapArbitraryPositiveMultiplicityProfileConfluentBinomialNormalForm
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalFiniteResolventJetRealFormLimit

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

/-- Flattened finite positive jet data associated with an arbitrary nonempty
below-half-mass multiplicity profile. -/
noncomputable def VacuumSemigroupGapSlope.resolventPositiveMultiplicityProfileData
    {T : P.StronglyContinuousPhysicalSemigroup}
    (G : T.VacuumSemigroupGapSlope)
    (first : ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)
    (tail : List (ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)) :
    ContinuousLinearMap.FinitePositivePowerJetData
      G.BelowHalfMassShift :=
  ContinuousLinearMap.positiveMultiplicityProfileData
    (fun sigma : G.BelowHalfMassShift => sigma.1) first tail

/-- Finite-time arbitrary-length mixed resolvent profile product. -/
noncomputable def VacuumSemigroupGapSlope.admissibleRescaledDefectResolventPositiveMultiplicityProfileProduct
    {T : P.StronglyContinuousPhysicalSemigroup}
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    (first : ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)
    (tail : List (ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)) :
    P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert :=
  ContinuousLinearMap.positiveMultiplicityProfileProduct
    (fun sigma : G.BelowHalfMassShift =>
      G.admissibleRescaledDefectResolvent
        hInnerSymmetric tau sigma.property)
    first tail

/-- Continuum arbitrary-length mixed resolvent profile product. -/
noncomputable def VacuumSemigroupGapSlope.continuumResolventPositiveMultiplicityProfileProduct
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
  ContinuousLinearMap.positiveMultiplicityProfileProduct
    (fun sigma : G.BelowHalfMassShift =>
      G.vacuumOrthogonalContinuumRealResolvent
        T hP hInnerSymmetric hSelf sigma.property)
    first tail

/-- Finite-time flattened arbitrary-profile confluent/binomial normal form. -/
noncomputable def VacuumSemigroupGapSlope.admissibleRescaledDefectResolventPositiveMultiplicityProfileNormalForm
    {T : P.StronglyContinuousPhysicalSemigroup}
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    (first : ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)
    (tail : List (ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)) :
    P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert :=
  let d := G.resolventPositiveMultiplicityProfileData first tail
  G.admissibleRescaledDefectResolventFinsetJetCombination
    hInnerSymmetric tau d.support d.node (fun b => d.order b + 1)
      d.coefficient

/-- Continuum flattened arbitrary-profile confluent/binomial normal form. -/
noncomputable def VacuumSemigroupGapSlope.continuumResolventPositiveMultiplicityProfileNormalForm
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
  let d := G.resolventPositiveMultiplicityProfileData first tail
  G.continuumResolventFinsetJetCombination
    T hP hInnerSymmetric hSelf d.support d.node
      (fun b => d.order b + 1) d.coefficient

/-- At finite time, the flattened arbitrary-profile normal form is exactly the
successive mixed resolvent product. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventPositiveMultiplicityProfileNormalForm_eq_product
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    (first : ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)
    (tail : List (ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift))
    (hCompatible :
      ContinuousLinearMap.positiveMultiplicityProfileCompatible
        (fun sigma : G.BelowHalfMassShift => sigma.1) first tail) :
    G.admissibleRescaledDefectResolventPositiveMultiplicityProfileNormalForm
        hInnerSymmetric tau first tail =
      G.admissibleRescaledDefectResolventPositiveMultiplicityProfileProduct
        hInnerSymmetric tau first tail := by
  simpa [
    VacuumSemigroupGapSlope.admissibleRescaledDefectResolventPositiveMultiplicityProfileNormalForm,
    VacuumSemigroupGapSlope.admissibleRescaledDefectResolventPositiveMultiplicityProfileProduct,
    VacuumSemigroupGapSlope.resolventPositiveMultiplicityProfileData,
    VacuumSemigroupGapSlope.admissibleRescaledDefectResolventFinsetJetCombination,
    ContinuousLinearMap.FinitePositivePowerJetData.eval,
    ContinuousLinearMap.finitePositivePowerJetCombination] using
    (ContinuousLinearMap.positiveMultiplicityProfileData_eval_eq_product
      (fun sigma : G.BelowHalfMassShift =>
        G.admissibleRescaledDefectResolvent
          hInnerSymmetric tau sigma.property)
      (fun sigma : G.BelowHalfMassShift => sigma.1)
      first tail hCompatible
      (fun sigma rho =>
        G.admissibleRescaledDefectResolvent_identity
          T hInnerSymmetric tau sigma.property rho.property))

/-- In the continuum, the same flattened arbitrary-profile normal form is
exactly the mixed resolvent product. -/
theorem VacuumSemigroupGapSlope.continuumResolventPositiveMultiplicityProfileNormalForm_eq_product
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (first : ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)
    (tail : List (ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift))
    (hCompatible :
      ContinuousLinearMap.positiveMultiplicityProfileCompatible
        (fun sigma : G.BelowHalfMassShift => sigma.1) first tail) :
    G.continuumResolventPositiveMultiplicityProfileNormalForm
        T hP hInnerSymmetric hSelf first tail =
      G.continuumResolventPositiveMultiplicityProfileProduct
        T hP hInnerSymmetric hSelf first tail := by
  simpa [
    VacuumSemigroupGapSlope.continuumResolventPositiveMultiplicityProfileNormalForm,
    VacuumSemigroupGapSlope.continuumResolventPositiveMultiplicityProfileProduct,
    VacuumSemigroupGapSlope.resolventPositiveMultiplicityProfileData,
    VacuumSemigroupGapSlope.continuumResolventFinsetJetCombination,
    ContinuousLinearMap.FinitePositivePowerJetData.eval,
    ContinuousLinearMap.finitePositivePowerJetCombination] using
    (ContinuousLinearMap.positiveMultiplicityProfileData_eval_eq_product
      (fun sigma : G.BelowHalfMassShift =>
        G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf sigma.property)
      (fun sigma : G.BelowHalfMassShift => sigma.1)
      first tail hCompatible
      (fun sigma rho =>
        G.vacuumOrthogonalContinuumRealResolvent_identity
          T hP hInnerSymmetric hSelf sigma.property rho.property))

/-- Finite-time profile normal form as an explicit finite replicated-word sum. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventPositiveMultiplicityProfileNormalForm_eq_finsetWordSum
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    (first : ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)
    (tail : List (ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)) :
    let d := G.resolventPositiveMultiplicityProfileData first tail
    G.admissibleRescaledDefectResolventPositiveMultiplicityProfileNormalForm
        hInnerSymmetric tau first tail =
      G.admissibleRescaledDefectResolventFinsetWordSum
        hInnerSymmetric tau d.support
        (fun b => List.replicate (d.order b + 1) (d.node b))
        d.coefficient := by
  dsimp only
  exact
    G.admissibleRescaledDefectResolventFinsetJetCombination_eq_finsetWordSum_replicate
      T hInnerSymmetric tau
      (G.resolventPositiveMultiplicityProfileData first tail).support
      (G.resolventPositiveMultiplicityProfileData first tail).node
      (fun b =>
        (G.resolventPositiveMultiplicityProfileData first tail).order b + 1)
      (G.resolventPositiveMultiplicityProfileData first tail).coefficient

/-- Continuum profile normal form as the corresponding finite replicated-word
sum. -/
theorem VacuumSemigroupGapSlope.continuumResolventPositiveMultiplicityProfileNormalForm_eq_finsetWordSum
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (first : ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)
    (tail : List (ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)) :
    let d := G.resolventPositiveMultiplicityProfileData first tail
    G.continuumResolventPositiveMultiplicityProfileNormalForm
        T hP hInnerSymmetric hSelf first tail =
      G.continuumResolventFinsetWordSum
        T hP hInnerSymmetric hSelf d.support
        (fun b => List.replicate (d.order b + 1) (d.node b))
        d.coefficient := by
  dsimp only
  exact
    G.continuumResolventFinsetJetCombination_eq_finsetWordSum_replicate
      T hP hInnerSymmetric hSelf
      (G.resolventPositiveMultiplicityProfileData first tail).support
      (G.resolventPositiveMultiplicityProfileData first tail).node
      (fun b =>
        (G.resolventPositiveMultiplicityProfileData first tail).order b + 1)
      (G.resolventPositiveMultiplicityProfileData first tail).coefficient

/-- Arbitrary-profile normal forms converge pointwise strongly after diagonal
complexification on the full standard complexification. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventPositiveMultiplicityProfileNormalFormDiagonalComplexification_tendsto_continuum
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
          (G.admissibleRescaledDefectResolventPositiveMultiplicityProfileNormalForm
            hInnerSymmetric tau first tail) z)
      G.admissibleRescaledDefectTimeFilter
      (𝓝
        (diagonalComplexification
          (G.continuumResolventPositiveMultiplicityProfileNormalForm
            T hP hInnerSymmetric hSelf first tail) z)) := by
  let d := G.resolventPositiveMultiplicityProfileData first tail
  exact
    G.admissibleRescaledDefectResolventFinsetJetCombinationDiagonalComplexification_tendsto_continuum
      T hP hInnerSymmetric hSelf d.support d.node
      (fun b => d.order b + 1) d.coefficient z

/-- The continuum arbitrary-profile normal form lies in the closed diagonal
real-form star subalgebra. -/
theorem VacuumSemigroupGapSlope.continuumResolventPositiveMultiplicityProfileNormalFormDiagonalComplexification_mem_realForm
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
        (G.continuumResolventPositiveMultiplicityProfileNormalForm
          T hP hInnerSymmetric hSelf first tail) ∈
      diagonalComplexificationStarSubalgebra
        (H := P.VacuumOrthogonalHilbert) := by
  let d := G.resolventPositiveMultiplicityProfileData first tail
  exact
    G.continuumResolventFinsetJetCombinationDiagonalComplexification_mem_realForm
      T hP hInnerSymmetric hSelf d.support d.node
      (fun b => d.order b + 1) d.coefficient

/-- The real bounded operator underlying the arbitrary-profile complex strong
limit exists uniquely. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventPositiveMultiplicityProfileNormalFormDiagonalComplexification_existsUnique_real_limit
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
          (G.continuumResolventPositiveMultiplicityProfileNormalForm
            T hP hInnerSymmetric hSelf first tail) := by
  let d := G.resolventPositiveMultiplicityProfileData first tail
  exact
    G.admissibleRescaledDefectResolventFinsetJetCombinationDiagonalComplexification_existsUnique_real_limit
      T hP hInnerSymmetric hSelf d.support d.node
      (fun b => d.order b + 1) d.coefficient

/-- Any real bounded operator producing the same arbitrary-profile complex
pointwise strong limit is the continuum profile normal form. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventPositiveMultiplicityProfileNormalForm_real_limit_eq_continuum
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (first : ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)
    (tail : List (ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift))
    (R : P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert)
    (hR : ∀ z : StandardRealHilbertComplexification P.VacuumOrthogonalHilbert,
      Tendsto
        (fun tau : G.AdmissibleRescaledDefectTime =>
          diagonalComplexification
            (G.admissibleRescaledDefectResolventPositiveMultiplicityProfileNormalForm
              hInnerSymmetric tau first tail) z)
        G.admissibleRescaledDefectTimeFilter
        (𝓝 (diagonalComplexification R z))) :
    R = G.continuumResolventPositiveMultiplicityProfileNormalForm
      T hP hInnerSymmetric hSelf first tail := by
  let d := G.resolventPositiveMultiplicityProfileData first tail
  exact
    G.admissibleRescaledDefectResolventFinsetJetCombination_real_limit_eq_continuum
      T hP hInnerSymmetric hSelf d.support d.node
      (fun b => d.order b + 1) d.coefficient R hR

/-- Result proposition for the arbitrary-profile normal-form real-limit package. -/
def VacuumSemigroupGapSlope.PositiveMultiplicityProfileRealFormStatement
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
          (G.admissibleRescaledDefectResolventPositiveMultiplicityProfileNormalForm
            hInnerSymmetric tau first tail) z)
      G.admissibleRescaledDefectTimeFilter
      (𝓝
        (diagonalComplexification
          (G.continuumResolventPositiveMultiplicityProfileNormalForm
            T hP hInnerSymmetric hSelf first tail) z))) ∧
  diagonalComplexification
      (G.continuumResolventPositiveMultiplicityProfileNormalForm
        T hP hInnerSymmetric hSelf first tail) ∈
    diagonalComplexificationStarSubalgebra
      (H := P.VacuumOrthogonalHilbert) ∧
  ∃! R : P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert,
    diagonalComplexification R =
      diagonalComplexification
        (G.continuumResolventPositiveMultiplicityProfileNormalForm
          T hP hInnerSymmetric hSelf first tail)

/-- Actual OS real-form strong-limit package for arbitrary nonempty positive
multiplicity profiles. -/
theorem VacuumSemigroupGapSlope.canonicalPositiveMultiplicityProfileRealFormStrongLimitPackage
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (first : ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)
    (tail : List (ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)) :
    G.PositiveMultiplicityProfileRealFormStatement
      T hP hInnerSymmetric hSelf first tail := by
  constructor
  · intro z
    exact
      G.admissibleRescaledDefectResolventPositiveMultiplicityProfileNormalFormDiagonalComplexification_tendsto_continuum
        T hP hInnerSymmetric hSelf first tail z
  constructor
  · exact
      G.continuumResolventPositiveMultiplicityProfileNormalFormDiagonalComplexification_mem_realForm
        T hP hInnerSymmetric hSelf first tail
  · exact
      G.admissibleRescaledDefectResolventPositiveMultiplicityProfileNormalFormDiagonalComplexification_existsUnique_real_limit
        T hP hInnerSymmetric hSelf first tail

/-- Result proposition for compatible arbitrary-profile mixed products. -/
def VacuumSemigroupGapSlope.PositiveMultiplicityProfileProductRealFormStatement
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
          (G.admissibleRescaledDefectResolventPositiveMultiplicityProfileProduct
            hInnerSymmetric tau first tail) z)
      G.admissibleRescaledDefectTimeFilter
      (𝓝
        (diagonalComplexification
          (G.continuumResolventPositiveMultiplicityProfileProduct
            T hP hInnerSymmetric hSelf first tail) z))) ∧
  diagonalComplexification
      (G.continuumResolventPositiveMultiplicityProfileProduct
        T hP hInnerSymmetric hSelf first tail) ∈
    diagonalComplexificationStarSubalgebra
      (H := P.VacuumOrthogonalHilbert) ∧
  ∃! R : P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert,
    diagonalComplexification R =
      diagonalComplexification
        (G.continuumResolventPositiveMultiplicityProfileProduct
          T hP hInnerSymmetric hSelf first tail)

/-- Compatible arbitrary-length mixed products inherit the same full actual OS
real-form strong-limit package through exact normal-form identification. -/
theorem VacuumSemigroupGapSlope.canonicalPositiveMultiplicityProfileProductRealFormStrongLimitPackage
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (first : ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)
    (tail : List (ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift))
    (hCompatible :
      ContinuousLinearMap.positiveMultiplicityProfileCompatible
        (fun sigma : G.BelowHalfMassShift => sigma.1) first tail) :
    G.PositiveMultiplicityProfileProductRealFormStatement
      T hP hInnerSymmetric hSelf first tail := by
  rw [← G.admissibleRescaledDefectResolventPositiveMultiplicityProfileNormalForm_eq_product
    T hInnerSymmetric _ first tail hCompatible]
  rw [← G.continuumResolventPositiveMultiplicityProfileNormalForm_eq_product
    T hP hInnerSymmetric hSelf first tail hCompatible]
  exact
    G.canonicalPositiveMultiplicityProfileRealFormStrongLimitPackage
      T hP hInnerSymmetric hSelf first tail

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
