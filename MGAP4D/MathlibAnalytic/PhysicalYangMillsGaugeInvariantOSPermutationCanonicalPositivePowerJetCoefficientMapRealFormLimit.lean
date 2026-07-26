import MGAP4D.MathlibAnalytic.ContinuousLinearMapPermutationCanonicalPositivePowerJetCoefficientMap
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalPositivePowerJetCoefficientMapRealFormLimit

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

/-- The uniquely sorted node-order coefficient Finsupp associated with an
arbitrary nonempty below-half-mass multiplicity profile. -/
noncomputable def VacuumSemigroupGapSlope.resolventPositiveMultiplicityProfilePermutationCanonicalCoefficientMap
    {T : P.StronglyContinuousPhysicalSemigroup}
    (G : T.VacuumSemigroupGapSlope)
    (first : ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)
    (tail : List (ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)) :
    ContinuousLinearMap.PositivePowerJetCoefficientMap
      G.BelowHalfMassShift :=
  ContinuousLinearMap.positiveMultiplicityProfilePermutationCanonicalCoefficientMap
    (fun sigma : G.BelowHalfMassShift => sigma.1) first tail

/-- The actual OS canonical coefficient Finsupp itself is invariant under every
permutation of the source profile. -/
theorem VacuumSemigroupGapSlope.resolventPositiveMultiplicityProfilePermutationCanonicalCoefficientMap_eq_of_perm
    {T : P.StronglyContinuousPhysicalSemigroup}
    (G : T.VacuumSemigroupGapSlope)
    (first₁ first₂ : ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)
    (tail₁ tail₂ : List (ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift))
    (hPerm : (first₁ :: tail₁).Perm (first₂ :: tail₂)) :
    G.resolventPositiveMultiplicityProfilePermutationCanonicalCoefficientMap
        first₁ tail₁ =
      G.resolventPositiveMultiplicityProfilePermutationCanonicalCoefficientMap
        first₂ tail₂ := by
  exact
    ContinuousLinearMap.positiveMultiplicityProfilePermutationCanonicalCoefficientMap_eq_of_perm
      (fun sigma : G.BelowHalfMassShift => sigma.1)
      first₁ first₂ tail₁ tail₂ Subtype.val_injective hPerm

/-- Finite-time evaluation of the permutation-canonical coefficient Finsupp. -/
noncomputable def VacuumSemigroupGapSlope.admissibleRescaledDefectResolventPositiveMultiplicityProfilePermutationCanonicalCoefficientNormalForm
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
    (G.resolventPositiveMultiplicityProfilePermutationCanonicalCoefficientMap
      first tail)
    (fun sigma : G.BelowHalfMassShift =>
      G.admissibleRescaledDefectResolvent
        hInnerSymmetric tau sigma.property)

/-- Continuum evaluation of the permutation-canonical coefficient Finsupp. -/
noncomputable def VacuumSemigroupGapSlope.continuumResolventPositiveMultiplicityProfilePermutationCanonicalCoefficientNormalForm
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
    (G.resolventPositiveMultiplicityProfilePermutationCanonicalCoefficientMap
      first tail)
    (fun sigma : G.BelowHalfMassShift =>
      G.vacuumOrthogonalContinuumRealResolvent
        T hP hInnerSymmetric hSelf sigma.property)

/-- Finite-time permutation-canonical coefficient normal forms are exactly
order-independent, without requiring pairwise distinctness for this equality. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventPositiveMultiplicityProfilePermutationCanonicalCoefficientNormalForm_eq_of_perm
    {T : P.StronglyContinuousPhysicalSemigroup}
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    (first₁ first₂ : ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)
    (tail₁ tail₂ : List (ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift))
    (hPerm : (first₁ :: tail₁).Perm (first₂ :: tail₂)) :
    G.admissibleRescaledDefectResolventPositiveMultiplicityProfilePermutationCanonicalCoefficientNormalForm
        hInnerSymmetric tau first₁ tail₁ =
      G.admissibleRescaledDefectResolventPositiveMultiplicityProfilePermutationCanonicalCoefficientNormalForm
        hInnerSymmetric tau first₂ tail₂ := by
  rw [VacuumSemigroupGapSlope.admissibleRescaledDefectResolventPositiveMultiplicityProfilePermutationCanonicalCoefficientNormalForm,
    VacuumSemigroupGapSlope.admissibleRescaledDefectResolventPositiveMultiplicityProfilePermutationCanonicalCoefficientNormalForm,
    G.resolventPositiveMultiplicityProfilePermutationCanonicalCoefficientMap_eq_of_perm
      first₁ first₂ tail₁ tail₂ hPerm]

/-- Continuum permutation-canonical coefficient normal forms are exactly
order-independent, without requiring pairwise distinctness for this equality. -/
theorem VacuumSemigroupGapSlope.continuumResolventPositiveMultiplicityProfilePermutationCanonicalCoefficientNormalForm_eq_of_perm
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (first₁ first₂ : ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)
    (tail₁ tail₂ : List (ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift))
    (hPerm : (first₁ :: tail₁).Perm (first₂ :: tail₂)) :
    G.continuumResolventPositiveMultiplicityProfilePermutationCanonicalCoefficientNormalForm
        T hP hInnerSymmetric hSelf first₁ tail₁ =
      G.continuumResolventPositiveMultiplicityProfilePermutationCanonicalCoefficientNormalForm
        T hP hInnerSymmetric hSelf first₂ tail₂ := by
  rw [VacuumSemigroupGapSlope.continuumResolventPositiveMultiplicityProfilePermutationCanonicalCoefficientNormalForm,
    VacuumSemigroupGapSlope.continuumResolventPositiveMultiplicityProfilePermutationCanonicalCoefficientNormalForm,
    G.resolventPositiveMultiplicityProfilePermutationCanonicalCoefficientMap_eq_of_perm
      first₁ first₂ tail₁ tail₂ hPerm]

/-- At finite time, pairwise scalar distinctness identifies the
permutation-canonical coefficient normal form with the original mixed product. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventPositiveMultiplicityProfilePermutationCanonicalCoefficientNormalForm_eq_product_of_pairwise
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
    G.admissibleRescaledDefectResolventPositiveMultiplicityProfilePermutationCanonicalCoefficientNormalForm
        hInnerSymmetric tau first tail =
      G.admissibleRescaledDefectResolventPositiveMultiplicityProfileProduct
        hInnerSymmetric tau first tail := by
  exact
    ContinuousLinearMap.positiveMultiplicityProfilePermutationCanonicalCoefficientMap_eval_eq_product_of_pairwise
      (fun sigma : G.BelowHalfMassShift =>
        G.admissibleRescaledDefectResolvent
          hInnerSymmetric tau sigma.property)
      (fun sigma : G.BelowHalfMassShift => sigma.1)
      first tail hPairwise
      (fun sigma rho =>
        G.admissibleRescaledDefectResolvent_identity
          T hInnerSymmetric tau sigma.property rho.property)

/-- In the continuum, pairwise scalar distinctness identifies the
permutation-canonical coefficient normal form with the original mixed product. -/
theorem VacuumSemigroupGapSlope.continuumResolventPositiveMultiplicityProfilePermutationCanonicalCoefficientNormalForm_eq_product_of_pairwise
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
    G.continuumResolventPositiveMultiplicityProfilePermutationCanonicalCoefficientNormalForm
        T hP hInnerSymmetric hSelf first tail =
      G.continuumResolventPositiveMultiplicityProfileProduct
        T hP hInnerSymmetric hSelf first tail := by
  exact
    ContinuousLinearMap.positiveMultiplicityProfilePermutationCanonicalCoefficientMap_eval_eq_product_of_pairwise
      (fun sigma : G.BelowHalfMassShift =>
        G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf sigma.property)
      (fun sigma : G.BelowHalfMassShift => sigma.1)
      first tail hPairwise
      (fun sigma rho =>
        G.vacuumOrthogonalContinuumRealResolvent_identity
          T hP hInnerSymmetric hSelf sigma.property rho.property)

/-- Full actual OS real-form statement written directly for the
permutation-canonical coefficient-map representation. -/
def VacuumSemigroupGapSlope.PositiveMultiplicityProfilePermutationCanonicalCoefficientRealFormStatement
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
          (G.admissibleRescaledDefectResolventPositiveMultiplicityProfilePermutationCanonicalCoefficientNormalForm
            hInnerSymmetric tau first tail) z)
      G.admissibleRescaledDefectTimeFilter
      (𝓝
        (diagonalComplexification
          (G.continuumResolventPositiveMultiplicityProfilePermutationCanonicalCoefficientNormalForm
            T hP hInnerSymmetric hSelf first tail) z))) ∧
  diagonalComplexification
      (G.continuumResolventPositiveMultiplicityProfilePermutationCanonicalCoefficientNormalForm
        T hP hInnerSymmetric hSelf first tail) ∈
    diagonalComplexificationStarSubalgebra
      (H := P.VacuumOrthogonalHilbert) ∧
  ∃! R : P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert,
    diagonalComplexification R =
      diagonalComplexification
        (G.continuumResolventPositiveMultiplicityProfilePermutationCanonicalCoefficientNormalForm
          T hP hInnerSymmetric hSelf first tail)

/-- Pairwise-distinct profiles carry the full actual OS real-form strong-limit
package through their uniquely sorted coefficient Finsupp representative. -/
theorem VacuumSemigroupGapSlope.canonicalPermutationCanonicalPositiveMultiplicityProfileCoefficientMapRealFormStrongLimitPackage
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
    G.PositiveMultiplicityProfilePermutationCanonicalCoefficientRealFormStatement
      T hP hInnerSymmetric hSelf first tail := by
  unfold VacuumSemigroupGapSlope.PositiveMultiplicityProfilePermutationCanonicalCoefficientRealFormStatement
  rcases
      G.canonicalPairwiseDistinctPositiveMultiplicityProfileProductRealFormStrongLimitPackage
        T hP hInnerSymmetric hSelf first tail hPairwise with
    ⟨hTendsto, hMem, hUnique⟩
  have hFinite : ∀ tau : G.AdmissibleRescaledDefectTime,
      G.admissibleRescaledDefectResolventPositiveMultiplicityProfilePermutationCanonicalCoefficientNormalForm
          hInnerSymmetric tau first tail =
        G.admissibleRescaledDefectResolventPositiveMultiplicityProfileProduct
          hInnerSymmetric tau first tail := by
    intro tau
    exact
      G.admissibleRescaledDefectResolventPositiveMultiplicityProfilePermutationCanonicalCoefficientNormalForm_eq_product_of_pairwise
        T hInnerSymmetric tau first tail hPairwise
  have hContinuum :
      G.continuumResolventPositiveMultiplicityProfilePermutationCanonicalCoefficientNormalForm
          T hP hInnerSymmetric hSelf first tail =
        G.continuumResolventPositiveMultiplicityProfileProduct
          T hP hInnerSymmetric hSelf first tail :=
    G.continuumResolventPositiveMultiplicityProfilePermutationCanonicalCoefficientNormalForm_eq_product_of_pairwise
      T hP hInnerSymmetric hSelf first tail hPairwise
  constructor
  · intro z
    simpa only [hFinite, hContinuum] using hTendsto z
  constructor
  · rw [hContinuum]
    exact hMem
  · rw [hContinuum]
    exact hUnique

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
