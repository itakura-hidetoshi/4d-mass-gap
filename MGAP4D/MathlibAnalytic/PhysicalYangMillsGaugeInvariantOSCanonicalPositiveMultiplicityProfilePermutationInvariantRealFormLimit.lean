import MGAP4D.MathlibAnalytic.ContinuousLinearMapPositiveMultiplicityProfilePermutationInvariantNormalForm
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalPairwiseDistinctPositiveMultiplicityProfileRealFormLimit

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

/-- At finite time, a pairwise-distinct mixed positive-resolvent product is
 invariant under every permutation of its multiplicity-profile entries. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventPositiveMultiplicityProfileProduct_eq_of_perm_of_pairwise
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    (first₁ first₂ : ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)
    (tail₁ tail₂ : List (ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift))
    (hPerm : (first₁ :: tail₁).Perm (first₂ :: tail₂))
    (hPairwise :
      G.BelowHalfMassPositiveMultiplicityProfilePairwiseDistinct first₁ tail₁) :
    G.admissibleRescaledDefectResolventPositiveMultiplicityProfileProduct
        hInnerSymmetric tau first₁ tail₁ =
      G.admissibleRescaledDefectResolventPositiveMultiplicityProfileProduct
        hInnerSymmetric tau first₂ tail₂ := by
  exact
    ContinuousLinearMap.positiveMultiplicityProfileProduct_eq_of_perm_of_pairwise
      (fun sigma : G.BelowHalfMassShift =>
        G.admissibleRescaledDefectResolvent
          hInnerSymmetric tau sigma.property)
      (fun sigma : G.BelowHalfMassShift => sigma.1)
      first₁ first₂ tail₁ tail₂ hPerm hPairwise
      (fun sigma rho =>
        G.admissibleRescaledDefectResolvent_identity
          T hInnerSymmetric tau sigma.property rho.property)

/-- In the continuum, a pairwise-distinct mixed positive-resolvent product is
 invariant under every permutation of its multiplicity-profile entries. -/
theorem VacuumSemigroupGapSlope.continuumResolventPositiveMultiplicityProfileProduct_eq_of_perm_of_pairwise
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (first₁ first₂ : ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)
    (tail₁ tail₂ : List (ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift))
    (hPerm : (first₁ :: tail₁).Perm (first₂ :: tail₂))
    (hPairwise :
      G.BelowHalfMassPositiveMultiplicityProfilePairwiseDistinct first₁ tail₁) :
    G.continuumResolventPositiveMultiplicityProfileProduct
        T hP hInnerSymmetric hSelf first₁ tail₁ =
      G.continuumResolventPositiveMultiplicityProfileProduct
        T hP hInnerSymmetric hSelf first₂ tail₂ := by
  exact
    ContinuousLinearMap.positiveMultiplicityProfileProduct_eq_of_perm_of_pairwise
      (fun sigma : G.BelowHalfMassShift =>
        G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf sigma.property)
      (fun sigma : G.BelowHalfMassShift => sigma.1)
      first₁ first₂ tail₁ tail₂ hPerm hPairwise
      (fun sigma rho =>
        G.vacuumOrthogonalContinuumRealResolvent_identity
          T hP hInnerSymmetric hSelf sigma.property rho.property)

/-- Finite-time flattened normal forms have the same operator value for two
 pairwise-distinct orderings of the same multiplicity profile. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventPositiveMultiplicityProfileNormalForm_eq_of_perm_of_pairwise
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    (first₁ first₂ : ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)
    (tail₁ tail₂ : List (ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift))
    (hPerm : (first₁ :: tail₁).Perm (first₂ :: tail₂))
    (hPairwise₁ :
      G.BelowHalfMassPositiveMultiplicityProfilePairwiseDistinct first₁ tail₁)
    (hPairwise₂ :
      G.BelowHalfMassPositiveMultiplicityProfilePairwiseDistinct first₂ tail₂) :
    G.admissibleRescaledDefectResolventPositiveMultiplicityProfileNormalForm
        hInnerSymmetric tau first₁ tail₁ =
      G.admissibleRescaledDefectResolventPositiveMultiplicityProfileNormalForm
        hInnerSymmetric tau first₂ tail₂ := by
  calc
    G.admissibleRescaledDefectResolventPositiveMultiplicityProfileNormalForm
        hInnerSymmetric tau first₁ tail₁ =
      G.admissibleRescaledDefectResolventPositiveMultiplicityProfileProduct
        hInnerSymmetric tau first₁ tail₁ :=
      G.admissibleRescaledDefectResolventPositiveMultiplicityProfileNormalForm_eq_product_of_pairwise
        T hInnerSymmetric tau first₁ tail₁ hPairwise₁
    _ = G.admissibleRescaledDefectResolventPositiveMultiplicityProfileProduct
        hInnerSymmetric tau first₂ tail₂ :=
      G.admissibleRescaledDefectResolventPositiveMultiplicityProfileProduct_eq_of_perm_of_pairwise
        T hInnerSymmetric tau first₁ first₂ tail₁ tail₂ hPerm hPairwise₁
    _ = G.admissibleRescaledDefectResolventPositiveMultiplicityProfileNormalForm
        hInnerSymmetric tau first₂ tail₂ :=
      (G.admissibleRescaledDefectResolventPositiveMultiplicityProfileNormalForm_eq_product_of_pairwise
        T hInnerSymmetric tau first₂ tail₂ hPairwise₂).symm

/-- Continuum flattened normal forms have the same operator value for two
 pairwise-distinct orderings of the same multiplicity profile. -/
theorem VacuumSemigroupGapSlope.continuumResolventPositiveMultiplicityProfileNormalForm_eq_of_perm_of_pairwise
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (first₁ first₂ : ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)
    (tail₁ tail₂ : List (ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift))
    (hPerm : (first₁ :: tail₁).Perm (first₂ :: tail₂))
    (hPairwise₁ :
      G.BelowHalfMassPositiveMultiplicityProfilePairwiseDistinct first₁ tail₁)
    (hPairwise₂ :
      G.BelowHalfMassPositiveMultiplicityProfilePairwiseDistinct first₂ tail₂) :
    G.continuumResolventPositiveMultiplicityProfileNormalForm
        T hP hInnerSymmetric hSelf first₁ tail₁ =
      G.continuumResolventPositiveMultiplicityProfileNormalForm
        T hP hInnerSymmetric hSelf first₂ tail₂ := by
  calc
    G.continuumResolventPositiveMultiplicityProfileNormalForm
        T hP hInnerSymmetric hSelf first₁ tail₁ =
      G.continuumResolventPositiveMultiplicityProfileProduct
        T hP hInnerSymmetric hSelf first₁ tail₁ :=
      G.continuumResolventPositiveMultiplicityProfileNormalForm_eq_product_of_pairwise
        T hP hInnerSymmetric hSelf first₁ tail₁ hPairwise₁
    _ = G.continuumResolventPositiveMultiplicityProfileProduct
        T hP hInnerSymmetric hSelf first₂ tail₂ :=
      G.continuumResolventPositiveMultiplicityProfileProduct_eq_of_perm_of_pairwise
        T hP hInnerSymmetric hSelf first₁ first₂ tail₁ tail₂ hPerm hPairwise₁
    _ = G.continuumResolventPositiveMultiplicityProfileNormalForm
        T hP hInnerSymmetric hSelf first₂ tail₂ :=
      (G.continuumResolventPositiveMultiplicityProfileNormalForm_eq_product_of_pairwise
        T hP hInnerSymmetric hSelf first₂ tail₂ hPairwise₂).symm

/-- The actual OS product real-form strong-limit package transports to every
 permutation of a pairwise-distinct source multiplicity profile. -/
theorem VacuumSemigroupGapSlope.canonicalPermutedPositiveMultiplicityProfileProductRealFormStrongLimitPackage
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (first₁ first₂ : ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)
    (tail₁ tail₂ : List (ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift))
    (hPerm : (first₁ :: tail₁).Perm (first₂ :: tail₂))
    (hPairwise :
      G.BelowHalfMassPositiveMultiplicityProfilePairwiseDistinct first₁ tail₁) :
    G.PositiveMultiplicityProfileProductRealFormStatement
      T hP hInnerSymmetric hSelf first₂ tail₂ := by
  unfold VacuumSemigroupGapSlope.PositiveMultiplicityProfileProductRealFormStatement
  rcases
      G.canonicalPairwiseDistinctPositiveMultiplicityProfileProductRealFormStrongLimitPackage
        T hP hInnerSymmetric hSelf first₁ tail₁ hPairwise with
    ⟨hTendsto, hMem, hUnique⟩
  have hFinite : ∀ tau : G.AdmissibleRescaledDefectTime,
      G.admissibleRescaledDefectResolventPositiveMultiplicityProfileProduct
          hInnerSymmetric tau first₁ tail₁ =
        G.admissibleRescaledDefectResolventPositiveMultiplicityProfileProduct
          hInnerSymmetric tau first₂ tail₂ := by
    intro tau
    exact
      G.admissibleRescaledDefectResolventPositiveMultiplicityProfileProduct_eq_of_perm_of_pairwise
        T hInnerSymmetric tau first₁ first₂ tail₁ tail₂ hPerm hPairwise
  have hContinuum :
      G.continuumResolventPositiveMultiplicityProfileProduct
          T hP hInnerSymmetric hSelf first₁ tail₁ =
        G.continuumResolventPositiveMultiplicityProfileProduct
          T hP hInnerSymmetric hSelf first₂ tail₂ :=
    G.continuumResolventPositiveMultiplicityProfileProduct_eq_of_perm_of_pairwise
      T hP hInnerSymmetric hSelf first₁ first₂ tail₁ tail₂ hPerm hPairwise
  constructor
  · intro z
    have hSource :
        (fun tau : G.AdmissibleRescaledDefectTime =>
          diagonalComplexification
            (G.admissibleRescaledDefectResolventPositiveMultiplicityProfileProduct
              hInnerSymmetric tau first₁ tail₁) z) =
        (fun tau : G.AdmissibleRescaledDefectTime =>
          diagonalComplexification
            (G.admissibleRescaledDefectResolventPositiveMultiplicityProfileProduct
              hInnerSymmetric tau first₂ tail₂) z) := by
      funext tau
      rw [hFinite tau]
    have hTarget :
        diagonalComplexification
            (G.continuumResolventPositiveMultiplicityProfileProduct
              T hP hInnerSymmetric hSelf first₁ tail₁) z =
          diagonalComplexification
            (G.continuumResolventPositiveMultiplicityProfileProduct
              T hP hInnerSymmetric hSelf first₂ tail₂) z := by
      rw [hContinuum]
    rw [← hSource, ← hTarget]
    exact hTendsto z
  constructor
  · rw [← hContinuum]
    exact hMem
  · rw [← hContinuum]
    exact hUnique

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
