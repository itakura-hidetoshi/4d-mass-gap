import MGAP4D.MathlibAnalytic.ContinuousLinearMapRationalFunctionalCalculusPositivePowerJetFaithfulness
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSPositivePowerJetCoefficientSemanticUniqueness

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

/-- A faithful finite rational functional calculus realizing the selected
finite-time below-half-mass resolvent powers. -/
abbrev VacuumSemigroupGapSlope.AdmissibleRescaledDefectResolventFiniteRationalFunctionalCalculusData
    {T : P.StronglyContinuousPhysicalSemigroup}
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    (nodes : Finset G.BelowHalfMassShift)
    (orderCap : ℕ) :=
  ContinuousLinearMap.PositivePowerJetCoefficientMap.FiniteRationalFunctionalCalculusData
    (fun sigma : G.BelowHalfMassShift =>
      G.admissibleRescaledDefectResolvent
        hInnerSymmetric tau sigma.property)
    (fun sigma : G.BelowHalfMassShift => sigma.1)
    nodes orderCap

/-- A faithful finite rational functional calculus realizing the selected
continuum below-half-mass resolvent powers. -/
abbrev VacuumSemigroupGapSlope.ContinuumResolventFiniteRationalFunctionalCalculusData
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (nodes : Finset G.BelowHalfMassShift)
    (orderCap : ℕ) :=
  ContinuousLinearMap.PositivePowerJetCoefficientMap.FiniteRationalFunctionalCalculusData
    (fun sigma : G.BelowHalfMassShift =>
      G.vacuumOrthogonalContinuumRealResolvent
        T hP hInnerSymmetric hSelf sigma.property)
    (fun sigma : G.BelowHalfMassShift => sigma.1)
    nodes orderCap

/-- Two coefficient maps fit a selected finite node and order window. -/
def VacuumSemigroupGapSlope.PositivePowerJetCoefficientMapsFitWindow
    {T : P.StronglyContinuousPhysicalSemigroup}
    (G : T.VacuumSemigroupGapSlope)
    (nodes : Finset G.BelowHalfMassShift)
    (orderCap : ℕ)
    (left right : ContinuousLinearMap.PositivePowerJetCoefficientMap
      G.BelowHalfMassShift) : Prop :=
  (∀ p,
    p ∈ ((↑left.support : Set (G.BelowHalfMassShift × ℕ)) ∪
      ↑right.support) → p.1 ∈ nodes) ∧
  ∀ p,
    p ∈ ((↑left.support : Set (G.BelowHalfMassShift × ℕ)) ∪
      ↑right.support) → p.2 < orderCap

/-- A faithful finite-time rational functional calculus supplies the exact
support-local independence condition used by coefficient semantic uniqueness. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventPositivePowerJetCoefficientMapsIndependent_of_finiteRationalFunctionalCalculus
    {T : P.StronglyContinuousPhysicalSemigroup}
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    (nodes : Finset G.BelowHalfMassShift)
    (orderCap : ℕ)
    (R : G.AdmissibleRescaledDefectResolventFiniteRationalFunctionalCalculusData
      hInnerSymmetric tau nodes orderCap)
    (left right : ContinuousLinearMap.PositivePowerJetCoefficientMap
      G.BelowHalfMassShift)
    (hFit : G.PositivePowerJetCoefficientMapsFitWindow
      nodes orderCap left right) :
    G.AdmissibleRescaledDefectResolventPositivePowerJetCoefficientMapsIndependent
      hInnerSymmetric tau left right := by
  rcases hFit with ⟨hNodes, hOrders⟩
  simpa [
    VacuumSemigroupGapSlope.AdmissibleRescaledDefectResolventPositivePowerJetCoefficientMapsIndependent] using
    (ContinuousLinearMap.PositivePowerJetCoefficientMap.areOperatorIndependentOnSupport_of_finiteRationalFunctionalCalculus
      (fun sigma : G.BelowHalfMassShift =>
        G.admissibleRescaledDefectResolvent
          hInnerSymmetric tau sigma.property)
      (fun sigma : G.BelowHalfMassShift => sigma.1)
      nodes orderCap R left right hNodes hOrders)

/-- A faithful continuum rational functional calculus supplies the exact
support-local independence condition used by coefficient semantic uniqueness. -/
theorem VacuumSemigroupGapSlope.continuumResolventPositivePowerJetCoefficientMapsIndependent_of_finiteRationalFunctionalCalculus
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (nodes : Finset G.BelowHalfMassShift)
    (orderCap : ℕ)
    (R : G.ContinuumResolventFiniteRationalFunctionalCalculusData
      T hP hInnerSymmetric hSelf nodes orderCap)
    (left right : ContinuousLinearMap.PositivePowerJetCoefficientMap
      G.BelowHalfMassShift)
    (hFit : G.PositivePowerJetCoefficientMapsFitWindow
      nodes orderCap left right) :
    G.ContinuumResolventPositivePowerJetCoefficientMapsIndependent
      T hP hInnerSymmetric hSelf left right := by
  rcases hFit with ⟨hNodes, hOrders⟩
  simpa [
    VacuumSemigroupGapSlope.ContinuumResolventPositivePowerJetCoefficientMapsIndependent] using
    (ContinuousLinearMap.PositivePowerJetCoefficientMap.areOperatorIndependentOnSupport_of_finiteRationalFunctionalCalculus
      (fun sigma : G.BelowHalfMassShift =>
        G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf sigma.property)
      (fun sigma : G.BelowHalfMassShift => sigma.1)
      nodes orderCap R left right hNodes hOrders)

/-- A finite-time rational functional calculus upgrades operator-level profile
permutation invariance to equality of the recursively aggregated OS Finsupps. -/
theorem VacuumSemigroupGapSlope.resolventPositiveMultiplicityProfileCoefficientMap_eq_of_perm_of_pairwise_of_finiteRationalFunctionalCalculus
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    (nodes : Finset G.BelowHalfMassShift)
    (orderCap : ℕ)
    (R : G.AdmissibleRescaledDefectResolventFiniteRationalFunctionalCalculusData
      hInnerSymmetric tau nodes orderCap)
    (first₁ first₂ : ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)
    (tail₁ tail₂ : List (ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift))
    (hPerm : (first₁ :: tail₁).Perm (first₂ :: tail₂))
    (hPairwise₁ :
      G.BelowHalfMassPositiveMultiplicityProfilePairwiseDistinct first₁ tail₁)
    (hFit : G.PositivePowerJetCoefficientMapsFitWindow nodes orderCap
      (G.resolventPositiveMultiplicityProfileCoefficientMap first₁ tail₁)
      (G.resolventPositiveMultiplicityProfileCoefficientMap first₂ tail₂)) :
    G.resolventPositiveMultiplicityProfileCoefficientMap first₁ tail₁ =
      G.resolventPositiveMultiplicityProfileCoefficientMap first₂ tail₂ := by
  apply
    G.resolventPositiveMultiplicityProfileCoefficientMap_eq_of_perm_of_pairwise_of_admissibleSupportIndependent
      T hInnerSymmetric tau first₁ first₂ tail₁ tail₂ hPerm hPairwise₁
  exact
    G.admissibleRescaledDefectResolventPositivePowerJetCoefficientMapsIndependent_of_finiteRationalFunctionalCalculus
      hInnerSymmetric tau nodes orderCap R _ _ hFit

/-- A continuum rational functional calculus upgrades operator-level profile
permutation invariance to equality of the recursively aggregated OS Finsupps. -/
theorem VacuumSemigroupGapSlope.resolventPositiveMultiplicityProfileCoefficientMap_eq_of_perm_of_pairwise_of_continuumRationalFunctionalCalculus
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (nodes : Finset G.BelowHalfMassShift)
    (orderCap : ℕ)
    (R : G.ContinuumResolventFiniteRationalFunctionalCalculusData
      T hP hInnerSymmetric hSelf nodes orderCap)
    (first₁ first₂ : ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)
    (tail₁ tail₂ : List (ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift))
    (hPerm : (first₁ :: tail₁).Perm (first₂ :: tail₂))
    (hPairwise₁ :
      G.BelowHalfMassPositiveMultiplicityProfilePairwiseDistinct first₁ tail₁)
    (hFit : G.PositivePowerJetCoefficientMapsFitWindow nodes orderCap
      (G.resolventPositiveMultiplicityProfileCoefficientMap first₁ tail₁)
      (G.resolventPositiveMultiplicityProfileCoefficientMap first₂ tail₂)) :
    G.resolventPositiveMultiplicityProfileCoefficientMap first₁ tail₁ =
      G.resolventPositiveMultiplicityProfileCoefficientMap first₂ tail₂ := by
  apply
    G.resolventPositiveMultiplicityProfileCoefficientMap_eq_of_perm_of_pairwise_of_continuumSupportIndependent
      T hP hInnerSymmetric hSelf first₁ first₂ tail₁ tail₂ hPerm hPairwise₁
  exact
    G.continuumResolventPositivePowerJetCoefficientMapsIndependent_of_finiteRationalFunctionalCalculus
      T hP hInnerSymmetric hSelf nodes orderCap R _ _ hFit

/-- At finite time, a faithful rational functional calculus identifies the
permutation-canonical coefficient map with the recursively aggregated map. -/
theorem VacuumSemigroupGapSlope.resolventPositiveMultiplicityProfilePermutationCanonicalCoefficientMap_eq_coefficientMap_of_pairwise_of_finiteRationalFunctionalCalculus
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    (nodes : Finset G.BelowHalfMassShift)
    (orderCap : ℕ)
    (R : G.AdmissibleRescaledDefectResolventFiniteRationalFunctionalCalculusData
      hInnerSymmetric tau nodes orderCap)
    (first : ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)
    (tail : List (ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift))
    (hPairwise :
      G.BelowHalfMassPositiveMultiplicityProfilePairwiseDistinct first tail)
    (hFit : G.PositivePowerJetCoefficientMapsFitWindow nodes orderCap
      (G.resolventPositiveMultiplicityProfilePermutationCanonicalCoefficientMap
        first tail)
      (G.resolventPositiveMultiplicityProfileCoefficientMap first tail)) :
    G.resolventPositiveMultiplicityProfilePermutationCanonicalCoefficientMap
        first tail =
      G.resolventPositiveMultiplicityProfileCoefficientMap first tail := by
  apply
    G.resolventPositiveMultiplicityProfilePermutationCanonicalCoefficientMap_eq_coefficientMap_of_pairwise_of_admissibleSupportIndependent
      T hInnerSymmetric tau first tail hPairwise
  exact
    G.admissibleRescaledDefectResolventPositivePowerJetCoefficientMapsIndependent_of_finiteRationalFunctionalCalculus
      hInnerSymmetric tau nodes orderCap R _ _ hFit

/-- In the continuum, a faithful rational functional calculus identifies the
permutation-canonical coefficient map with the recursively aggregated map. -/
theorem VacuumSemigroupGapSlope.resolventPositiveMultiplicityProfilePermutationCanonicalCoefficientMap_eq_coefficientMap_of_pairwise_of_continuumRationalFunctionalCalculus
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (nodes : Finset G.BelowHalfMassShift)
    (orderCap : ℕ)
    (R : G.ContinuumResolventFiniteRationalFunctionalCalculusData
      T hP hInnerSymmetric hSelf nodes orderCap)
    (first : ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)
    (tail : List (ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift))
    (hPairwise :
      G.BelowHalfMassPositiveMultiplicityProfilePairwiseDistinct first tail)
    (hFit : G.PositivePowerJetCoefficientMapsFitWindow nodes orderCap
      (G.resolventPositiveMultiplicityProfilePermutationCanonicalCoefficientMap
        first tail)
      (G.resolventPositiveMultiplicityProfileCoefficientMap first tail)) :
    G.resolventPositiveMultiplicityProfilePermutationCanonicalCoefficientMap
        first tail =
      G.resolventPositiveMultiplicityProfileCoefficientMap first tail := by
  apply
    G.resolventPositiveMultiplicityProfilePermutationCanonicalCoefficientMap_eq_coefficientMap_of_pairwise_of_continuumSupportIndependent
      T hP hInnerSymmetric hSelf first tail hPairwise
  exact
    G.continuumResolventPositivePowerJetCoefficientMapsIndependent_of_finiteRationalFunctionalCalculus
      T hP hInnerSymmetric hSelf nodes orderCap R _ _ hFit

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
