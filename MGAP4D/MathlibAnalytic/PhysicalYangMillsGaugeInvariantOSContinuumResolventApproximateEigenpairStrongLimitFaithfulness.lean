import MGAP4D.MathlibAnalytic.LinearPMapClosedApproximateEigenpairStrongLimit
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSContinuumResolventConfluentCauchySpectralWitnessFaithfulness
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace LinearPMap

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- Strong approximate eigenpairs in the domain of the closed continuum
excitation Hamiltonian.  In a finite-volume application the domain points are
graph-compatible lifts of finite-volume eigenvectors. -/
abbrev VacuumSemigroupGapSlope.ContinuumResolventApproximateEigenpairStrongLimitData
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (nodes : Finset G.BelowHalfMassShift)
    (orderCap : ℕ) :=
  ClosedLinearPMapFiniteApproximateEigenpairStrongLimitData
    (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf)
    (nodes.card * orderCap)

/-- Strong approximate eigenpair limits produce exact confluent spectral
witnesses for the closed continuum excitation Hamiltonian. -/
noncomputable def VacuumSemigroupGapSlope.ContinuumResolventApproximateEigenpairStrongLimitData.toContinuumResolventConfluentSpectralWitnessData
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (nodes : Finset G.BelowHalfMassShift)
    (orderCap : ℕ)
    (R : G.ContinuumResolventApproximateEigenpairStrongLimitData
      T hSelf nodes orderCap) :
    G.ContinuumResolventConfluentSpectralWitnessData
      T hP hInnerSymmetric hSelf nodes orderCap := by
  let exactData := R.toFiniteDistinctClosedEigenpairData
    (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint_isClosed hP hSelf)
  exact
    { SpectralIndex := exactData.SpectralIndex
      spectralFintype := exactData.spectralFintype
      spectralValue := exactData.spectralValue
      spectralValue_injective := exactData.spectralValue_injective
      spectralCard := exactData.spectralCard
      spectralVector := exactData.spectralVector
      spectralVector_ne_zero := exactData.spectralVector_ne_zero
      hamiltonian_apply_spectralVector := exactData.apply_spectralVector }

/-- The selected continuum resolvent powers are linearly independent when a
finite family of graph-compatible approximate eigenpairs converges strongly
with vanishing target residual. -/
theorem VacuumSemigroupGapSlope.continuumResolventConfluentCauchy_linearIndependent_of_approximateEigenpairStrongLimit
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (nodes : Finset G.BelowHalfMassShift)
    (orderCap : ℕ)
    (R : G.ContinuumResolventApproximateEigenpairStrongLimitData
      T hSelf nodes orderCap) :
    LinearIndependent ℝ
      (fun p : nodes × Fin orderCap =>
        ContinuousLinearMap.positivePowerJetOperatorFamily
          (fun sigma : G.BelowHalfMassShift =>
            G.vacuumOrthogonalContinuumRealResolvent
              T hP hInnerSymmetric hSelf sigma.property)
          (p.1.1, p.2.1)) :=
  G.continuumResolventConfluentCauchy_linearIndependent_of_confluentSpectralWitness
    T hP hInnerSymmetric hSelf nodes orderCap
    (VacuumSemigroupGapSlope.ContinuumResolventApproximateEigenpairStrongLimitData.toContinuumResolventConfluentSpectralWitnessData
      T G hP hInnerSymmetric hSelf nodes orderCap R)

/-- Strong approximate eigenpair transport supplies support-local coefficient
faithfulness for every coefficient map fitting the selected node-order window. -/
theorem VacuumSemigroupGapSlope.continuumResolventPositivePowerJetCoefficientMapsIndependent_of_approximateEigenpairStrongLimit
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (nodes : Finset G.BelowHalfMassShift)
    (orderCap : ℕ)
    (R : G.ContinuumResolventApproximateEigenpairStrongLimitData
      T hSelf nodes orderCap)
    (left right : ContinuousLinearMap.PositivePowerJetCoefficientMap
      G.BelowHalfMassShift)
    (hFit : G.PositivePowerJetCoefficientMapsFitWindow
      nodes orderCap left right) :
    G.ContinuumResolventPositivePowerJetCoefficientMapsIndependent
      T hP hInnerSymmetric hSelf left right :=
  G.continuumResolventPositivePowerJetCoefficientMapsIndependent_of_confluentSpectralWitness
    T hP hInnerSymmetric hSelf nodes orderCap
    (VacuumSemigroupGapSlope.ContinuumResolventApproximateEigenpairStrongLimitData.toContinuumResolventConfluentSpectralWitnessData
      T G hP hInnerSymmetric hSelf nodes orderCap R)
    left right hFit

/-- Strong approximate eigenpair transport upgrades profile permutation
invariance to exact recursive coefficient Finsupp equality. -/
theorem VacuumSemigroupGapSlope.resolventPositiveMultiplicityProfileCoefficientMap_eq_of_perm_of_pairwise_of_continuumApproximateEigenpairStrongLimit
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (nodes : Finset G.BelowHalfMassShift)
    (orderCap : ℕ)
    (R : G.ContinuumResolventApproximateEigenpairStrongLimitData
      T hSelf nodes orderCap)
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
      G.resolventPositiveMultiplicityProfileCoefficientMap first₂ tail₂ :=
  G.resolventPositiveMultiplicityProfileCoefficientMap_eq_of_perm_of_pairwise_of_continuumConfluentSpectralWitness
    T hP hInnerSymmetric hSelf nodes orderCap
    (VacuumSemigroupGapSlope.ContinuumResolventApproximateEigenpairStrongLimitData.toContinuumResolventConfluentSpectralWitnessData
      T G hP hInnerSymmetric hSelf nodes orderCap R)
    first₁ first₂ tail₁ tail₂ hPerm hPairwise₁ hFit

/-- Strong approximate eigenpair transport identifies the permutation-canonical
coefficient map with the recursive coefficient map. -/
theorem VacuumSemigroupGapSlope.resolventPositiveMultiplicityProfilePermutationCanonicalCoefficientMap_eq_coefficientMap_of_pairwise_of_continuumApproximateEigenpairStrongLimit
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (nodes : Finset G.BelowHalfMassShift)
    (orderCap : ℕ)
    (R : G.ContinuumResolventApproximateEigenpairStrongLimitData
      T hSelf nodes orderCap)
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
      G.resolventPositiveMultiplicityProfileCoefficientMap first tail :=
  G.resolventPositiveMultiplicityProfilePermutationCanonicalCoefficientMap_eq_coefficientMap_of_pairwise_of_continuumConfluentSpectralWitness
    T hP hInnerSymmetric hSelf nodes orderCap
    (VacuumSemigroupGapSlope.ContinuumResolventApproximateEigenpairStrongLimitData.toContinuumResolventConfluentSpectralWitnessData
      T G hP hInnerSymmetric hSelf nodes orderCap R)
    first tail hPairwise hFit

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
