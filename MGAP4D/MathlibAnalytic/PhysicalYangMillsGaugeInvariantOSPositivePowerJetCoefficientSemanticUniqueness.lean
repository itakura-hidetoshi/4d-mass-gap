import MGAP4D.MathlibAnalytic.ContinuousLinearMapPositivePowerJetCoefficientSemanticUniqueness
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSPermutationCanonicalPositivePowerJetCoefficientMapRealFormLimit

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

/-- Global linear independence of all finite-time below-half-mass resolvent
positive powers.  This is the exact condition making coefficient-map evaluation
faithful at the chosen admissible time. -/
def VacuumSemigroupGapSlope.AdmissibleRescaledDefectResolventPositivePowerJetOperatorIndependent
    {T : P.StronglyContinuousPhysicalSemigroup}
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime) : Prop :=
  ContinuousLinearMap.PositivePowerJetCoefficientMap.IsOperatorIndependent
    (fun sigma : G.BelowHalfMassShift =>
      G.admissibleRescaledDefectResolvent
        hInnerSymmetric tau sigma.property)

/-- Global linear independence of all continuum below-half-mass resolvent
positive powers. -/
def VacuumSemigroupGapSlope.ContinuumResolventPositivePowerJetOperatorIndependent
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian) : Prop :=
  ContinuousLinearMap.PositivePowerJetCoefficientMap.IsOperatorIndependent
    (fun sigma : G.BelowHalfMassShift =>
      G.vacuumOrthogonalContinuumRealResolvent
        T hP hInnerSymmetric hSelf sigma.property)

/-- Support-local finite-time independence for two concrete coefficient maps. -/
def VacuumSemigroupGapSlope.AdmissibleRescaledDefectResolventPositivePowerJetCoefficientMapsIndependent
    {T : P.StronglyContinuousPhysicalSemigroup}
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    (c d : ContinuousLinearMap.PositivePowerJetCoefficientMap
      G.BelowHalfMassShift) : Prop :=
  c.AreOperatorIndependentOnSupport d
    (fun sigma : G.BelowHalfMassShift =>
      G.admissibleRescaledDefectResolvent
        hInnerSymmetric tau sigma.property)

/-- Support-local continuum independence for two concrete coefficient maps. -/
def VacuumSemigroupGapSlope.ContinuumResolventPositivePowerJetCoefficientMapsIndependent
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (c d : ContinuousLinearMap.PositivePowerJetCoefficientMap
      G.BelowHalfMassShift) : Prop :=
  c.AreOperatorIndependentOnSupport d
    (fun sigma : G.BelowHalfMassShift =>
      G.vacuumOrthogonalContinuumRealResolvent
        T hP hInnerSymmetric hSelf sigma.property)

/-- Global finite-time independence implies every support-local comparison. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolventPositivePowerJetCoefficientMapsIndependent_of_operatorIndependent
    {T : P.StronglyContinuousPhysicalSemigroup}
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    (hIndependent :
      G.AdmissibleRescaledDefectResolventPositivePowerJetOperatorIndependent
        hInnerSymmetric tau)
    (c d : ContinuousLinearMap.PositivePowerJetCoefficientMap
      G.BelowHalfMassShift) :
    G.AdmissibleRescaledDefectResolventPositivePowerJetCoefficientMapsIndependent
      hInnerSymmetric tau c d := by
  exact
    ContinuousLinearMap.PositivePowerJetCoefficientMap.
      areOperatorIndependentOnSupport_of_isOperatorIndependent
        (fun sigma : G.BelowHalfMassShift =>
          G.admissibleRescaledDefectResolvent
            hInnerSymmetric tau sigma.property)
        hIndependent c d

/-- Global continuum independence implies every support-local comparison. -/
theorem VacuumSemigroupGapSlope.continuumResolventPositivePowerJetCoefficientMapsIndependent_of_operatorIndependent
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (hIndependent :
      G.ContinuumResolventPositivePowerJetOperatorIndependent
        T hP hInnerSymmetric hSelf)
    (c d : ContinuousLinearMap.PositivePowerJetCoefficientMap
      G.BelowHalfMassShift) :
    G.ContinuumResolventPositivePowerJetCoefficientMapsIndependent
      T hP hInnerSymmetric hSelf c d := by
  exact
    ContinuousLinearMap.PositivePowerJetCoefficientMap.
      areOperatorIndependentOnSupport_of_isOperatorIndependent
        (fun sigma : G.BelowHalfMassShift =>
          G.vacuumOrthogonalContinuumRealResolvent
            T hP hInnerSymmetric hSelf sigma.property)
        hIndependent c d

/-- At one faithful finite time, pairwise-distinct permutations have exactly the
same recursively aggregated OS coefficient Finsupp. -/
theorem VacuumSemigroupGapSlope.resolventPositiveMultiplicityProfileCoefficientMap_eq_of_perm_of_pairwise_of_admissibleSupportIndependent
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
    (hIndependent :
      G.AdmissibleRescaledDefectResolventPositivePowerJetCoefficientMapsIndependent
        hInnerSymmetric tau
        (G.resolventPositiveMultiplicityProfileCoefficientMap first₁ tail₁)
        (G.resolventPositiveMultiplicityProfileCoefficientMap first₂ tail₂)) :
    G.resolventPositiveMultiplicityProfileCoefficientMap first₁ tail₁ =
      G.resolventPositiveMultiplicityProfileCoefficientMap first₂ tail₂ := by
  simpa [
    VacuumSemigroupGapSlope.resolventPositiveMultiplicityProfileCoefficientMap,
    VacuumSemigroupGapSlope.AdmissibleRescaledDefectResolventPositivePowerJetCoefficientMapsIndependent] using
    (ContinuousLinearMap.positiveMultiplicityProfileCoefficientMap_eq_of_perm_of_pairwise_of_supportIndependent
      (fun sigma : G.BelowHalfMassShift =>
        G.admissibleRescaledDefectResolvent
          hInnerSymmetric tau sigma.property)
      (fun sigma : G.BelowHalfMassShift => sigma.1)
      first₁ first₂ tail₁ tail₂ hPerm hPairwise₁
      (fun sigma rho =>
        G.admissibleRescaledDefectResolvent_identity
          T hInnerSymmetric tau sigma.property rho.property)
      hIndependent)

/-- At a faithful continuum family, pairwise-distinct permutations have exactly
the same recursively aggregated OS coefficient Finsupp. -/
theorem VacuumSemigroupGapSlope.resolventPositiveMultiplicityProfileCoefficientMap_eq_of_perm_of_pairwise_of_continuumSupportIndependent
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
    (hIndependent :
      G.ContinuumResolventPositivePowerJetCoefficientMapsIndependent
        T hP hInnerSymmetric hSelf
        (G.resolventPositiveMultiplicityProfileCoefficientMap first₁ tail₁)
        (G.resolventPositiveMultiplicityProfileCoefficientMap first₂ tail₂)) :
    G.resolventPositiveMultiplicityProfileCoefficientMap first₁ tail₁ =
      G.resolventPositiveMultiplicityProfileCoefficientMap first₂ tail₂ := by
  simpa [
    VacuumSemigroupGapSlope.resolventPositiveMultiplicityProfileCoefficientMap,
    VacuumSemigroupGapSlope.ContinuumResolventPositivePowerJetCoefficientMapsIndependent] using
    (ContinuousLinearMap.positiveMultiplicityProfileCoefficientMap_eq_of_perm_of_pairwise_of_supportIndependent
      (fun sigma : G.BelowHalfMassShift =>
        G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf sigma.property)
      (fun sigma : G.BelowHalfMassShift => sigma.1)
      first₁ first₂ tail₁ tail₂ hPerm hPairwise₁
      (fun sigma rho =>
        G.vacuumOrthogonalContinuumRealResolvent_identity
          T hP hInnerSymmetric hSelf sigma.property rho.property)
      hIndependent)

/-- At one faithful finite time, the permutation-canonical OS coefficient map
is the older recursively aggregated map itself. -/
theorem VacuumSemigroupGapSlope.resolventPositiveMultiplicityProfilePermutationCanonicalCoefficientMap_eq_coefficientMap_of_pairwise_of_admissibleSupportIndependent
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    (first : ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift)
    (tail : List (ContinuousLinearMap.PositiveMultiplicityProfileEntry
      G.BelowHalfMassShift))
    (hPairwise :
      G.BelowHalfMassPositiveMultiplicityProfilePairwiseDistinct first tail)
    (hIndependent :
      G.AdmissibleRescaledDefectResolventPositivePowerJetCoefficientMapsIndependent
        hInnerSymmetric tau
        (G.resolventPositiveMultiplicityProfilePermutationCanonicalCoefficientMap
          first tail)
        (G.resolventPositiveMultiplicityProfileCoefficientMap first tail)) :
    G.resolventPositiveMultiplicityProfilePermutationCanonicalCoefficientMap
        first tail =
      G.resolventPositiveMultiplicityProfileCoefficientMap first tail := by
  simpa [
    VacuumSemigroupGapSlope.resolventPositiveMultiplicityProfilePermutationCanonicalCoefficientMap,
    VacuumSemigroupGapSlope.resolventPositiveMultiplicityProfileCoefficientMap,
    VacuumSemigroupGapSlope.AdmissibleRescaledDefectResolventPositivePowerJetCoefficientMapsIndependent] using
    (ContinuousLinearMap.positiveMultiplicityProfilePermutationCanonicalCoefficientMap_eq_coefficientMap_of_pairwise_of_supportIndependent
      (fun sigma : G.BelowHalfMassShift =>
        G.admissibleRescaledDefectResolvent
          hInnerSymmetric tau sigma.property)
      (fun sigma : G.BelowHalfMassShift => sigma.1)
      first tail hPairwise
      (fun sigma rho =>
        G.admissibleRescaledDefectResolvent_identity
          T hInnerSymmetric tau sigma.property rho.property)
      hIndependent)

/-- At a faithful continuum family, the permutation-canonical OS coefficient
map is the older recursively aggregated map itself. -/
theorem VacuumSemigroupGapSlope.resolventPositiveMultiplicityProfilePermutationCanonicalCoefficientMap_eq_coefficientMap_of_pairwise_of_continuumSupportIndependent
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
      G.BelowHalfMassPositiveMultiplicityProfilePairwiseDistinct first tail)
    (hIndependent :
      G.ContinuumResolventPositivePowerJetCoefficientMapsIndependent
        T hP hInnerSymmetric hSelf
        (G.resolventPositiveMultiplicityProfilePermutationCanonicalCoefficientMap
          first tail)
        (G.resolventPositiveMultiplicityProfileCoefficientMap first tail)) :
    G.resolventPositiveMultiplicityProfilePermutationCanonicalCoefficientMap
        first tail =
      G.resolventPositiveMultiplicityProfileCoefficientMap first tail := by
  simpa [
    VacuumSemigroupGapSlope.resolventPositiveMultiplicityProfilePermutationCanonicalCoefficientMap,
    VacuumSemigroupGapSlope.resolventPositiveMultiplicityProfileCoefficientMap,
    VacuumSemigroupGapSlope.ContinuumResolventPositivePowerJetCoefficientMapsIndependent] using
    (ContinuousLinearMap.positiveMultiplicityProfilePermutationCanonicalCoefficientMap_eq_coefficientMap_of_pairwise_of_supportIndependent
      (fun sigma : G.BelowHalfMassShift =>
        G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf sigma.property)
      (fun sigma : G.BelowHalfMassShift => sigma.1)
      first tail hPairwise
      (fun sigma rho =>
        G.vacuumOrthogonalContinuumRealResolvent_identity
          T hP hInnerSymmetric hSelf sigma.property rho.property)
      hIndependent)

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
