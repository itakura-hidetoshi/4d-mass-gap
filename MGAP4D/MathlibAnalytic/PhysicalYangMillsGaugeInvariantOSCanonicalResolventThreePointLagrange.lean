import MGAP4D.MathlibAnalytic.ContinuousLinearMapResolventThreePointLagrange
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalResolventThreePointDividedDifference

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

/-- At every admissible positive time, a product of three pairwise-distinct
real resolvents is the symmetric three-point Lagrange combination. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolvent_comp_comp_eq_threePointLagrangeCombination
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    {lambda mu nu : ℝ}
    (hlambda : lambda < G.mass / 2)
    (hmu : mu < G.mass / 2)
    (hnu : nu < G.mass / 2)
    (hlambdaMu : lambda ≠ mu)
    (hlambdaNu : lambda ≠ nu)
    (hmuNu : mu ≠ nu) :
    (G.admissibleRescaledDefectResolvent
        hInnerSymmetric tau hlambda).comp
        ((G.admissibleRescaledDefectResolvent
            hInnerSymmetric tau hmu).comp
          (G.admissibleRescaledDefectResolvent
            hInnerSymmetric tau hnu)) =
      ContinuousLinearMap.threePointLagrangeCombination
        (G.admissibleRescaledDefectResolvent
          hInnerSymmetric tau hlambda)
        (G.admissibleRescaledDefectResolvent
          hInnerSymmetric tau hmu)
        (G.admissibleRescaledDefectResolvent
          hInnerSymmetric tau hnu)
        lambda mu nu := by
  apply
    ContinuousLinearMap.comp_comp_eq_threePointLagrangeCombination_of_resolvent_identities
      (lambda := lambda) (mu := mu) (nu := nu)
      (hlambdaMu := hlambdaMu) (hlambdaNu := hlambdaNu) (hmuNu := hmuNu)
  · exact
      G.admissibleRescaledDefectResolvent_identity
        T hInnerSymmetric tau hlambda hmu
  · exact
      G.admissibleRescaledDefectResolvent_identity
        T hInnerSymmetric tau hlambda hnu
  · exact
      G.admissibleRescaledDefectResolvent_identity
        T hInnerSymmetric tau hmu hnu

/-- The continuum product of three pairwise-distinct real resolvents is the
symmetric three-point Lagrange combination. -/
theorem VacuumSemigroupGapSlope.vacuumOrthogonalContinuumRealResolvent_comp_comp_eq_threePointLagrangeCombination
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda mu nu : ℝ}
    (hlambda : lambda < G.mass / 2)
    (hmu : mu < G.mass / 2)
    (hnu : nu < G.mass / 2)
    (hlambdaMu : lambda ≠ mu)
    (hlambdaNu : lambda ≠ nu)
    (hmuNu : mu ≠ nu) :
    (G.vacuumOrthogonalContinuumRealResolvent
        T hP hInnerSymmetric hSelf hlambda).comp
        ((G.vacuumOrthogonalContinuumRealResolvent
            T hP hInnerSymmetric hSelf hmu).comp
          (G.vacuumOrthogonalContinuumRealResolvent
            T hP hInnerSymmetric hSelf hnu)) =
      ContinuousLinearMap.threePointLagrangeCombination
        (G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf hlambda)
        (G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf hmu)
        (G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf hnu)
        lambda mu nu := by
  apply
    ContinuousLinearMap.comp_comp_eq_threePointLagrangeCombination_of_resolvent_identities
      (lambda := lambda) (mu := mu) (nu := nu)
      (hlambdaMu := hlambdaMu) (hlambdaNu := hlambdaNu) (hmuNu := hmuNu)
  · exact
      G.vacuumOrthogonalContinuumRealResolvent_identity
        T hP hInnerSymmetric hSelf hlambda hmu
  · exact
      G.vacuumOrthogonalContinuumRealResolvent_identity
        T hP hInnerSymmetric hSelf hlambda hnu
  · exact
      G.vacuumOrthogonalContinuumRealResolvent_identity
        T hP hInnerSymmetric hSelf hmu hnu

/-- The finite-time symmetric three-point Lagrange combinations converge
strongly to the continuum Lagrange combination. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolvent_threePointLagrangeCombination_tendsto_continuumThreePointLagrangeCombination
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda mu nu : ℝ}
    (hlambda : lambda < G.mass / 2)
    (hmu : mu < G.mass / 2)
    (hnu : nu < G.mass / 2)
    (y : P.VacuumOrthogonalHilbert) :
    Tendsto
      (fun tau : G.AdmissibleRescaledDefectTime =>
        ContinuousLinearMap.threePointLagrangeCombination
          (G.admissibleRescaledDefectResolvent
            hInnerSymmetric tau hlambda)
          (G.admissibleRescaledDefectResolvent
            hInnerSymmetric tau hmu)
          (G.admissibleRescaledDefectResolvent
            hInnerSymmetric tau hnu)
          lambda mu nu y)
      G.admissibleRescaledDefectTimeFilter
      (𝓝
        (ContinuousLinearMap.threePointLagrangeCombination
          (G.vacuumOrthogonalContinuumRealResolvent
            T hP hInnerSymmetric hSelf hlambda)
          (G.vacuumOrthogonalContinuumRealResolvent
            T hP hInnerSymmetric hSelf hmu)
          (G.vacuumOrthogonalContinuumRealResolvent
            T hP hInnerSymmetric hSelf hnu)
          lambda mu nu y)) := by
  have hLambda :=
    G.admissibleRescaledDefectResolvent_tendsto_continuumResolvent
      T hP hInnerSymmetric hSelf hlambda y
  have hMu :=
    G.admissibleRescaledDefectResolvent_tendsto_continuumResolvent
      T hP hInnerSymmetric hSelf hmu y
  have hNu :=
    G.admissibleRescaledDefectResolvent_tendsto_continuumResolvent
      T hP hInnerSymmetric hSelf hnu y
  have hLambdaWeighted :=
    hLambda.const_smul ((lambda - mu)⁻¹ * (lambda - nu)⁻¹)
  have hMuWeighted :=
    hMu.const_smul ((mu - lambda)⁻¹ * (mu - nu)⁻¹)
  have hNuWeighted :=
    hNu.const_smul ((nu - lambda)⁻¹ * (nu - mu)⁻¹)
  have hSum := (hLambdaWeighted.add hMuWeighted).add hNuWeighted
  simpa only [ContinuousLinearMap.threePointLagrangeCombination_apply] using hSum

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
