import MGAP4D.MathlibAnalytic.ContinuousLinearMapResolventThreePointDividedDifference
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSCanonicalResolventDividedDifference

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
real resolvents is the corresponding nested three-point divided difference. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolvent_comp_comp_eq_threePointDividedDifference
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
      ContinuousLinearMap.threePointDividedDifference
        (G.admissibleRescaledDefectResolvent
          hInnerSymmetric tau hlambda)
        (G.admissibleRescaledDefectResolvent
          hInnerSymmetric tau hmu)
        (G.admissibleRescaledDefectResolvent
          hInnerSymmetric tau hnu)
        lambda mu nu := by
  apply
    ContinuousLinearMap.comp_comp_eq_threePointDividedDifference_of_resolvent_identities
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
corresponding nested three-point divided difference. -/
theorem VacuumSemigroupGapSlope.vacuumOrthogonalContinuumRealResolvent_comp_comp_eq_threePointDividedDifference
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
      ContinuousLinearMap.threePointDividedDifference
        (G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf hlambda)
        (G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf hmu)
        (G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf hnu)
        lambda mu nu := by
  apply
    ContinuousLinearMap.comp_comp_eq_threePointDividedDifference_of_resolvent_identities
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

/-- Three-point divided differences of finite-time resolvents converge strongly
to the corresponding continuum three-point divided difference. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolvent_threePointDividedDifference_tendsto_continuumThreePointDividedDifference
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
        ContinuousLinearMap.threePointDividedDifference
          (G.admissibleRescaledDefectResolvent
            hInnerSymmetric tau hlambda)
          (G.admissibleRescaledDefectResolvent
            hInnerSymmetric tau hmu)
          (G.admissibleRescaledDefectResolvent
            hInnerSymmetric tau hnu)
          lambda mu nu y)
      G.admissibleRescaledDefectTimeFilter
      (𝓝
        (ContinuousLinearMap.threePointDividedDifference
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
  have hLambdaNu :=
    (hLambda.sub hNu).const_smul (lambda - nu)⁻¹
  have hMuNu :=
    (hMu.sub hNu).const_smul (mu - nu)⁻¹
  have hOuter :=
    (hLambdaNu.sub hMuNu).const_smul (lambda - mu)⁻¹
  simpa only [ContinuousLinearMap.threePointDividedDifference_apply] using hOuter

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
