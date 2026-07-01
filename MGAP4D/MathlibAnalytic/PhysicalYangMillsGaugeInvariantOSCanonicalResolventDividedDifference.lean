import MGAP4D.MathlibAnalytic.ContinuousLinearMapResolventDividedDifference
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSFullStrongResolvent

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

/-- At each admissible positive time, the product of two distinct real
resolvents is their two-point divided difference. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolvent_comp_eq_inv_smul_sub
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    {lambda mu : ℝ}
    (hlambda : lambda < G.mass / 2)
    (hmu : mu < G.mass / 2)
    (hne : lambda ≠ mu) :
    (G.admissibleRescaledDefectResolvent
        hInnerSymmetric tau hlambda).comp
        (G.admissibleRescaledDefectResolvent
          hInnerSymmetric tau hmu) =
      (lambda - mu)⁻¹ •
        (G.admissibleRescaledDefectResolvent hInnerSymmetric tau hlambda -
          G.admissibleRescaledDefectResolvent hInnerSymmetric tau hmu) := by
  apply ContinuousLinearMap.comp_eq_inv_smul_sub_of_resolvent_identity_of_ne
    (lambda := lambda) (mu := mu) (hne := hne)
  exact
    G.admissibleRescaledDefectResolvent_identity
      T hInnerSymmetric tau hlambda hmu

/-- Pointwise finite-time form of the two-point resolvent divided difference. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolvent_comp_apply_eq_inv_smul_sub_apply
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    {lambda mu : ℝ}
    (hlambda : lambda < G.mass / 2)
    (hmu : mu < G.mass / 2)
    (hne : lambda ≠ mu)
    (y : P.VacuumOrthogonalHilbert) :
    G.admissibleRescaledDefectResolvent hInnerSymmetric tau hlambda
        (G.admissibleRescaledDefectResolvent hInnerSymmetric tau hmu y) =
      (lambda - mu)⁻¹ •
        (G.admissibleRescaledDefectResolvent hInnerSymmetric tau hlambda y -
          G.admissibleRescaledDefectResolvent hInnerSymmetric tau hmu y) := by
  exact
    ContinuousLinearMap.comp_apply_eq_inv_smul_sub_apply_of_resolvent_identity_of_ne
      (G.admissibleRescaledDefectResolvent hInnerSymmetric tau hlambda)
      (G.admissibleRescaledDefectResolvent hInnerSymmetric tau hmu)
      lambda mu hne
      (G.admissibleRescaledDefectResolvent_identity
        T hInnerSymmetric tau hlambda hmu)
      y

/-- The product of two distinct continuum excitation-Hamiltonian resolvents is
their two-point divided difference. -/
theorem VacuumSemigroupGapSlope.vacuumOrthogonalContinuumRealResolvent_comp_eq_inv_smul_sub
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda mu : ℝ}
    (hlambda : lambda < G.mass / 2)
    (hmu : mu < G.mass / 2)
    (hne : lambda ≠ mu) :
    (G.vacuumOrthogonalContinuumRealResolvent
        T hP hInnerSymmetric hSelf hlambda).comp
        (G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf hmu) =
      (lambda - mu)⁻¹ •
        (G.vacuumOrthogonalContinuumRealResolvent
            T hP hInnerSymmetric hSelf hlambda -
          G.vacuumOrthogonalContinuumRealResolvent
            T hP hInnerSymmetric hSelf hmu) := by
  apply ContinuousLinearMap.comp_eq_inv_smul_sub_of_resolvent_identity_of_ne
    (lambda := lambda) (mu := mu) (hne := hne)
  exact
    G.vacuumOrthogonalContinuumRealResolvent_identity
      T hP hInnerSymmetric hSelf hlambda hmu

/-- Pointwise continuum form of the two-point resolvent divided difference. -/
theorem VacuumSemigroupGapSlope.vacuumOrthogonalContinuumRealResolvent_comp_apply_eq_inv_smul_sub_apply
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda mu : ℝ}
    (hlambda : lambda < G.mass / 2)
    (hmu : mu < G.mass / 2)
    (hne : lambda ≠ mu)
    (y : P.VacuumOrthogonalHilbert) :
    G.vacuumOrthogonalContinuumRealResolvent
        T hP hInnerSymmetric hSelf hlambda
        (G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf hmu y) =
      (lambda - mu)⁻¹ •
        (G.vacuumOrthogonalContinuumRealResolvent
            T hP hInnerSymmetric hSelf hlambda y -
          G.vacuumOrthogonalContinuumRealResolvent
            T hP hInnerSymmetric hSelf hmu y) := by
  exact
    ContinuousLinearMap.comp_apply_eq_inv_smul_sub_apply_of_resolvent_identity_of_ne
      (G.vacuumOrthogonalContinuumRealResolvent
        T hP hInnerSymmetric hSelf hlambda)
      (G.vacuumOrthogonalContinuumRealResolvent
        T hP hInnerSymmetric hSelf hmu)
      lambda mu hne
      (G.vacuumOrthogonalContinuumRealResolvent_identity
        T hP hInnerSymmetric hSelf hlambda hmu)
      y

/-- Two-point divided differences of the finite-time resolvents converge
strongly to the corresponding continuum divided difference. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolvent_dividedDifference_tendsto_continuumDividedDifference
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda mu : ℝ}
    (hlambda : lambda < G.mass / 2)
    (hmu : mu < G.mass / 2)
    (y : P.VacuumOrthogonalHilbert) :
    Tendsto
      (fun tau : G.AdmissibleRescaledDefectTime =>
        (lambda - mu)⁻¹ •
          (G.admissibleRescaledDefectResolvent
              hInnerSymmetric tau hlambda y -
            G.admissibleRescaledDefectResolvent
              hInnerSymmetric tau hmu y))
      G.admissibleRescaledDefectTimeFilter
      (𝓝
        ((lambda - mu)⁻¹ •
          (G.vacuumOrthogonalContinuumRealResolvent
              T hP hInnerSymmetric hSelf hlambda y -
            G.vacuumOrthogonalContinuumRealResolvent
              T hP hInnerSymmetric hSelf hmu y))) := by
  have hLambda :=
    G.admissibleRescaledDefectResolvent_tendsto_continuumResolvent
      T hP hInnerSymmetric hSelf hlambda y
  have hMu :=
    G.admissibleRescaledDefectResolvent_tendsto_continuumResolvent
      T hP hInnerSymmetric hSelf hmu y
  exact (hLambda.sub hMu).const_smul (lambda - mu)⁻¹

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
