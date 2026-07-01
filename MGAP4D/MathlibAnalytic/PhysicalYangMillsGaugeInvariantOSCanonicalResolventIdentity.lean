import MGAP4D.MathlibAnalytic.RealHilbertUniformCoerciveSymmetricStrongLimitResolventIdentity
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalRealResolventIdentity
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSFullStrongResolvent
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter Set Topology
open scoped InnerProductSpace LinearPMap

namespace ContinuousLinearMap

variable {E : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Two opposite-order resolvent identities force the corresponding bounded
operator products to commute. -/
theorem comp_comm_of_resolvent_identities
    (Rlambda Rmu : E →L[ℝ] E)
    (lambda mu : ℝ)
    (hLambdaMu :
      Rlambda - Rmu =
        (lambda - mu) • (Rlambda.comp Rmu))
    (hMuLambda :
      Rmu - Rlambda =
        (mu - lambda) • (Rmu.comp Rlambda)) :
    Rlambda.comp Rmu = Rmu.comp Rlambda := by
  by_cases hEq : lambda = mu
  · subst mu
    simpa using hLambdaMu
  have hScale :
      (lambda - mu) • (Rlambda.comp Rmu) =
        (lambda - mu) • (Rmu.comp Rlambda) := by
    calc
      (lambda - mu) • (Rlambda.comp Rmu) = Rlambda - Rmu :=
        hLambdaMu.symm
      _ = -(Rmu - Rlambda) := by abel
      _ = -((mu - lambda) • (Rmu.comp Rlambda)) := by
        rw [hMuLambda]
      _ = (lambda - mu) • (Rmu.comp Rlambda) := by module
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  have hScaledZero :
      (lambda - mu) •
          ((Rlambda.comp Rmu) - (Rmu.comp Rlambda)) = 0 := by
    rw [smul_sub]
    exact sub_eq_zero.mpr hScale
  have hNormZero :
      ‖(lambda - mu) •
          ((Rlambda.comp Rmu) - (Rmu.comp Rlambda))‖ = 0 := by
    rw [hScaledZero, norm_zero]
  rw [norm_smul, Real.norm_eq_abs] at hNormZero
  have hScalar : |lambda - mu| ≠ 0 :=
    abs_ne_zero.mpr (sub_ne_zero.mpr hEq)
  exact (mul_eq_zero.mp hNormZero).resolve_left hScalar

end ContinuousLinearMap

namespace PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : D.OSPreHilbertData}

namespace StronglyContinuousPhysicalSemigroup

/-- The bounded rescaled-defect resolvents satisfy the real resolvent identity
at every admissible positive time. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolvent_identity
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    {lambda mu : ℝ}
    (hlambda : lambda < G.mass / 2)
    (hmu : mu < G.mass / 2) :
    G.admissibleRescaledDefectResolvent hInnerSymmetric tau hlambda -
        G.admissibleRescaledDefectResolvent hInnerSymmetric tau hmu =
      (lambda - mu) •
        ((G.admissibleRescaledDefectResolvent
            hInnerSymmetric tau hlambda).comp
          (G.admissibleRescaledDefectResolvent
            hInnerSymmetric tau hmu)) := by
  exact
    realHilbert_uniformCoerciveSymmetricStrongLimit_limitResolvent_identity
      (G.admissibleRescaledDefectData hInnerSymmetric tau)
      hlambda hmu

/-- Rescaled-defect resolvents at different below-half-mass real shifts commute
at each admissible positive time. -/
theorem VacuumSemigroupGapSlope.admissibleRescaledDefectResolvent_comp_comm
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (tau : G.AdmissibleRescaledDefectTime)
    {lambda mu : ℝ}
    (hlambda : lambda < G.mass / 2)
    (hmu : mu < G.mass / 2) :
    (G.admissibleRescaledDefectResolvent
        hInnerSymmetric tau hlambda).comp
        (G.admissibleRescaledDefectResolvent
          hInnerSymmetric tau hmu) =
      (G.admissibleRescaledDefectResolvent
        hInnerSymmetric tau hmu).comp
        (G.admissibleRescaledDefectResolvent
          hInnerSymmetric tau hlambda) := by
  exact
    realHilbert_uniformCoerciveSymmetricStrongLimit_limitResolvent_comp_comm
      (G.admissibleRescaledDefectData hInnerSymmetric tau)
      hlambda hmu

/-- The continuum excitation-Hamiltonian resolvents satisfy the real resolvent
identity under the common half-mass normalization. -/
theorem VacuumSemigroupGapSlope.vacuumOrthogonalContinuumRealResolvent_identity
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda mu : ℝ}
    (hlambda : lambda < G.mass / 2)
    (hmu : mu < G.mass / 2) :
    G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf hlambda -
        G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf hmu =
      (lambda - mu) •
        ((G.vacuumOrthogonalContinuumRealResolvent
            T hP hInnerSymmetric hSelf hlambda).comp
          (G.vacuumOrthogonalContinuumRealResolvent
            T hP hInnerSymmetric hSelf hmu)) := by
  apply LinearPMap.realResolvent_sub_eq_smul_comp
    (A := T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf)
    (hSelf :=
      T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint_isSelfAdjoint
        hP hSelf)
    hlambda hmu
  exact
    G.vacuumOrthogonalClosedRightHamiltonian_halfGap
      T hP hInnerSymmetric hSelf

/-- Continuum excitation-Hamiltonian resolvents commute at all real shifts
below the common half-mass threshold. -/
theorem VacuumSemigroupGapSlope.vacuumOrthogonalContinuumRealResolvent_comp_comm
    (T : P.StronglyContinuousPhysicalSemigroup)
    (G : T.VacuumSemigroupGapSlope)
    (hP : P.IsNormalized)
    (hInnerSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda mu : ℝ}
    (hlambda : lambda < G.mass / 2)
    (hmu : mu < G.mass / 2) :
    (G.vacuumOrthogonalContinuumRealResolvent
        T hP hInnerSymmetric hSelf hlambda).comp
        (G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf hmu) =
      (G.vacuumOrthogonalContinuumRealResolvent
        T hP hInnerSymmetric hSelf hmu).comp
        (G.vacuumOrthogonalContinuumRealResolvent
          T hP hInnerSymmetric hSelf hlambda) := by
  apply ContinuousLinearMap.comp_comm_of_resolvent_identities
    (lambda := lambda) (mu := mu)
  · exact
      G.vacuumOrthogonalContinuumRealResolvent_identity
        T hP hInnerSymmetric hSelf hlambda hmu
  · exact
      G.vacuumOrthogonalContinuumRealResolvent_identity
        T hP hInnerSymmetric hSelf hmu hlambda

end StronglyContinuousPhysicalSemigroup
end PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData

end

end MathlibAnalytic
end MGAP4D
