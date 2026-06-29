import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonUniformImplicitEulerOSBridgeL2
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSVacuumOrthogonalContinuousRealResolvent

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Set Filter Topology
open scoped InnerProductSpace LinearPMap

namespace ContinuousCompactOrientedGaugeWilsonUniformImplicitEulerOSBridge

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {D : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {P : D.OSPreHilbertData}
    {T : P.StronglyContinuousPhysicalSemigroup}
    {U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ℕ}

/-- The continuum uniform Dobrushin lower bound restricted to the complete
vacuum-orthogonal closed-Hamiltonian carrier. -/
theorem vacuumOrthogonalClosedRightHamiltonian_gap
    (B : ContinuousCompactOrientedGaugeWilsonUniformImplicitEulerOSBridge
      P T U)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    (x : (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf).domain) :
    continuousCompactOrientedUniformDobrushinGap U *
        ‖((x :
          T.vacuumOrthogonalClosedRightHamiltonianDomain) :
            P.VacuumOrthogonalHilbert)‖ ^ 2 ≤
      inner ℝ
        (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf x)
        ((x : T.vacuumOrthogonalClosedRightHamiltonianDomain) :
          P.VacuumOrthogonalHilbert) := by
  have hxOrthogonal :
      inner ℝ
          (((x : T.vacuumOrthogonalClosedRightHamiltonianDomain) :
            P.VacuumOrthogonalHilbert) : P.PhysicalHilbert)
          P.vacuum = 0 := by
    rw [real_inner_comm]
    exact (P.mem_vacuumOrthogonal_iff _).mp
      ((x : T.vacuumOrthogonalClosedRightHamiltonianDomain) :
        P.VacuumOrthogonalHilbert).property
  simpa only [
    PhysicalYangMillsGaugeInvariantOSReflectionData.OSPreHilbertData.StronglyContinuousPhysicalSemigroup.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint] using
    B.closedRightHamiltonian_inner_ge_uniformDobrushinGap_mul_norm_sq
      hP
      (T.vacuumOrthogonalAmbientDomainPoint
        (x : T.vacuumOrthogonalClosedRightHamiltonianDomain))
      hxOrthogonal

/-- The continuum excitation-sector resolvent below the uniform Dobrushin gap. -/
noncomputable def vacuumOrthogonalRealResolvent
    (B : ContinuousCompactOrientedGaugeWilsonUniformImplicitEulerOSBridge
      P T U)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda : lambda < continuousCompactOrientedUniformDobrushinGap U) :
    P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert :=
  LinearPMap.realResolvent
    (A := T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf)
    (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint_isSelfAdjoint
      hP hSelf)
    hlambda
    (B.vacuumOrthogonalClosedRightHamiltonian_gap hP hSelf)

/-- Pointwise continuum excitation resolvent estimate. -/
theorem vacuumOrthogonalRealResolvent_norm_bound
    (B : ContinuousCompactOrientedGaugeWilsonUniformImplicitEulerOSBridge
      P T U)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda : lambda < continuousCompactOrientedUniformDobrushinGap U)
    (y : P.VacuumOrthogonalHilbert) :
    ‖B.vacuumOrthogonalRealResolvent hP hSelf hlambda y‖ ≤
      (continuousCompactOrientedUniformDobrushinGap U - lambda)⁻¹ * ‖y‖ := by
  exact LinearPMap.realResolventLinearMap_norm_bound
    (A := T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf)
    (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint_isSelfAdjoint
      hP hSelf)
    hlambda
    (B.vacuumOrthogonalClosedRightHamiltonian_gap hP hSelf)
    y

/-- Operator-norm bound for the continuum excitation resolvent. -/
theorem vacuumOrthogonalRealResolvent_norm_le
    (B : ContinuousCompactOrientedGaugeWilsonUniformImplicitEulerOSBridge
      P T U)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda : lambda < continuousCompactOrientedUniformDobrushinGap U) :
    ‖B.vacuumOrthogonalRealResolvent hP hSelf hlambda‖ ≤
      (continuousCompactOrientedUniformDobrushinGap U - lambda)⁻¹ := by
  exact LinearPMap.realResolvent_norm_le
    (A := T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf)
    (T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint_isSelfAdjoint
      hP hSelf)
    hlambda
    (B.vacuumOrthogonalClosedRightHamiltonian_gap hP hSelf)

/-- Every real shift below the uniform Dobrushin gap is bijective on the
continuum excitation sector. -/
theorem vacuumOrthogonalRealShift_bijective
    (B : ContinuousCompactOrientedGaugeWilsonUniformImplicitEulerOSBridge
      P T U)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda : lambda < continuousCompactOrientedUniformDobrushinGap U) :
    Function.Bijective
      (T.vacuumOrthogonalClosedRightHamiltonianRealShift hSelf lambda) := by
  apply LinearPMap.realShift_bijective
    (A := T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint hSelf)
    (hSelf :=
      T.vacuumOrthogonalClosedRightHamiltonianOfSelfAdjoint_isSelfAdjoint
        hP hSelf)
    hlambda
  exact B.vacuumOrthogonalClosedRightHamiltonian_gap hP hSelf

/-- Complete continuum real-gap package transported from the uniform compact
Wilson implicit-Euler family. -/
theorem vacuumOrthogonalContinuousRealResolvent_package
    (B : ContinuousCompactOrientedGaugeWilsonUniformImplicitEulerOSBridge
      P T U)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda : lambda < continuousCompactOrientedUniformDobrushinGap U) :
    (∃ R : P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert,
        R = B.vacuumOrthogonalRealResolvent hP hSelf hlambda ∧
        ‖R‖ ≤
          (continuousCompactOrientedUniformDobrushinGap U - lambda)⁻¹) ∧
      Function.Bijective
        (T.vacuumOrthogonalClosedRightHamiltonianRealShift hSelf lambda) :=
  ⟨⟨B.vacuumOrthogonalRealResolvent hP hSelf hlambda, rfl,
      B.vacuumOrthogonalRealResolvent_norm_le hP hSelf hlambda⟩,
    B.vacuumOrthogonalRealShift_bijective hP hSelf hlambda⟩

end ContinuousCompactOrientedGaugeWilsonUniformImplicitEulerOSBridge

end

end MathlibAnalytic
end MGAP4D
