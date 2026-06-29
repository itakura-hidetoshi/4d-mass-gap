import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryUniformImplicitEulerOSResolventCoreL2

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped LinearPMap

namespace PeriodicHypercubicSpecialUnitaryUniformDobrushinFamilyData

variable
    {sideLength : ℕ → ℕ}
    {sideLength_pos : ∀ n, 0 < sideLength n}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {beta_nonneg : ∀ n, 0 ≤ beta n}

variable
    {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
    {W : PhysicalYangMillsGaugeInvariantOSReflectionData S}
    {P : W.OSPreHilbertData}
    {T : P.StronglyContinuousPhysicalSemigroup}

theorem periodicVacuumOrthogonalContinuousRealResolvent_package
    (D : PeriodicHypercubicSpecialUnitaryUniformDobrushinFamilyData
      sideLength sideLength_pos N hN beta beta_nonneg)
    (B : D.UniformImplicitEulerOSBridge)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda : lambda < 1 - D.coefficientBound) :
    (∃ R : P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert,
        R = D.periodicVacuumOrthogonalRealResolvent B hP hSelf hlambda ∧
        ‖R‖ ≤ (1 - D.coefficientBound - lambda)⁻¹) ∧
      Function.Bijective
        (T.vacuumOrthogonalClosedRightHamiltonianRealShift hSelf lambda) := by
  have hbelow :
      lambda < continuousCompactOrientedUniformDobrushinGap D.toUniformFamily := by
    simpa only [toUniformFamily_gap] using hlambda
  rcases B.vacuumOrthogonalContinuousRealResolvent_package hP hSelf hbelow with
    ⟨⟨R, hR, hnorm⟩, hbij⟩
  refine ⟨⟨R, ?_, ?_⟩, hbij⟩
  · simpa only [periodicVacuumOrthogonalRealResolvent] using hR
  · simpa only [toUniformFamily_gap] using hnorm

end PeriodicHypercubicSpecialUnitaryUniformDobrushinFamilyData

end

end MathlibAnalytic
end MGAP4D
