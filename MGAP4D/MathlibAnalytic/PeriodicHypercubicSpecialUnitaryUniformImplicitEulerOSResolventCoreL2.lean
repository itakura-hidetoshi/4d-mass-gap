import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryUniformImplicitEulerOSGapL2
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonUniformImplicitEulerOSRealResolventL2

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

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

noncomputable def periodicVacuumOrthogonalRealResolvent
    (D : PeriodicHypercubicSpecialUnitaryUniformDobrushinFamilyData
      sideLength sideLength_pos N hN beta beta_nonneg)
    (B : D.UniformImplicitEulerOSBridge)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda : lambda < 1 - D.coefficientBound) :
    P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert :=
  B.vacuumOrthogonalRealResolvent hP hSelf (by
    simpa only [toUniformFamily_gap] using hlambda)

theorem periodicVacuumOrthogonalRealResolvent_norm_le
    (D : PeriodicHypercubicSpecialUnitaryUniformDobrushinFamilyData
      sideLength sideLength_pos N hN beta beta_nonneg)
    (B : D.UniformImplicitEulerOSBridge)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda : lambda < 1 - D.coefficientBound) :
    ‖D.periodicVacuumOrthogonalRealResolvent B hP hSelf hlambda‖ ≤
      (1 - D.coefficientBound - lambda)⁻¹ := by
  unfold periodicVacuumOrthogonalRealResolvent
  simpa only [toUniformFamily_gap] using
    B.vacuumOrthogonalRealResolvent_norm_le hP hSelf
      (by simpa only [toUniformFamily_gap] using hlambda)

end PeriodicHypercubicSpecialUnitaryUniformDobrushinFamilyData

end

end MathlibAnalytic
end MGAP4D
