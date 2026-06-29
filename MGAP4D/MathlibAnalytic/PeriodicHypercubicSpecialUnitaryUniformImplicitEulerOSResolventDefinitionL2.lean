import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryUniformImplicitEulerOSGapL2
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonUniformImplicitEulerOSRealResolventL2

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace PeriodicHypercubicSpecialUnitaryUniformDobrushinFamilyData

variable {sideLength : ℕ → ℕ} {sideLength_pos : ∀ n, 0 < sideLength n}
variable {N : ℕ} {hN : 0 < N}
variable [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
variable {beta : ℕ → ℝ} {beta_nonneg : ∀ n, 0 ≤ beta n}
variable {S : PhysicalFourDimensionalYangMillsSymmetryLimit}
variable {W : PhysicalYangMillsGaugeInvariantOSReflectionData S}
variable {P : W.OSPreHilbertData}
variable {T : P.StronglyContinuousPhysicalSemigroup}

noncomputable def periodicVacuumOrthogonalRealResolvent
    (D : PeriodicHypercubicSpecialUnitaryUniformDobrushinFamilyData
      sideLength sideLength_pos N hN beta beta_nonneg)
    (B : D.UniformImplicitEulerOSBridge P T)
    (hP : P.IsNormalized)
    (hSelf : IsSelfAdjoint T.closedRightHamiltonian)
    {lambda : ℝ}
    (hlambda : lambda < 1 - D.coefficientBound) :
    P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert :=
  B.vacuumOrthogonalRealResolvent hP hSelf (by
    simpa only [toUniformFamily_gap] using hlambda)

end PeriodicHypercubicSpecialUnitaryUniformDobrushinFamilyData

end

end MathlibAnalytic
end MGAP4D
