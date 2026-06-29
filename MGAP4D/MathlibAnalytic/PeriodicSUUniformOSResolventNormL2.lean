import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryUniformImplicitEulerOSResolventDefinitionL2

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

theorem periodicVacuumOrthogonalRealResolvent_norm_le
    (D : PeriodicHypercubicSpecialUnitaryUniformDobrushinFamilyData
      sideLength sideLength_pos N hN beta beta_nonneg)
    (B : D.UniformImplicitEulerOSBridge P T)
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
