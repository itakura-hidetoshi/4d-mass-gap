import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryUniformImplicitEulerOSResolventPackageL2
import MGAP4D.MathlibAnalytic.PhysicalYangMillsGaugeInvariantOSSemigroupSymmetry

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

theorem periodicVacuumOrthogonalMassGap_package_of_innerSymmetric
    (D : PeriodicHypercubicSpecialUnitaryUniformDobrushinFamilyData
      sideLength sideLength_pos N hN beta beta_nonneg)
    (B : D.UniformImplicitEulerOSBridge P T)
    (hP : P.IsNormalized)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {lambda : ℝ}
    (hlambda : lambda < 1 - D.coefficientBound) :
    ∃ hSelf : IsSelfAdjoint T.closedRightHamiltonian,
      (∃ R : P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert,
          R = D.periodicVacuumOrthogonalRealResolvent B hP hSelf hlambda ∧
          ‖R‖ ≤ (1 - D.coefficientBound - lambda)⁻¹) ∧
        Function.Bijective
          (T.vacuumOrthogonalClosedRightHamiltonianRealShift hSelf lambda) := by
  let hSelf : IsSelfAdjoint T.closedRightHamiltonian :=
    T.closedRightHamiltonian_isSelfAdjoint_of_innerSymmetric hSymmetric
  exact ⟨hSelf,
    D.periodicVacuumOrthogonalContinuousRealResolvent_package
      B hP hSelf hlambda⟩

end PeriodicHypercubicSpecialUnitaryUniformDobrushinFamilyData

end

end MathlibAnalytic
end MGAP4D
