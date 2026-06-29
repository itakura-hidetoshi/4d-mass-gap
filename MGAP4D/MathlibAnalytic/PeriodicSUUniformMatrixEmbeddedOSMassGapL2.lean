import MGAP4D.MathlibAnalytic.PeriodicSUUniformMatrixOSMassGapL2
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonUniformImplicitEulerEmbeddedOSBridgeL2

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

namespace PeriodicHypercubicSpecialUnitaryUniformDobrushinMatrixFamilyData

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

/-- The common-carrier vector convergence bridge for a periodic `SU(N)`
matrix-plus-Rayleigh Dobrushin family. -/
abbrev EmbeddedUniformImplicitEulerOSBridge
    (M : PeriodicHypercubicSpecialUnitaryUniformDobrushinMatrixFamilyData
      sideLength sideLength_pos N hN beta beta_nonneg)
    (P : W.OSPreHilbertData)
    (T : P.StronglyContinuousPhysicalSemigroup) :=
  ContinuousCompactOrientedGaugeWilsonUniformImplicitEulerEmbeddedOSBridge
    P T M.toUniformDobrushinFamilyData.toUniformFamily

/-- End-to-end continuum excitation real-gap package from periodic `SU(N)`
matrix-plus-Rayleigh data and isometrically embedded implicit-Euler trajectory
convergence. -/
theorem periodicVacuumOrthogonalMassGap_package_of_embedded_innerSymmetric
    (M : PeriodicHypercubicSpecialUnitaryUniformDobrushinMatrixFamilyData
      sideLength sideLength_pos N hN beta beta_nonneg)
    (B : M.EmbeddedUniformImplicitEulerOSBridge P T)
    (hP : P.IsNormalized)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {lambda : ℝ}
    (hlambda : lambda < 1 - M.coefficientBound) :
    ∃ hSelf : IsSelfAdjoint T.closedRightHamiltonian,
      (∃ R : P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert,
          R = M.toUniformDobrushinFamilyData.periodicVacuumOrthogonalRealResolvent
            B.toUniformImplicitEulerOSBridge hP hSelf hlambda ∧
          ‖R‖ ≤ (1 - M.coefficientBound - lambda)⁻¹) ∧
        Function.Bijective
          (T.vacuumOrthogonalClosedRightHamiltonianRealShift hSelf lambda) := by
  exact M.periodicVacuumOrthogonalMassGap_package_of_innerSymmetric
    B.toUniformImplicitEulerOSBridge hP hSymmetric hlambda

/-- The common-carrier periodic construction gives the graph-closed continuum
Hamiltonian lower bound before invoking self-adjoint spectral calculus. -/
theorem closedRightHamiltonian_inner_ge_uniformGap_mul_norm_sq_of_embedded
    (M : PeriodicHypercubicSpecialUnitaryUniformDobrushinMatrixFamilyData
      sideLength sideLength_pos N hN beta beta_nonneg)
    (B : M.EmbeddedUniformImplicitEulerOSBridge P T)
    (hP : P.IsNormalized)
    (psi : T.closedRightHamiltonian.domain)
    (hpsi : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    (1 - M.coefficientBound) * ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ (T.closedRightHamiltonian psi)
        (psi : P.PhysicalHilbert) := by
  simpa using
    B.closedRightHamiltonian_inner_ge_uniformDobrushinGap_mul_norm_sq
      hP psi hpsi

end PeriodicHypercubicSpecialUnitaryUniformDobrushinMatrixFamilyData

end

end MathlibAnalytic
end MGAP4D
