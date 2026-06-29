import MGAP4D.MathlibAnalytic.PeriodicSUUniformDobrushinMatrixFamilyL2
import MGAP4D.MathlibAnalytic.PeriodicSUUniformOSMassGapPackageL2

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

/-- The OS implicit-Euler convergence bridge associated with a periodic
matrix-plus-Rayleigh Dobrushin family. -/
abbrev UniformImplicitEulerOSBridge
    (M : PeriodicHypercubicSpecialUnitaryUniformDobrushinMatrixFamilyData
      sideLength sideLength_pos N hN beta beta_nonneg)
    (P : W.OSPreHilbertData)
    (T : P.StronglyContinuousPhysicalSemigroup) :=
  M.toUniformDobrushinFamilyData.UniformImplicitEulerOSBridge P T

/-- End-to-end continuum excitation mass-gap package obtained from periodic
four-dimensional `SU(N)` matrix-plus-Rayleigh Dobrushin data, the two OS norm
convergence statements, normalized vacuum, and symmetry of the completed
Euclidean-time semigroup. -/
theorem periodicVacuumOrthogonalMassGap_package_of_innerSymmetric
    (M : PeriodicHypercubicSpecialUnitaryUniformDobrushinMatrixFamilyData
      sideLength sideLength_pos N hN beta beta_nonneg)
    (B : M.UniformImplicitEulerOSBridge P T)
    (hP : P.IsNormalized)
    (hSymmetric : T.toPhysicalSemigroup.IsInnerSymmetric)
    {lambda : ℝ}
    (hlambda : lambda < 1 - M.coefficientBound) :
    ∃ hSelf : IsSelfAdjoint T.closedRightHamiltonian,
      (∃ R : P.VacuumOrthogonalHilbert →L[ℝ] P.VacuumOrthogonalHilbert,
          R = M.toUniformDobrushinFamilyData.periodicVacuumOrthogonalRealResolvent
            B hP hSelf hlambda ∧
          ‖R‖ ≤ (1 - M.coefficientBound - lambda)⁻¹) ∧
        Function.Bijective
          (T.vacuumOrthogonalClosedRightHamiltonianRealShift hSelf lambda) := by
  simpa using
    M.toUniformDobrushinFamilyData.
      periodicVacuumOrthogonalMassGap_package_of_innerSymmetric
        B hP hSymmetric hlambda

/-- The same hypotheses yield the graph-closed continuum Hamiltonian lower
bound with mass `1 - coefficientBound`. -/
theorem closedRightHamiltonian_inner_ge_uniformGap_mul_norm_sq
    (M : PeriodicHypercubicSpecialUnitaryUniformDobrushinMatrixFamilyData
      sideLength sideLength_pos N hN beta beta_nonneg)
    (B : M.UniformImplicitEulerOSBridge P T)
    (hP : P.IsNormalized)
    (psi : T.closedRightHamiltonian.domain)
    (hpsi : inner ℝ (psi : P.PhysicalHilbert) P.vacuum = 0) :
    (1 - M.coefficientBound) * ‖(psi : P.PhysicalHilbert)‖ ^ 2 ≤
      inner ℝ (T.closedRightHamiltonian psi)
        (psi : P.PhysicalHilbert) := by
  simpa using
    M.toUniformDobrushinFamilyData.
      closedRightHamiltonian_inner_ge_uniformGap_mul_norm_sq
        B hP psi hpsi

end PeriodicHypercubicSpecialUnitaryUniformDobrushinMatrixFamilyData

end

end MathlibAnalytic
end MGAP4D
