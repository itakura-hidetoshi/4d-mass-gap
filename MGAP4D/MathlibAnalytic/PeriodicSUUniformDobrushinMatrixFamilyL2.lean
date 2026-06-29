import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryUniformDobrushinFamilyL2
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonDobrushinMatrixL2

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A scale-dependent periodic four-dimensional `SU(N)` Wilson family carrying
both proof-relevant Dobrushin matrices and the centered random-scan `L²`
comparison, together with one volume-independent coefficient bound. -/
structure PeriodicHypercubicSpecialUnitaryUniformDobrushinMatrixFamilyData
    (sideLength : ℕ → ℕ)
    (sideLength_pos : ∀ n, 0 < sideLength n)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (beta_nonneg : ∀ n, 0 ≤ beta n) where
  certificate : ∀ n,
    ContinuousCompactOrientedGaugeWilsonDobrushinMatrixRandomScanCertificate
      (periodicHypercubicSpecialUnitaryWilsonSystemOfPositiveSide
        (sideLength n) N (sideLength_pos n) hN
        (beta n) (beta_nonneg n))
  coefficientBound : ℝ
  coefficientBound_nonneg : 0 ≤ coefficientBound
  coefficientBound_lt_one : coefficientBound < 1
  coefficient_le : ∀ n, (certificate n).coefficient ≤ coefficientBound

namespace PeriodicHypercubicSpecialUnitaryUniformDobrushinMatrixFamilyData

variable
    {sideLength : ℕ → ℕ}
    {sideLength_pos : ∀ n, 0 < sideLength n}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {beta_nonneg : ∀ n, 0 ≤ beta n}

/-- Forgetting the bounded-test matrix layer yields the periodic uniform
Rayleigh family used by the finite-volume and OS mass-gap bridges. -/
noncomputable def toUniformDobrushinFamilyData
    (M : PeriodicHypercubicSpecialUnitaryUniformDobrushinMatrixFamilyData
      sideLength sideLength_pos N hN beta beta_nonneg) :
    PeriodicHypercubicSpecialUnitaryUniformDobrushinFamilyData
      sideLength sideLength_pos N hN beta beta_nonneg where
  certificate := fun n => (M.certificate n).toRandomScanCertificate
  coefficientBound := M.coefficientBound
  coefficientBound_nonneg := M.coefficientBound_nonneg
  coefficientBound_lt_one := M.coefficientBound_lt_one
  coefficient_le := by
    intro n
    exact M.coefficient_le n

@[simp] theorem toUniformDobrushinFamilyData_coefficientBound
    (M : PeriodicHypercubicSpecialUnitaryUniformDobrushinMatrixFamilyData
      sideLength sideLength_pos N hN beta beta_nonneg) :
    M.toUniformDobrushinFamilyData.coefficientBound = M.coefficientBound :=
  rfl

@[simp] theorem toUniformDobrushinFamilyData_certificate_coefficient
    (M : PeriodicHypercubicSpecialUnitaryUniformDobrushinMatrixFamilyData
      sideLength sideLength_pos N hN beta beta_nonneg)
    (n : ℕ) :
    (M.toUniformDobrushinFamilyData.certificate n).coefficient =
      (M.certificate n).coefficient :=
  rfl

/-- Every finite periodic `SU(N)` excitation Hamiltonian inherits the common
matrix-family gap. -/
theorem restrictedEnergy_gap
    (M : PeriodicHypercubicSpecialUnitaryUniformDobrushinMatrixFamilyData
      sideLength sideLength_pos N hN beta beta_nonneg)
    (n : ℕ)
    (f : (M.toUniformDobrushinFamilyData.toUniformFamily.system n).VacuumOrthogonalL2) :
    (1 - M.coefficientBound) * ‖f‖ ^ 2 ≤
      inner ℝ
        ((M.toUniformDobrushinFamilyData.toUniformFamily.system n).
          heatBathHamiltonianVacuumOrthogonalL2 f)
        f := by
  simpa using
    M.toUniformDobrushinFamilyData.restrictedEnergy_gap n f

/-- Uniform finite-volume real-resolvent package derived from the
matrix-plus-Rayleigh family. -/
theorem realGap_package
    (M : PeriodicHypercubicSpecialUnitaryUniformDobrushinMatrixFamilyData
      sideLength sideLength_pos N hN beta beta_nonneg)
    {lambda : ℝ}
    (hlambda : lambda < 1 - M.coefficientBound) :
    ∀ n : ℕ,
      ∃ R :
          (M.toUniformDobrushinFamilyData.toUniformFamily.system n).
              VacuumOrthogonalL2 →L[ℝ]
            (M.toUniformDobrushinFamilyData.toUniformFamily.system n).
              VacuumOrthogonalL2,
        (∀ y,
          (M.toUniformDobrushinFamilyData.toUniformFamily.system n).
              restrictedEnergyShiftL2 lambda (R y) = y) ∧
        (∀ f,
          R ((M.toUniformDobrushinFamilyData.toUniformFamily.system n).
              restrictedEnergyShiftL2 lambda f) = f) ∧
        ‖R‖ ≤ (1 - M.coefficientBound - lambda)⁻¹ := by
  simpa using
    M.toUniformDobrushinFamilyData.realGap_package hlambda

end PeriodicHypercubicSpecialUnitaryUniformDobrushinMatrixFamilyData

end

end MathlibAnalytic
end MGAP4D
