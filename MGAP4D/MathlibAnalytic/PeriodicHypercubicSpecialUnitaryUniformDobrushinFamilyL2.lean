import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryPhysicalEmbedding
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonUniformDobrushinResolventNormL2

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Scale-dependent periodic four-dimensional `SU(N)` Wilson systems equipped
with local strict Dobrushin certificates and one volume-independent upper
bound for all Dobrushin coefficients. -/
structure PeriodicHypercubicSpecialUnitaryUniformDobrushinFamilyData
    (sideLength : ℕ → ℕ)
    (sideLength_pos : ∀ n, 0 < sideLength n)
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (beta_nonneg : ∀ n, 0 ≤ beta n) where
  certificate : ∀ n,
    ContinuousCompactOrientedGaugeWilsonDobrushinRandomScanRayleighCertificate
      (periodicHypercubicSpecialUnitaryWilsonSystemOfPositiveSide
        (sideLength n) N (sideLength_pos n) hN
        (beta n) (beta_nonneg n))
  coefficientBound : ℝ
  coefficientBound_nonneg : 0 ≤ coefficientBound
  coefficientBound_lt_one : coefficientBound < 1
  coefficient_le : ∀ n, (certificate n).coefficient ≤ coefficientBound

namespace PeriodicHypercubicSpecialUnitaryUniformDobrushinFamilyData

variable
    {sideLength : ℕ → ℕ}
    {sideLength_pos : ∀ n, 0 < sideLength n}
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {beta_nonneg : ∀ n, 0 ≤ beta n}

/-- The concrete periodic `SU(N)` family viewed as the generic uniformly
Dobrushin-controlled compact Wilson family. -/
noncomputable def toUniformFamily
    (D : PeriodicHypercubicSpecialUnitaryUniformDobrushinFamilyData
      sideLength sideLength_pos N hN beta beta_nonneg) :
    ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ℕ where
  system := fun n =>
    periodicHypercubicSpecialUnitaryWilsonSystemOfPositiveSide
      (sideLength n) N (sideLength_pos n) hN
      (beta n) (beta_nonneg n)
  certificate := D.certificate
  coefficientBound := D.coefficientBound
  coefficientBound_nonneg := D.coefficientBound_nonneg
  coefficientBound_lt_one := D.coefficientBound_lt_one
  coefficient_le := D.coefficient_le

@[simp] theorem toUniformFamily_system
    (D : PeriodicHypercubicSpecialUnitaryUniformDobrushinFamilyData
      sideLength sideLength_pos N hN beta beta_nonneg)
    (n : ℕ) :
    (D.toUniformFamily.system n) =
      periodicHypercubicSpecialUnitaryWilsonSystemOfPositiveSide
        (sideLength n) N (sideLength_pos n) hN
        (beta n) (beta_nonneg n) :=
  rfl

@[simp] theorem toUniformFamily_gap
    (D : PeriodicHypercubicSpecialUnitaryUniformDobrushinFamilyData
      sideLength sideLength_pos N hN beta beta_nonneg) :
    continuousCompactOrientedUniformDobrushinGap D.toUniformFamily =
      1 - D.coefficientBound :=
  rfl

/-- The concrete periodic `SU(N)` family has one positive volume-independent
excitation gap. -/
theorem uniformGap_pos
    (D : PeriodicHypercubicSpecialUnitaryUniformDobrushinFamilyData
      sideLength sideLength_pos N hN beta beta_nonneg) :
    0 < continuousCompactOrientedUniformDobrushinGap D.toUniformFamily :=
  continuous_compact_oriented_uniformDobrushinGap_pos D.toUniformFamily

/-- Every periodic `SU(N)` finite-volume excitation Hamiltonian satisfies the
same coercive lower bound. -/
theorem restrictedEnergy_gap
    (D : PeriodicHypercubicSpecialUnitaryUniformDobrushinFamilyData
      sideLength sideLength_pos N hN beta beta_nonneg)
    (n : ℕ)
    (f : (D.toUniformFamily.system n).VacuumOrthogonalL2) :
    (1 - D.coefficientBound) * ‖f‖ ^ 2 ≤
      inner ℝ
        ((D.toUniformFamily.system n).heatBathHamiltonianVacuumOrthogonalL2 f)
        f := by
  simpa only [toUniformFamily_gap] using
    continuous_compact_oriented_uniformDobrushin_restrictedEnergy_gap
      D.toUniformFamily n f

/-- Uniform finite-volume real-resolvent package for the concrete periodic
`SU(N)` family. -/
theorem realGap_package
    (D : PeriodicHypercubicSpecialUnitaryUniformDobrushinFamilyData
      sideLength sideLength_pos N hN beta beta_nonneg)
    {lambda : ℝ}
    (hlambda : lambda < 1 - D.coefficientBound) :
    ∀ n : ℕ,
      ∃ R : (D.toUniformFamily.system n).VacuumOrthogonalL2 →L[ℝ]
          (D.toUniformFamily.system n).VacuumOrthogonalL2,
        (∀ y,
          (D.toUniformFamily.system n).restrictedEnergyShiftL2 lambda (R y) = y) ∧
        (∀ f,
          R ((D.toUniformFamily.system n).restrictedEnergyShiftL2 lambda f) = f) ∧
        ‖R‖ ≤ (1 - D.coefficientBound - lambda)⁻¹ := by
  have hbelow :
      lambda < continuousCompactOrientedUniformDobrushinGap D.toUniformFamily := by
    simpa only [toUniformFamily_gap] using hlambda
  simpa only [toUniformFamily_gap] using
    continuous_compact_oriented_uniformDobrushin_realGap_package
      D.toUniformFamily hbelow

end PeriodicHypercubicSpecialUnitaryUniformDobrushinFamilyData

end

end MathlibAnalytic
end MGAP4D
