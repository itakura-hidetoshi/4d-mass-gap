import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryHeatBathGap
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonDobrushinMatrixL2

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-!
Turn scale-wise compact-Haar Dobrushin matrix/random-scan certificates for the
actual periodic `SU(N)` Wilson systems into one volume-uniform non-Abelian
heat-bath gap package.

The family coefficient need not be exactly constant.  It is enough that every
finite-scale Dobrushin coefficient is bounded by one common
`coefficientBound < 1`; the resulting uniform heat-bath gap is
`1 - coefficientBound`.
-/

/-- A family of genuine compact-Haar Dobrushin matrix/random-scan certificates
for periodic `SU(N)` Wilson systems, controlled by one strict coefficient
upper bound at every positive lattice size. -/
structure PeriodicHypercubicSpecialUnitaryUniformDobrushinMatrixRandomScanData
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (beta_nonneg : ∀ n, 0 ≤ beta n) where
  coefficientBound : ℝ
  coefficientBound_nonneg : 0 ≤ coefficientBound
  coefficientBound_lt_one : coefficientBound < 1
  certificate :
    ∀ (n : ℕ) [NeZero n],
      ContinuousCompactOrientedGaugeWilsonDobrushinMatrixRandomScanCertificate
        (periodicHypercubicSpecialUnitaryWilsonSystem
          n N hN (beta n) (beta_nonneg n))
  coefficient_le_bound :
    ∀ (n : ℕ) [NeZero n],
      (certificate n).coefficient ≤ coefficientBound

namespace PeriodicHypercubicSpecialUnitaryUniformDobrushinMatrixRandomScanData

/-- The common non-Abelian heat-bath gap extracted from the family coefficient
bound. -/
def uniformGap
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {beta_nonneg : ∀ n, 0 ≤ beta n}
    (D : PeriodicHypercubicSpecialUnitaryUniformDobrushinMatrixRandomScanData
      N hN beta beta_nonneg) : ℝ :=
  continuousCompactOrientedDobrushinHeatBathGap D.coefficientBound

/-- Strict uniform Dobrushin control gives a positive scale-independent gap. -/
theorem uniformGap_pos
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {beta_nonneg : ∀ n, 0 ≤ beta n}
    (D : PeriodicHypercubicSpecialUnitaryUniformDobrushinMatrixRandomScanData
      N hN beta beta_nonneg) :
    0 < D.uniformGap := by
  unfold uniformGap continuousCompactOrientedDobrushinHeatBathGap
  exact sub_pos.mpr D.coefficientBound_lt_one

/-- At every positive periodic lattice size, the local compact-Haar Dobrushin
certificate implies the Poincaré inequality with the weaker common gap
`1 - coefficientBound`. -/
theorem heatBathPoincareL2
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {beta_nonneg : ∀ n, 0 ≤ beta n}
    (D : PeriodicHypercubicSpecialUnitaryUniformDobrushinMatrixRandomScanData
      N hN beta beta_nonneg)
    (n : ℕ)
    [NeZero n] :
    periodicHypercubicSpecialUnitaryHeatBathPoincareL2
      n N hN (beta n) (beta_nonneg n) D.uniformGap := by
  unfold periodicHypercubicSpecialUnitaryHeatBathPoincareL2
  intro f
  have hLocal :=
    (continuous_compact_oriented_dobrushinMatrixHeatBathPoincareL2
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN (beta n) (beta_nonneg n))
      (D.certificate n)) f
  have hGapLe :
      D.uniformGap ≤
        continuousCompactOrientedDobrushinHeatBathGap
          (D.certificate n).coefficient := by
    unfold uniformGap continuousCompactOrientedDobrushinHeatBathGap
    exact sub_le_sub_left (D.coefficient_le_bound n) 1
  have hScaled :=
    mul_le_mul_of_nonneg_right hGapLe
      (sq_nonneg
        ‖(periodicHypercubicSpecialUnitaryWilsonSystem
          n N hN (beta n) (beta_nonneg n)).vacuumCenteredL2 f‖)
  exact hScaled.trans hLocal

/-- The scale-wise non-Abelian Dobrushin family canonically constructs the
uniform periodic `SU(N)` heat-bath gap datum introduced in PR #830. -/
noncomputable def toUniformHeatBathGapData
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {beta_nonneg : ∀ n, 0 ≤ beta n}
    (D : PeriodicHypercubicSpecialUnitaryUniformDobrushinMatrixRandomScanData
      N hN beta beta_nonneg) :
    PeriodicHypercubicSpecialUnitaryUniformHeatBathGapData
      N hN beta beta_nonneg where
  gap := D.uniformGap
  gap_pos := D.uniformGap_pos
  poincare := by
    intro n
    exact D.heatBathPoincareL2 n

/-- Uniform compact-Haar Dobrushin matrix/random-scan data give the same
vacuum-orthogonal Hamiltonian coercivity lower bound at every finite periodic
`SU(N)` scale. -/
theorem coercive
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {beta_nonneg : ∀ n, 0 ≤ beta n}
    (D : PeriodicHypercubicSpecialUnitaryUniformDobrushinMatrixRandomScanData
      N hN beta beta_nonneg)
    (n : ℕ)
    [NeZero n]
    (f : Lp ℝ 2
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN (beta n) (beta_nonneg n)).gibbsMeasure)
    (hf : inner ℝ
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN (beta n) (beta_nonneg n)).gibbsVacuumL2 f = 0) :
    D.uniformGap * ‖f‖ ^ 2 ≤
      inner ℝ
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          n N hN (beta n) (beta_nonneg n)).heatBathHamiltonianL2 f) f :=
  PeriodicHypercubicSpecialUnitaryUniformHeatBathGapData.coercive
    D.toUniformHeatBathGapData n f hf

/-- Uniform strict compact-Haar Dobrushin data exclude every nonzero
zero-energy vector orthogonal to the normalized Haar--Gibbs vacuum, at every
finite periodic `SU(N)` scale. -/
theorem kernel_eq_vacuum_on_orthogonal
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {beta_nonneg : ∀ n, 0 ≤ beta n}
    (D : PeriodicHypercubicSpecialUnitaryUniformDobrushinMatrixRandomScanData
      N hN beta beta_nonneg)
    (n : ℕ)
    [NeZero n]
    (f : Lp ℝ 2
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN (beta n) (beta_nonneg n)).gibbsMeasure)
    (hfOrth : inner ℝ
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN (beta n) (beta_nonneg n)).gibbsVacuumL2 f = 0)
    (hfZero :
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN (beta n) (beta_nonneg n)).heatBathHamiltonianL2 f = 0) :
    f = 0 :=
  PeriodicHypercubicSpecialUnitaryUniformHeatBathGapData.kernel_eq_vacuum_on_orthogonal
    D.toUniformHeatBathGapData n f hfOrth hfZero

end PeriodicHypercubicSpecialUnitaryUniformDobrushinMatrixRandomScanData

end

end MathlibAnalytic
end MGAP4D
