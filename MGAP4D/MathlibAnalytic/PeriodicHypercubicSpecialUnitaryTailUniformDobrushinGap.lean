import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryExplicitDobrushinL2

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-!
Package the explicit periodic compact-Haar `SU(N)` Dobrushin gap uniformly on
the nondegenerate lattice tail `n ≥ 3`.

The geometry used to prove the sharp shared-plaquette incidence bound is valid
on this tail.  No artificial claim about the degenerate side lengths `n = 1,2`
is needed for continuum subsequences whose lattice size tends to infinity.
-/

/-- Uniform explicit `SU(N)` Dobrushin and centered-Rayleigh data on every
nondegenerate periodic lattice scale. -/
structure PeriodicHypercubicSpecialUnitaryTailUniformDobrushinGapData
    (N : ℕ)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ)
    (beta_nonneg : ∀ n, 0 ≤ beta n) where
  coefficientBound : ℝ
  coefficientBound_nonneg : 0 ≤ coefficientBound
  coefficientBound_lt_one : coefficientBound < 1
  beta_lt_threshold :
    ∀ n : ℕ, 3 ≤ n →
      beta n < Real.log ((19 : ℝ) / 17) / 4
  coefficient_le_bound :
    ∀ n : ℕ, 3 ≤ n →
      18 * periodicHypercubicSpecialUnitaryDobrushinEta (beta n) ≤
        coefficientBound
  rayleigh :
    ∀ (n : ℕ) [NeZero n], 3 ≤ n →
      PeriodicHypercubicSpecialUnitaryCenteredRandomScanRayleighData
        n N hN (beta n) (beta_nonneg n)

namespace PeriodicHypercubicSpecialUnitaryTailUniformDobrushinGapData

/-- The common heat-bath gap on the nondegenerate periodic tail. -/
def uniformGap
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {beta_nonneg : ∀ n, 0 ≤ beta n}
    (D : PeriodicHypercubicSpecialUnitaryTailUniformDobrushinGapData
      N hN beta beta_nonneg) : ℝ :=
  continuousCompactOrientedDobrushinHeatBathGap D.coefficientBound

/-- Strict common coefficient control gives a positive tail-uniform gap. -/
theorem uniformGap_pos
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {beta_nonneg : ∀ n, 0 ≤ beta n}
    (D : PeriodicHypercubicSpecialUnitaryTailUniformDobrushinGapData
      N hN beta beta_nonneg) :
    0 < D.uniformGap := by
  unfold uniformGap continuousCompactOrientedDobrushinHeatBathGap
  exact sub_pos.mpr D.coefficientBound_lt_one

/-- Every nondegenerate periodic scale satisfies the common compact-Haar
`SU(N)` heat-bath Poincaré inequality. -/
theorem heatBathPoincareL2
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {beta_nonneg : ∀ n, 0 ≤ beta n}
    (D : PeriodicHypercubicSpecialUnitaryTailUniformDobrushinGapData
      N hN beta beta_nonneg)
    (n : ℕ)
    [NeZero n]
    (hn : 3 ≤ n) :
    periodicHypercubicSpecialUnitaryHeatBathPoincareL2
      n N hN (beta n) (beta_nonneg n) D.uniformGap := by
  unfold periodicHypercubicSpecialUnitaryHeatBathPoincareL2
  intro f
  have hLocal :=
    (periodicHypercubicSpecialUnitaryExplicitDobrushinHeatBathPoincareL2
      n N hn hN (beta n) (beta_nonneg n)
      (D.beta_lt_threshold n hn) (D.rayleigh n hn)) f
  have hGapLe :
      D.uniformGap ≤
        periodicHypercubicSpecialUnitaryExplicitDobrushinHeatBathGap
          (beta n) := by
    unfold uniformGap
      periodicHypercubicSpecialUnitaryExplicitDobrushinHeatBathGap
      continuousCompactOrientedDobrushinHeatBathGap
    exact sub_le_sub_left (D.coefficient_le_bound n hn) 1
  have hScaled :=
    mul_le_mul_of_nonneg_right hGapLe
      (sq_nonneg
        ‖(periodicHypercubicSpecialUnitaryWilsonSystem
          n N hN (beta n) (beta_nonneg n)).vacuumCenteredL2 f‖)
  exact hScaled.trans hLocal

/-- Tail-uniform explicit `SU(N)` Dobrushin data give one common coercive
Hamiltonian lower bound at every periodic scale `n ≥ 3`. -/
theorem coercive
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {beta_nonneg : ∀ n, 0 ≤ beta n}
    (D : PeriodicHypercubicSpecialUnitaryTailUniformDobrushinGapData
      N hN beta beta_nonneg)
    (n : ℕ)
    [NeZero n]
    (hn : 3 ≤ n)
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
  periodicHypercubicSpecialUnitary_heatBathHamiltonianL2_gap_on_vacuumOrthogonal
    n N hN (beta n) (beta_nonneg n) D.uniformGap
    (D.heatBathPoincareL2 n hn) f hf

/-- On every nondegenerate scale, the common positive gap excludes nonzero
zero-energy vectors orthogonal to the normalized Haar--Gibbs vacuum. -/
theorem kernel_eq_zero
    {N : ℕ}
    {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ}
    {beta_nonneg : ∀ n, 0 ≤ beta n}
    (D : PeriodicHypercubicSpecialUnitaryTailUniformDobrushinGapData
      N hN beta beta_nonneg)
    (n : ℕ)
    [NeZero n]
    (hn : 3 ≤ n)
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
  periodicHypercubicSpecialUnitary_heatBathHamiltonianL2_kernel_eq_vacuum_on_orthogonal
    n N hN (beta n) (beta_nonneg n) D.uniformGap D.uniformGap_pos
    (D.heatBathPoincareL2 n hn) f hfOrth hfZero

end PeriodicHypercubicSpecialUnitaryTailUniformDobrushinGapData

end

end MathlibAnalytic
end MGAP4D
