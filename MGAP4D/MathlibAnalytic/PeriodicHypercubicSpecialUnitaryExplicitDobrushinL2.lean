import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryExplicitDobrushin
import MGAP4D.MathlibAnalytic.PeriodicHypercubicSpecialUnitaryDobrushinHeatBathGap

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory

noncomputable section

/-!
Connect the explicit periodic compact-Haar `SU(N)` Dobrushin matrix from the
Wilson plaquette interaction to the existing random-scan `L²` and heat-bath-gap
bridge.

All matrix, row-sum, strictness, edge-cardinality, Poincaré, coercivity, and
kernel fields are generated here.  The only remaining analytic input is the
centered random-scan `L²` Rayleigh comparison itself.
-/

/-- The explicit finite-volume heat-bath gap produced by the periodic `SU(N)`
Dobrushin coefficient. -/
def periodicHypercubicSpecialUnitaryExplicitDobrushinHeatBathGap
    (beta : ℝ) : ℝ :=
  continuousCompactOrientedDobrushinHeatBathGap
    (18 * periodicHypercubicSpecialUnitaryDobrushinEta beta)

/-- The one genuinely analytic field still needed after the explicit periodic
`SU(N)` conditional-law matrix has been constructed. -/
structure PeriodicHypercubicSpecialUnitaryCenteredRandomScanRayleighData
    (n N : ℕ) [NeZero n]
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta) where
  centered_randomScan_rayleigh_le :
    ∀ f : Lp ℝ 2
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).gibbsMeasure,
      inner ℝ
          ((periodicHypercubicSpecialUnitaryWilsonSystem
            n N hN beta beta_nonneg).randomScanHeatBathL2
            ((periodicHypercubicSpecialUnitaryWilsonSystem
              n N hN beta beta_nonneg).vacuumCenteredL2 f))
          ((periodicHypercubicSpecialUnitaryWilsonSystem
            n N hN beta beta_nonneg).vacuumCenteredL2 f) ≤
        continuousCompactOrientedDobrushinRandomScanRate
            (periodicHypercubicSpecialUnitaryWilsonSystem
              n N hN beta beta_nonneg)
            (18 * periodicHypercubicSpecialUnitaryDobrushinEta beta) *
          ‖(periodicHypercubicSpecialUnitaryWilsonSystem
            n N hN beta beta_nonneg).vacuumCenteredL2 f‖ ^ 2

/-- The explicit periodic `SU(N)` matrix and one centered Rayleigh comparison
canonically form the full matrix/random-scan certificate consumed by the
Poincaré bridge. -/
noncomputable def
    periodicHypercubicSpecialUnitaryDobrushinMatrixRandomScanCertificate
    (n N : ℕ) [NeZero n]
    (hn : 3 ≤ n)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (hBetaLt : beta < Real.log ((19 : ℝ) / 17) / 4)
    (R : PeriodicHypercubicSpecialUnitaryCenteredRandomScanRayleighData
      n N hN beta beta_nonneg) :
    ContinuousCompactOrientedGaugeWilsonDobrushinMatrixRandomScanCertificate
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg) := by
  let D := periodicHypercubicSpecialUnitaryDobrushinMatrixData
    n N hn hN beta beta_nonneg hBetaLt
  exact
    { influence := D.influence
      influence_nonneg := D.influence_nonneg
      influence_diagonal_zero := D.influence_diagonal_zero
      conditionalIntegral_difference_abs_le :=
        D.conditionalIntegral_difference_abs_le
      coefficient := D.coefficient
      coefficient_nonneg := D.coefficient_nonneg
      rowSum_le_coefficient := D.rowSum_le_coefficient
      coefficient_lt_one := D.coefficient_lt_one
      edgeCard_pos := by
        change 0 < Fintype.card (PeriodicHypercubicEdge n)
        exact Fintype.card_pos_iff.mpr ⟨(fun _ => 0), 0⟩
      centered_randomScan_rayleigh_le :=
        R.centered_randomScan_rayleigh_le }

/-- The explicit logarithmic weak-influence region gives a positive finite-volume
`SU(N)` heat-bath gap. -/
theorem periodicHypercubicSpecialUnitaryExplicitDobrushinHeatBathGap_pos
    (beta : ℝ)
    (hBetaLt : beta < Real.log ((19 : ℝ) / 17) / 4) :
    0 < periodicHypercubicSpecialUnitaryExplicitDobrushinHeatBathGap beta := by
  unfold periodicHypercubicSpecialUnitaryExplicitDobrushinHeatBathGap
    continuousCompactOrientedDobrushinHeatBathGap
  exact sub_pos.mpr
    (periodicHypercubicSpecialUnitary_eighteen_mul_eta_lt_one_of_beta_lt
      beta hBetaLt)

/-- The single centered random-scan comparison now yields the native compact-Haar
Poincaré inequality for the actual periodic `SU(N)` Wilson system. -/
theorem periodicHypercubicSpecialUnitaryExplicitDobrushinHeatBathPoincareL2
    (n N : ℕ) [NeZero n]
    (hn : 3 ≤ n)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (hBetaLt : beta < Real.log ((19 : ℝ) / 17) / 4)
    (R : PeriodicHypercubicSpecialUnitaryCenteredRandomScanRayleighData
      n N hN beta beta_nonneg) :
    periodicHypercubicSpecialUnitaryHeatBathPoincareL2
      n N hN beta beta_nonneg
        (periodicHypercubicSpecialUnitaryExplicitDobrushinHeatBathGap beta) := by
  exact continuous_compact_oriented_dobrushinMatrixHeatBathPoincareL2
    (periodicHypercubicSpecialUnitaryWilsonSystem
      n N hN beta beta_nonneg)
    (periodicHypercubicSpecialUnitaryDobrushinMatrixRandomScanCertificate
      n N hn hN beta beta_nonneg hBetaLt R)

/-- Explicit periodic `SU(N)` Dobrushin data plus the centered random-scan theorem
give the Hamiltonian coercivity lower bound on the Haar--Gibbs-vacuum
orthogonal sector. -/
theorem periodicHypercubicSpecialUnitaryExplicitDobrushin_coercive
    (n N : ℕ) [NeZero n]
    (hn : 3 ≤ n)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (hBetaLt : beta < Real.log ((19 : ℝ) / 17) / 4)
    (R : PeriodicHypercubicSpecialUnitaryCenteredRandomScanRayleighData
      n N hN beta beta_nonneg)
    (f : Lp ℝ 2
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).gibbsMeasure)
    (hf : inner ℝ
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).gibbsVacuumL2 f = 0) :
    periodicHypercubicSpecialUnitaryExplicitDobrushinHeatBathGap beta *
        ‖f‖ ^ 2 ≤
      inner ℝ
        ((periodicHypercubicSpecialUnitaryWilsonSystem
          n N hN beta beta_nonneg).heatBathHamiltonianL2 f) f := by
  exact
    continuous_compact_oriented_dobrushinMatrixHamiltonianL2_gap_on_vacuumOrthogonal
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg)
      (periodicHypercubicSpecialUnitaryDobrushinMatrixRandomScanCertificate
        n N hn hN beta beta_nonneg hBetaLt R)
      f hf

/-- In the explicit strict region, the only zero-energy vector orthogonal to the
normalized periodic `SU(N)` Haar--Gibbs vacuum is zero. -/
theorem periodicHypercubicSpecialUnitaryExplicitDobrushin_kernel_eq_zero
    (n N : ℕ) [NeZero n]
    (hn : 3 ≤ n)
    (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ)
    (beta_nonneg : 0 ≤ beta)
    (hBetaLt : beta < Real.log ((19 : ℝ) / 17) / 4)
    (R : PeriodicHypercubicSpecialUnitaryCenteredRandomScanRayleighData
      n N hN beta beta_nonneg)
    (f : Lp ℝ 2
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).gibbsMeasure)
    (hfOrth : inner ℝ
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).gibbsVacuumL2 f = 0)
    (hfZero :
      (periodicHypercubicSpecialUnitaryWilsonSystem
        n N hN beta beta_nonneg).heatBathHamiltonianL2 f = 0) :
    f = 0 := by
  exact
    periodicHypercubicSpecialUnitary_heatBathHamiltonianL2_kernel_eq_vacuum_on_orthogonal
      n N hN beta beta_nonneg
      (periodicHypercubicSpecialUnitaryExplicitDobrushinHeatBathGap beta)
      (periodicHypercubicSpecialUnitaryExplicitDobrushinHeatBathGap_pos
        beta hBetaLt)
      (periodicHypercubicSpecialUnitaryExplicitDobrushinHeatBathPoincareL2
        n N hn hN beta beta_nonneg hBetaLt R)
      f hfOrth hfZero

end

end MathlibAnalytic
end MGAP4D
