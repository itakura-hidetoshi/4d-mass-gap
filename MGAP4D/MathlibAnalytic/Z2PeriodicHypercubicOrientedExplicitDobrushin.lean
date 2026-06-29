import MGAP4D.MathlibAnalytic.FiniteOrientedLatticeWilsonSharedPlaquetteCoefficientBound
import MGAP4D.MathlibAnalytic.Z2PeriodicHypercubicOrientedWilsonSystem

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Explicit active-influence majorant for the periodic oriented `Z₂` system. -/
def z2PeriodicHypercubicOrientedDobrushinEta
    (beta : ℝ) : ℝ :=
  (Real.exp (beta * 2) - 1) /
    (Real.exp (beta * 2) + 1)

/-- The periodic oriented `Z₂` plaquette energy is uniformly bounded by one. -/
theorem z2PeriodicHypercubicOriented_uniformPlaquetteEnergyUpperBound_one
    (n : ℕ) [NeZero n]
    (beta : ℝ)
    (hBeta : 0 ≤ beta) :
    (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta).UniformPlaquetteEnergyUpperBound 1 := by
  classical
  intro g
  dsimp [z2PeriodicHypercubicOrientedWilsonSystem]
  split_ifs <;> norm_num

/-- In four periodic dimensions, exact oriented canonical influence satisfies
the explicit `18 × eta` estimate. -/
theorem z2PeriodicHypercubicOriented_canonicalDobrushinCoefficient_le
    (n : ℕ) [NeZero n]
    (hn : 3 ≤ n)
    (beta : ℝ)
    (hBeta : 0 ≤ beta) :
    (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta).canonicalDobrushinCoefficient
          (z2PeriodicHypercubicOrientedIncidenceCertificate
            n hn beta hBeta).edgeCard_pos ≤
      18 * z2PeriodicHypercubicOrientedDobrushinEta beta := by
  let L := z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta
  let C := z2PeriodicHypercubicOrientedIncidenceCertificate n hn beta hBeta
  have hBound :=
    finite_oriented_canonicalDobrushinCoefficient_le_of_sharedPlaquetteEnergy
      L C.edgeCard_pos 1
      (z2PeriodicHypercubicOriented_uniformPlaquetteEnergyUpperBound_one
        n beta hBeta)
      1 18
      C.activeSharedPlaquetteCard_le_one
      C.activeNeighborCard_le_eighteen
  simpa [L, C, z2PeriodicHypercubicOrientedDobrushinEta] using hBound

/-- The threshold `exp (2 beta) < 19/17` makes the `18 × eta` bound strict. -/
theorem z2PeriodicHypercubicOriented_eighteen_mul_eta_lt_one_of_exp_lt
    (beta : ℝ)
    (hExp : Real.exp (beta * 2) < (19 : ℝ) / 17) :
    18 * z2PeriodicHypercubicOrientedDobrushinEta beta < 1 := by
  let x : ℝ := Real.exp (beta * 2)
  have hx : x < (19 : ℝ) / 17 := by
    simpa [x] using hExp
  have hden : 0 < x + 1 := by
    dsimp [x]
    positivity
  calc
    18 * z2PeriodicHypercubicOrientedDobrushinEta beta =
        (18 * (x - 1)) / (x + 1) := by
      dsimp [z2PeriodicHypercubicOrientedDobrushinEta, x]
      ring
    _ < 1 := by
      apply (div_lt_iff₀ hden).2
      norm_num at hx ⊢
      nlinarith

/-- The exact oriented coefficient is strict under the exponential threshold. -/
theorem z2PeriodicHypercubicOriented_canonicalDobrushinCoefficient_lt_one_of_exp_lt
    (n : ℕ) [NeZero n]
    (hn : 3 ≤ n)
    (beta : ℝ)
    (hBeta : 0 ≤ beta)
    (hExp : Real.exp (beta * 2) < (19 : ℝ) / 17) :
    (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta).canonicalDobrushinCoefficient
          (z2PeriodicHypercubicOrientedIncidenceCertificate
            n hn beta hBeta).edgeCard_pos < 1 :=
  lt_of_le_of_lt
    (z2PeriodicHypercubicOriented_canonicalDobrushinCoefficient_le
      n hn beta hBeta)
    (z2PeriodicHypercubicOriented_eighteen_mul_eta_lt_one_of_exp_lt
      beta hExp)

/-- The logarithmic small-coupling condition implies strict contraction. -/
theorem z2PeriodicHypercubicOriented_canonicalDobrushinCoefficient_lt_one_of_beta_lt
    (n : ℕ) [NeZero n]
    (hn : 3 ≤ n)
    (beta : ℝ)
    (hBeta : 0 ≤ beta)
    (hBetaLt : beta < Real.log ((19 : ℝ) / 17) / 2) :
    (z2PeriodicHypercubicOrientedWilsonSystem n beta hBeta).canonicalDobrushinCoefficient
          (z2PeriodicHypercubicOrientedIncidenceCertificate
            n hn beta hBeta).edgeCard_pos < 1 := by
  have hArg : beta * 2 < Real.log ((19 : ℝ) / 17) := by
    nlinarith
  have hRatioPos : 0 < (19 : ℝ) / 17 := by
    norm_num
  have hExp : Real.exp (beta * 2) < (19 : ℝ) / 17 := by
    calc
      Real.exp (beta * 2) <
          Real.exp (Real.log ((19 : ℝ) / 17)) :=
        Real.exp_lt_exp.mpr hArg
      _ = (19 : ℝ) / 17 := Real.exp_log hRatioPos
  exact
    z2PeriodicHypercubicOriented_canonicalDobrushinCoefficient_lt_one_of_exp_lt
      n hn beta hBeta hExp

end

end MathlibAnalytic
end MGAP4D
