import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathCarry
import Mathlib.Analysis.SpecificLimits.Basic

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- A canonical lattice-spacing sequence whose denominators absorb every fixed
rational time after finitely many scales.

Using `n!` rather than `n` is deliberate: every fixed positive integer divides
`n!` for all sufficiently large `n`. -/
noncomputable def
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
    (n : ℕ) : ℝ :=
  ((n.factorial : ℝ))⁻¹

/-- The factorial lattice spacing is strictly positive at every scale. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_pos
    (n : ℕ) :
    0 < periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing n := by
  unfold periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
  positivity

/-- The factorial lattice spacing tends to zero. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_tendsto_zero :
    Tendsto
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
      atTop (nhds 0) := by
  have hfactorial :
      Tendsto (fun n : ℕ => (n.factorial : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop :
      Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop).comp
      factorial_tendsto_atTop
  simpa only [
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing] using
    tendsto_inv_atTop_zero.comp hfactorial

/-- Every fixed rational physical time is an exact element of the factorial
lattice subgroup at all sufficiently large scales.

This is the arithmetic reason factorial spacing eliminates the floor carry for
rational translations without any stochastic-continuity premise. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_rational_eventually_latticeMultiple
    (r : ℚ) :
    ∀ᶠ n : ℕ in atTop,
      ∃ k : ℤ,
        (r : ℝ) =
          (k : ℝ) *
            periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing n := by
  filter_upwards [eventually_ge_atTop r.den] with n hn
  have hdvd : r.den ∣ n.factorial :=
    Nat.dvd_factorial r.den_pos hn
  rcases hdvd with ⟨m, hm⟩
  have hmne : m ≠ 0 := by
    intro hm0
    rw [hm0, Nat.mul_zero] at hm
    exact n.factorial_ne_zero hm
  let k : ℤ := r.num * (m : ℤ)
  refine ⟨k, ?_⟩
  have hdenQ : (r.den : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt r.den_pos)
  have hmQ : (m : ℚ) ≠ 0 := by
    exact_mod_cast hmne
  have hkQ :
      r = (k : ℚ) * ((n.factorial : ℚ))⁻¹ := by
    rw [← r.num_div_den]
    dsimp [k]
    rw [Int.cast_mul, Int.cast_natCast, hm]
    push_cast
    field_simp [hdenQ, hmQ]
  have hkR := congrArg (fun z : ℚ => (z : ℝ)) hkQ
  simpa only [
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing,
    Rat.cast_mul, Rat.cast_intCast, Rat.cast_inv_nat] using hkR

/-- Consequently, for every fixed rational translation, the binary floor carry
vanishes eventually at every rational observation coordinate simultaneously. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_rational_carry_eventually_zero
    (r : ℚ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ q : ℚ,
        physicalTemporalFloorCarry
            periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
            (q : ℝ) (r : ℝ) n = 0 := by
  filter_upwards [
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_rational_eventually_latticeMultiple
      r] with n hn
  rcases hn with ⟨k, hk⟩
  intro q
  rw [hk]
  exact
    physicalTemporalFloorCarry_lattice_multiple
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_pos
      (q : ℝ) n k

end

end MathlibAnalytic
end MGAP4D
