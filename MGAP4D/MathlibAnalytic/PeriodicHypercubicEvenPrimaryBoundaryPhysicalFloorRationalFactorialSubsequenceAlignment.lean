import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalCarryReadoutCovariance
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenPrimaryBoundaryPhysicalFloorRationalScalarPathCompactProkhorov
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
import Mathlib.Tactic

/-!
# Factorial subsequence alignment for the one-sided primary scalar path

The generic physical-floor selector has a genuine zero-or-one carry, isolated in the preceding
primary-readout layer.  For the canonical factorial spacing `a_n = (n!)⁻¹`, however, every fixed
rational time is an exact lattice multiple at all sufficiently large scales.  Strict cofinality of
the Prokhorov subsequence preserves that eventual exact alignment.

This file transports the already-proved factorial arithmetic onto the new same-root primary scalar
Prokhorov subsequence.  In particular, for a nonnegative rational shift the eventual integer lattice
multiple can be chosen as a natural number, exactly matching the aligned finite-cylinder
stationarity API.

No continuum stationarity, adjacent-step regularity premise, OS contraction, null-space
preservation, semigroup, Hamiltonian, spectral statement, or mass-gap transfer is introduced here.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- Along every primary-scalar Prokhorov subsequence at factorial spacing, the floor carry of a
fixed rational shift vanishes eventually, simultaneously at every rational observation slot. -/
theorem
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit.factorial_rational_carry_eventually_zero
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (L :
      PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
        H N hN beta hbeta
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing)
    (t : ℚ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ q : ℚ,
        physicalTemporalFloorCarry
            periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
            (q : ℝ) (t : ℝ) (L.subsequence n) = 0 := by
  exact
    L.subsequence_strictMono.tendsto_atTop.eventually
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_rational_carry_eventually_zero
        t)

/-- For a nonnegative rational shift, eventual factorial alignment along the primary-scalar
Prokhorov subsequence can be represented by a natural lattice-step count.  This is the exact receipt
required by the finite aligned primary-cylinder stationarity theorem. -/
theorem
    PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit.factorial_nonnegative_rational_eventually_naturalAligned
    (H : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)
    (L :
      PeriodicHypercubicEvenPrimarySpatialPhysicalFloorRationalScalarPlaquettePathProkhorovSubsequenceLimit
        H N hN beta hbeta
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing)
    (t : ℚ) (ht : 0 ≤ t) :
    ∀ᶠ n : ℕ in atTop,
      ∃ k : ℕ,
        PhysicalTemporalFloorRationalTimeAligned
          periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
          (L.subsequence n) t (k : ℤ) := by
  have hMultiple :
      ∀ᶠ m : ℕ in atTop,
        ∃ k : ℤ,
          (t : ℝ) =
            (k : ℝ) *
              periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing m :=
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_rational_eventually_latticeMultiple
      t
  have hAlong :
      ∀ᶠ n : ℕ in atTop,
        ∃ k : ℤ,
          (t : ℝ) =
            (k : ℝ) *
              periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
                (L.subsequence n) :=
    L.subsequence_strictMono.tendsto_atTop.eventually hMultiple
  filter_upwards [hAlong] with n hn
  rcases hn with ⟨k, hk⟩
  have ha :
      0 < periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
        (L.subsequence n) :=
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_pos _
  have htR : 0 ≤ (t : ℝ) := by
    exact_mod_cast ht
  rw [hk] at htR
  have hkR : 0 ≤ (k : ℝ) :=
    nonneg_of_mul_nonneg_right (by simpa [mul_comm] using htR) ha
  have hkZ : 0 ≤ k := by
    exact_mod_cast hkR
  have hAlignedInt :
      PhysicalTemporalFloorRationalTimeAligned
        periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
        (L.subsequence n) t k := by
    unfold PhysicalTemporalFloorRationalTimeAligned
    rw [hk]
    field_simp [ne_of_gt ha]
  rcases Int.eq_ofNat_of_zero_le hkZ with ⟨m, rfl⟩
  exact ⟨m, hAlignedInt⟩

end

end MathlibAnalytic
end MGAP4D
