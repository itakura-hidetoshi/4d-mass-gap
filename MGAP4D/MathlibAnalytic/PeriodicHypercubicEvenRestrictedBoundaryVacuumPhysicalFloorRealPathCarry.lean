import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathLaw
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The exact carry produced when two physical real times are converted to
integer lattice steps by the scale-wise floor selector.

The carry is defined before any probabilistic argument.  Its only possible
values are `0` and `1`; hence arbitrary real-time composition differs from a
common discrete path shift by at most one lattice step at each readout
coordinate. -/
noncomputable def physicalTemporalFloorCarry
    (latticeSpacing : ℕ → ℝ) (t s : ℝ) (n : ℕ) : ℤ :=
  physicalTemporalFloorStep latticeSpacing (t + s) n -
    physicalTemporalFloorStep latticeSpacing t n -
    physicalTemporalFloorStep latticeSpacing s n

/-- The floor-addition carry is exactly binary. -/
theorem physicalTemporalFloorCarry_eq_zero_or_one
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (t s : ℝ) (n : ℕ) :
    physicalTemporalFloorCarry latticeSpacing t s n = 0 ∨
      physicalTemporalFloorCarry latticeSpacing t s n = 1 := by
  have hne : latticeSpacing n ≠ 0 := ne_of_gt (latticeSpacing_pos n)
  have hquot :
      (t + s) / latticeSpacing n =
        t / latticeSpacing n + s / latticeSpacing n := by
    field_simp [hne]
  have hlo :
      ⌊t / latticeSpacing n⌋ + ⌊s / latticeSpacing n⌋ ≤
        ⌊(t + s) / latticeSpacing n⌋ := by
    rw [hquot]
    exact Int.le_floor_add _ _
  have hhi :
      ⌊(t + s) / latticeSpacing n⌋ - 1 ≤
        ⌊t / latticeSpacing n⌋ + ⌊s / latticeSpacing n⌋ := by
    rw [hquot]
    exact Int.le_floor_add_floor _ _
  unfold physicalTemporalFloorCarry physicalTemporalFloorStep
  omega

/-- Order form of the binary carry bound. -/
theorem physicalTemporalFloorCarry_bounds
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (t s : ℝ) (n : ℕ) :
    0 ≤ physicalTemporalFloorCarry latticeSpacing t s n ∧
      physicalTemporalFloorCarry latticeSpacing t s n ≤ 1 := by
  rcases physicalTemporalFloorCarry_eq_zero_or_one
      latticeSpacing latticeSpacing_pos t s n with h | h
  · simp [h]
  · simp [h]

/-- Exact addition formula for the canonical floor-selected lattice steps. -/
theorem physicalTemporalFloorStep_add_eq_add_add_carry
    (latticeSpacing : ℕ → ℝ) (t s : ℝ) (n : ℕ) :
    physicalTemporalFloorStep latticeSpacing (t + s) n =
      physicalTemporalFloorStep latticeSpacing t n +
        physicalTemporalFloorStep latticeSpacing s n +
          physicalTemporalFloorCarry latticeSpacing t s n := by
  unfold physicalTemporalFloorCarry
  omega

/-- Arbitrary real translation of a floor-extended path is a common floor shift
plus the exact binary one-step carry at the observation time.

This is the precise deterministic obstruction between the already proved
`a_n ℤ` stationarity and a genuine all-real-time stationarity theorem. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathShift_floorExtension_apply_carry
    (latticeSpacing : ℕ → ℝ)
    (n : ℕ) (s t : ℝ) (x : ℤ → ℝ) :
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathShift s
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathExtension
          latticeSpacing n x) t =
      x
        (physicalTemporalFloorStep latticeSpacing t n +
          physicalTemporalFloorStep latticeSpacing s n +
          physicalTemporalFloorCarry latticeSpacing t s n) := by
  unfold periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathShift
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathExtension
  rw [physicalTemporalFloorStep_add_eq_add_add_carry]

/-- A physical time which is exactly a lattice-time multiple has the expected
integer floor step. -/
theorem physicalTemporalFloorStep_lattice_multiple
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (n : ℕ) (k : ℤ) :
    physicalTemporalFloorStep latticeSpacing
        ((k : ℝ) * latticeSpacing n) n = k := by
  have h :=
    physicalTemporalFloorStep_add_lattice_multiple
      latticeSpacing latticeSpacing_pos 0 n k
  simpa [physicalTemporalFloorStep] using h

/-- The binary carry vanishes identically when the translated physical time is
an exact element of the lattice subgroup `a_n ℤ`.

Thus the new carry decomposition recovers the previously proved exact lattice
subgroup covariance as the zero-carry case. -/
theorem physicalTemporalFloorCarry_lattice_multiple
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (t : ℝ) (n : ℕ) (k : ℤ) :
    physicalTemporalFloorCarry latticeSpacing t
        ((k : ℝ) * latticeSpacing n) n = 0 := by
  have hadd :=
    physicalTemporalFloorStep_add_lattice_multiple
      latticeSpacing latticeSpacing_pos t n k
  have hstep :=
    physicalTemporalFloorStep_lattice_multiple
      latticeSpacing latticeSpacing_pos n k
  unfold physicalTemporalFloorCarry
  rw [hadd, hstep]
  omega

/-- At exact lattice-time shifts the general carry formula collapses to the
already established integer path shift formula. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathShift_floorExtension_apply_lattice_multiple
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (n : ℕ) (k : ℤ) (t : ℝ) (x : ℤ → ℝ) :
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathShift
        ((k : ℝ) * latticeSpacing n)
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathExtension
          latticeSpacing n x) t =
      x (physicalTemporalFloorStep latticeSpacing t n + k) := by
  rw [
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRealPathShift_floorExtension_apply_carry]
  rw [physicalTemporalFloorStep_lattice_multiple
    latticeSpacing latticeSpacing_pos n k]
  rw [physicalTemporalFloorCarry_lattice_multiple
    latticeSpacing latticeSpacing_pos t n k]
  simp

end

end MathlibAnalytic
end MGAP4D
