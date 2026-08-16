import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathCylinderCarry
import MGAP4D.MathlibAnalytic.PhysicalYangMillsOrientedFloorTemporalApproximation

namespace MGAP4D
namespace MathlibAnalytic

open Filter

noncomputable section

/-- Multiplying the binary floor carry by the lattice spacing makes it vanish in
the continuum limit.

No regularity of the carry sequence is required: at every scale it is either
`0` or `1`, while the lattice spacing tends to zero. -/
theorem physicalTemporalFloorCarry_mul_latticeSpacing_tendsto_zero
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero : Tendsto latticeSpacing atTop (nhds 0))
    (t s : ℝ) :
    Tendsto
      (fun n : ℕ =>
        (physicalTemporalFloorCarry latticeSpacing t s n : ℝ) *
          latticeSpacing n)
      atTop (nhds 0) := by
  have hseq :
      (fun n : ℕ =>
        (physicalTemporalFloorCarry latticeSpacing t s n : ℝ) *
          latticeSpacing n) =
      (fun n : ℕ =>
        if physicalTemporalFloorCarry latticeSpacing t s n = 0 then
          (0 : ℝ)
        else latticeSpacing n) := by
    funext n
    rcases physicalTemporalFloorCarry_eq_zero_or_one
        latticeSpacing latticeSpacing_pos t s n with hcarry | hcarry
    · simp [hcarry]
    · simp [hcarry]
  rw [hseq]
  exact Filter.Tendsto.if' tendsto_const_nhds latticeSpacing_tendsto_zero

/-- Adding the binary carry to a floor-selected lattice coordinate does not
change its physical continuum target.

This is the deterministic limit statement needed after the exact common-shift
factorization of an arbitrary real cylinder translation. -/
theorem physicalTemporalFloorStep_add_carry_physicalTime_tendsto
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero : Tendsto latticeSpacing atTop (nhds 0))
    (t s : ℝ) :
    Tendsto
      (fun n : ℕ =>
        (((physicalTemporalFloorStep latticeSpacing t n +
            physicalTemporalFloorCarry latticeSpacing t s n : ℤ) : ℝ) *
          latticeSpacing n))
      atTop (nhds t) := by
  have hfloor :=
    physicalTemporalFloorStep_tendsto
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero t
  have hcarry :=
    physicalTemporalFloorCarry_mul_latticeSpacing_tendsto_zero
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero t s
  simpa [Int.cast_add, add_mul] using hfloor.add hcarry

/-- The carry-corrected physical time convergence is stable under every strictly
increasing subsequence, in particular under the same Prokhorov subsequence used
by the path-valued continuum limit. -/
theorem physicalTemporalFloorStep_add_carry_physicalTime_tendsto_subsequence
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero : Tendsto latticeSpacing atTop (nhds 0))
    (subsequence : ℕ → ℕ) (hsubsequence : StrictMono subsequence)
    (t s : ℝ) :
    Tendsto
      (fun n : ℕ =>
        (((physicalTemporalFloorStep latticeSpacing t (subsequence n) +
            physicalTemporalFloorCarry latticeSpacing t s (subsequence n) : ℤ) : ℝ) *
          latticeSpacing (subsequence n)))
      atTop (nhds t) := by
  exact
    (physicalTemporalFloorStep_add_carry_physicalTime_tendsto
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero t s).comp
      hsubsequence.tendsto_atTop

/-- Every coordinate of a finite residual cylinder produced by the arbitrary
real-shift carry factorization still represents its original physical target
time in the continuum limit. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRealPathResidualCylinder_physicalTime_tendsto_subsequence
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (latticeSpacing_tendsto_zero : Tendsto latticeSpacing atTop (nhds 0))
    (subsequence : ℕ → ℕ) (hsubsequence : StrictMono subsequence)
    (s : ℝ) (J : Finset ℝ) (t : J) :
    Tendsto
      (fun n : ℕ =>
        (((physicalTemporalFloorStep latticeSpacing (t : ℝ) (subsequence n) +
            physicalTemporalFloorCarry latticeSpacing (t : ℝ) s (subsequence n) : ℤ) : ℝ) *
          latticeSpacing (subsequence n)))
      atTop (nhds (t : ℝ)) := by
  exact
    physicalTemporalFloorStep_add_carry_physicalTime_tendsto_subsequence
      latticeSpacing latticeSpacing_pos latticeSpacing_tendsto_zero
      subsequence hsubsequence (t : ℝ) s

end

end MathlibAnalytic
end MGAP4D
