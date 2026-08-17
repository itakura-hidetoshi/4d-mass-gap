import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathShiftAction

/-!
# Rational path reflection and factorial alignment

The continuum rational path carrier admits the literal Euclidean time reflection
`θx(q) = x(-q)`.  At finite lattice spacing, however, the floor selector is not
odd in general: `⌊-t/a⌋` need not equal `-⌊t/a⌋`.

For the canonical factorial spacing this obstruction disappears eventually at
every fixed rational time, because that time becomes an exact lattice multiple.
This file records both pieces explicitly so later OS-reflection arguments never
silently replace a floor by an odd map outside its valid aligned regime.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter MeasureTheory

noncomputable section

/-- Euclidean time reflection on the countable rational path carrier. -/
def periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathReflection
    (x : ℚ → ℝ) : ℚ → ℝ :=
  fun q => x (-q)

/-- Rational path reflection is continuous in the product topology. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathReflection_continuous :
    Continuous
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathReflection := by
  exact continuous_pi (fun q => continuous_apply (-q))

/-- Rational path reflection is measurable in the product sigma algebra. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathReflection_measurable :
    Measurable
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathReflection := by
  exact measurable_pi_lambda _ (fun q => measurable_pi_apply (-q))

/-- Rational path reflection is an involution. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathReflection_involutive :
    Function.Involutive
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathReflection := by
  intro x
  funext q
  simp [periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathReflection]

/-- Reflection conjugates a common rational path translation to its inverse. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathReflection_shift
    (r : ℚ) (x : ℚ → ℝ) :
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathReflection
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift r x) =
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift (-r)
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathReflection x) := by
  funext q
  simp [periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathReflection,
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathShift]
  congr 1
  ring

/-- Read a finite rational cylinder after Euclidean time reflection. -/
def periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteJointReflectionReadout
    (J : Finset ℚ) (x : ℚ → ℝ) : ∀ q : J, ℝ :=
  fun q => x (-(q : ℚ))

/-- The reflected finite joint readout is measurable. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteJointReflectionReadout_measurable
    (J : Finset ℚ) :
    Measurable
      (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteJointReflectionReadout
        J) := by
  exact measurable_pi_lambda _ (fun q => measurable_pi_apply (-(q : ℚ)))

/-- Reflected finite joint readout is finite restriction after full path
reflection. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteJointReflectionReadout_eq_restrict_reflection
    (J : Finset ℚ) (x : ℚ → ℝ) :
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalFiniteJointReflectionReadout
        J x =
      J.restrict (π := fun _ : ℚ => ℝ)
        (periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalRationalPathReflection x) := by
  rfl

/-- Once a rational physical time is exactly a lattice multiple, the floor
selector is exactly odd at that time. -/
theorem physicalTemporalFloorStep_neg_eq_neg_of_rational_latticeMultiple
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (q : ℚ) (n : ℕ) (k : ℤ)
    (hq : (q : ℝ) = (k : ℝ) * latticeSpacing n) :
    physicalTemporalFloorStep latticeSpacing (-(q : ℝ)) n =
      -physicalTemporalFloorStep latticeSpacing (q : ℝ) n := by
  have hneg :
      (-(q : ℝ)) = ((-k : ℤ) : ℝ) * latticeSpacing n := by
    calc
      (-(q : ℝ)) = -((k : ℝ) * latticeSpacing n) := by rw [hq]
      _ = ((-k : ℤ) : ℝ) * latticeSpacing n := by
        push_cast
        ring
  rw [hneg, hq]
  rw [physicalTemporalFloorStep_lattice_multiple
    latticeSpacing latticeSpacing_pos n (-k)]
  rw [physicalTemporalFloorStep_lattice_multiple
    latticeSpacing latticeSpacing_pos n k]

/-- For every fixed rational time, factorial spacing eventually makes the floor
selector exactly odd. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_rational_floorStep_neg_eventually
    (q : ℚ) :
    ∀ᶠ n : ℕ in atTop,
      physicalTemporalFloorStep
          periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
          (-(q : ℝ)) n =
        -physicalTemporalFloorStep
          periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
          (q : ℝ) n := by
  filter_upwards [
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_rational_eventually_latticeMultiple
      q] with n hn
  rcases hn with ⟨k, hk⟩
  exact
    physicalTemporalFloorStep_neg_eq_neg_of_rational_latticeMultiple
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing
      periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFactorialLatticeSpacing_pos
      q n k hk

/-- At an exactly aligned rational time, the finite rational floor readout is
literally the existing integer-time boundary-vacuum readout. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathReadout_apply_of_latticeMultiple
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (n : ℕ) (q : ℚ) (k : ℤ)
    (hq : (q : ℝ) = (k : ℝ) * latticeSpacing n)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathReadout
        H N hN beta hbeta latticeSpacing n A q =
      periodicHypercubicEvenRestrictedBoundaryVacuumMomentAtTime
        H N hN beta hbeta k A := by
  unfold periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathReadout
  rw [hq]
  rw [physicalTemporalFloorStep_lattice_multiple
    latticeSpacing latticeSpacing_pos n k]

/-- The reflected rational coordinate of an exactly aligned finite readout is
the integer-time readout at the negated lattice index. -/
theorem
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathReadout_apply_neg_of_latticeMultiple
    (H N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (latticeSpacing : ℕ → ℝ)
    (latticeSpacing_pos : ∀ n, 0 < latticeSpacing n)
    (n : ℕ) (q : ℚ) (k : ℤ)
    (hq : (q : ℝ) = (k : ℝ) * latticeSpacing n)
    (A : PeriodicHypercubicEvenEdge H →
      Matrix.specialUnitaryGroup (Fin N) ℂ) :
    periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathReadout
        H N hN beta hbeta latticeSpacing n A (-q) =
      periodicHypercubicEvenRestrictedBoundaryVacuumMomentAtTime
        H N hN beta hbeta (-k) A := by
  unfold periodicHypercubicEvenRestrictedBoundaryVacuumPhysicalFloorRationalPathReadout
  have hneg :
      ((-q : ℚ) : ℝ) = ((-k : ℤ) : ℝ) * latticeSpacing n := by
    calc
      ((-q : ℚ) : ℝ) = -(q : ℝ) := by norm_num
      _ = -((k : ℝ) * latticeSpacing n) := by rw [hq]
      _ = ((-k : ℤ) : ℝ) * latticeSpacing n := by
        push_cast
        ring
  rw [hneg]
  rw [physicalTemporalFloorStep_lattice_multiple
    latticeSpacing latticeSpacing_pos n (-k)]

end
end MathlibAnalytic
end MGAP4D
