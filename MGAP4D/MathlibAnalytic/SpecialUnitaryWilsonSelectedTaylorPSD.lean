import MGAP4D.MathlibAnalytic.RealKernelPositiveSemidefiniteCertificateAlgebra
import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonKernelFeatureMeasurability
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter
open scoped BigOperators Topology

noncomputable section

/-- The exact nonnegative scalar multiplying the degree-`n` normalized-trace
kernel inside one Wilson relative-kernel Taylor expansion. -/
noncomputable def specialUnitaryWilsonSelectedTaylorCoefficient
    (beta : ℝ)
    (n : ℕ) : ℝ :=
  Real.exp (-beta) * (beta ^ n / (Nat.factorial n : ℝ))

/-- One selected Taylor degree of the one-plaquette Wilson relative kernel. -/
def specialUnitaryWilsonRelativeSelectedDegreeKernel
    (N : ℕ)
    (beta : ℝ)
    (n : ℕ)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  specialUnitaryWilsonSelectedTaylorCoefficient beta n *
    specialUnitaryNormalizedTraceRelativeKernel N g h ^ n

/-- At nonnegative coupling every selected Taylor degree is itself a concrete
Hilbert kernel. -/
noncomputable def specialUnitaryWilsonRelativeSelectedDegreeFeature
    (N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (n : ℕ) :
    RealHilbertKernelFeature
      (Matrix.specialUnitaryGroup (Fin N) ℂ)
      (specialUnitaryWilsonRelativeSelectedDegreeKernel N beta n) := by
  have hCoefficient :
      0 ≤ specialUnitaryWilsonSelectedTaylorCoefficient beta n := by
    unfold specialUnitaryWilsonSelectedTaylorCoefficient
    exact mul_nonneg (Real.exp_nonneg _)
      (div_nonneg (pow_nonneg hbeta _) (by positivity))
  simpa [specialUnitaryWilsonRelativeSelectedDegreeKernel] using
    RealHilbertKernelFeature.nonnegSMul
      (specialUnitaryWilsonSelectedTaylorCoefficient beta n)
      hCoefficient
      ((specialUnitaryNormalizedTraceRelativeKernelFeature N hN).pow n)

/-- The finite Taylor remainder obtained by deleting one selected degree from
the complete one-plaquette Wilson partial sum.  It is written as a literal
finite sum, so no subtraction is used in its PSD certificate. -/
def specialUnitaryWilsonRelativeKernelPartialSelectedRemainder
    (N : ℕ)
    (beta : ℝ)
    (degree selected : ℕ)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  ∑ m ∈ (Finset.range (degree + 1)).erase selected,
    specialUnitaryWilsonRelativeSelectedDegreeKernel N beta m g h

/-- Deleting one Taylor degree from a finite Wilson partial leaves a symmetric
positive-semidefinite kernel.  Every surviving degree is a nonnegatively
scaled tensor power and finite sums are closed in the PSD cone. -/
theorem specialUnitaryWilsonRelativeKernelPartialSelectedRemainder_positiveSemidefiniteCertificate
    (N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (degree selected : ℕ) :
    RealKernelPositiveSemidefiniteCertificate
      (Matrix.specialUnitaryGroup (Fin N) ℂ)
      (specialUnitaryWilsonRelativeKernelPartialSelectedRemainder
        N beta degree selected) := by
  classical
  unfold specialUnitaryWilsonRelativeKernelPartialSelectedRemainder
  refine RealKernelPositiveSemidefiniteCertificate.finsetSum
    ((Finset.range (degree + 1)).erase selected)
    (fun m => specialUnitaryWilsonRelativeSelectedDegreeKernel N beta m) ?_
  intro m hm
  exact
    (specialUnitaryWilsonRelativeSelectedDegreeFeature
      N hN beta hbeta m).toPositiveSemidefiniteCertificate

/-- Whenever the selected degree lies inside the truncation, the complete
finite Wilson partial is exactly the selected Hilbert kernel plus the PSD
remainder obtained by erasing that degree. -/
theorem specialUnitaryWilsonRelativeKernelPartial_eq_selected_add_remainder
    (N : ℕ)
    (beta : ℝ)
    (degree selected : ℕ)
    (hselected : selected ≤ degree)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    specialUnitaryWilsonRelativeKernelPartial N beta degree g h =
      specialUnitaryWilsonRelativeSelectedDegreeKernel N beta selected g h +
        specialUnitaryWilsonRelativeKernelPartialSelectedRemainder
          N beta degree selected g h := by
  classical
  have hmem : selected ∈ Finset.range (degree + 1) := by
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hselected)
  have hPartialSum :
      specialUnitaryWilsonRelativeKernelPartial N beta degree g h =
        ∑ m ∈ Finset.range (degree + 1),
          specialUnitaryWilsonRelativeSelectedDegreeKernel N beta m g h := by
    unfold specialUnitaryWilsonRelativeKernelPartial
    rw [RealHilbertKernelFeature.exponentialPartialKernel_eq_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    simp only [specialUnitaryWilsonRelativeSelectedDegreeKernel,
      specialUnitaryWilsonSelectedTaylorCoefficient, mul_pow]
    ring
  rw [hPartialSum]
  calc
    (∑ m ∈ Finset.range (degree + 1),
      specialUnitaryWilsonRelativeSelectedDegreeKernel N beta m g h) =
        (∑ m ∈ (Finset.range (degree + 1)).erase selected,
          specialUnitaryWilsonRelativeSelectedDegreeKernel N beta m g h) +
          specialUnitaryWilsonRelativeSelectedDegreeKernel N beta selected g h := by
      exact (Finset.sum_erase_add (Finset.range (degree + 1)) selected hmem).symm
    _ = specialUnitaryWilsonRelativeSelectedDegreeKernel N beta selected g h +
        specialUnitaryWilsonRelativeKernelPartialSelectedRemainder
          N beta degree selected g h := by
      unfold specialUnitaryWilsonRelativeKernelPartialSelectedRemainder
      ring

/-- Equivalent subtraction form of the finite PSD remainder.  This identity is
used only for limits; the PSD proof itself remains cancellation-free. -/
theorem specialUnitaryWilsonRelativeKernelPartialSelectedRemainder_eq_sub
    (N : ℕ)
    (beta : ℝ)
    (degree selected : ℕ)
    (hselected : selected ≤ degree)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    specialUnitaryWilsonRelativeKernelPartialSelectedRemainder
        N beta degree selected g h =
      specialUnitaryWilsonRelativeKernelPartial N beta degree g h -
        specialUnitaryWilsonRelativeSelectedDegreeKernel N beta selected g h := by
  have hdecomp :=
    specialUnitaryWilsonRelativeKernelPartial_eq_selected_add_remainder
      N beta degree selected hselected g h
  rw [hdecomp]
  ring

end

end MathlibAnalytic
end MGAP4D
