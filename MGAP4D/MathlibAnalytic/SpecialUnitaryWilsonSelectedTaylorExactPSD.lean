import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonSelectedTaylorPSD

namespace MGAP4D
namespace MathlibAnalytic

open Filter
open scoped Topology

noncomputable section

/-- Exact one-plaquette Wilson remainder after removing a single selected
Taylor degree. -/
def specialUnitaryWilsonRelativeSelectedRemainderKernel
    (N : ℕ)
    (beta : ℝ)
    (selected : ℕ)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) : ℝ :=
  specialUnitaryWilsonRelativeKernel N beta g h -
    specialUnitaryWilsonRelativeSelectedDegreeKernel N beta selected g h

/-- The finite erased-degree remainders converge pointwise to the exact Wilson
remainder after the same selected Taylor degree is removed. -/
theorem specialUnitaryWilsonRelativeKernelPartialSelectedRemainder_tendsto_exact
    (N : ℕ)
    (beta : ℝ)
    (selected : ℕ)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    Tendsto
      (fun tail =>
        specialUnitaryWilsonRelativeKernelPartialSelectedRemainder
          N beta (tail + selected) selected g h)
      atTop
      (𝓝
        (specialUnitaryWilsonRelativeSelectedRemainderKernel
          N beta selected g h)) := by
  have hProduct :
      Tendsto
        (fun degree => specialUnitaryWilsonRelativeKernelPartial N beta degree g h)
        atTop
        (𝓝 (specialUnitaryWilsonRelativeKernel N beta g h)) :=
    specialUnitaryWilsonRelativeKernelPartial_tendsto N beta g h
  have hBase :
      Tendsto
        (fun degree =>
          specialUnitaryWilsonRelativeKernelPartial N beta degree g h -
            specialUnitaryWilsonRelativeSelectedDegreeKernel N beta selected g h)
        atTop
        (𝓝
          (specialUnitaryWilsonRelativeKernel N beta g h -
            specialUnitaryWilsonRelativeSelectedDegreeKernel N beta selected g h)) :=
    hProduct.sub tendsto_const_nhds
  have hShift :
      Tendsto
        (fun tail =>
          specialUnitaryWilsonRelativeKernelPartial N beta (tail + selected) g h -
            specialUnitaryWilsonRelativeSelectedDegreeKernel N beta selected g h)
        atTop
        (𝓝
          (specialUnitaryWilsonRelativeKernel N beta g h -
            specialUnitaryWilsonRelativeSelectedDegreeKernel N beta selected g h)) := by
    rw [tendsto_add_atTop_iff_nat
      (f := fun degree =>
        specialUnitaryWilsonRelativeKernelPartial N beta degree g h -
          specialUnitaryWilsonRelativeSelectedDegreeKernel N beta selected g h)
      selected]
    exact hBase
  have hfun :
      (fun tail =>
        specialUnitaryWilsonRelativeKernelPartialSelectedRemainder
          N beta (tail + selected) selected g h) =
      (fun tail =>
        specialUnitaryWilsonRelativeKernelPartial N beta (tail + selected) g h -
          specialUnitaryWilsonRelativeSelectedDegreeKernel N beta selected g h) := by
    funext tail
    exact
      specialUnitaryWilsonRelativeKernelPartialSelectedRemainder_eq_sub
        N beta (tail + selected) selected (by omega) g h
  rw [hfun]
  simpa [specialUnitaryWilsonRelativeSelectedRemainderKernel] using hShift

/-- Removing any selected degree from the exact one-plaquette Wilson kernel
leaves a symmetric positive-semidefinite kernel.  This is obtained as the
pointwise closed limit of literal erased-degree finite Taylor sums. -/
noncomputable def specialUnitaryWilsonRelativeSelectedRemainderCertificate
    (N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (selected : ℕ) :
    RealKernelPositiveSemidefiniteCertificate
      (Matrix.specialUnitaryGroup (Fin N) ℂ)
      (specialUnitaryWilsonRelativeSelectedRemainderKernel N beta selected) :=
  RealKernelPositiveSemidefiniteCertificate.pointwiseLimit
    (fun tail =>
      specialUnitaryWilsonRelativeKernelPartialSelectedRemainder_positiveSemidefiniteCertificate
        N hN beta hbeta (tail + selected) selected)
    (specialUnitaryWilsonRelativeKernelPartialSelectedRemainder_tendsto_exact
      N beta selected)

/-- Exact one-plaquette Wilson decomposition into a selected Taylor Hilbert
sector and its exact PSD complement. -/
theorem specialUnitaryWilsonRelativeKernel_eq_selectedRemainder_add_selectedDegree
    (N : ℕ)
    (beta : ℝ)
    (selected : ℕ)
    (g h : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    specialUnitaryWilsonRelativeKernel N beta g h =
      specialUnitaryWilsonRelativeSelectedRemainderKernel N beta selected g h +
        specialUnitaryWilsonRelativeSelectedDegreeKernel N beta selected g h := by
  unfold specialUnitaryWilsonRelativeSelectedRemainderKernel
  ring

end

end MathlibAnalytic
end MGAP4D
