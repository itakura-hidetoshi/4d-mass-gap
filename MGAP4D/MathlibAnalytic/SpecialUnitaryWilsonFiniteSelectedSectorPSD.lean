import MGAP4D.MathlibAnalytic.RealKernelPositiveSemidefiniteCertificateFiniteProduct
import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonKernelRKHSFeature
import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonSelectedTaylorExactPSD

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Finite-product selected-sector domination for the exact Wilson relative
kernel.  Each factor may select its own Taylor degree.  The full finite Schur
product minus the product of all selected degree sectors is symmetric positive
semidefinite.

The proof uses only the one-plaquette exact PSD remainder and the generic
finite Schur-product telescoping theorem; no multi-degree contribution is
discarded. -/
theorem specialUnitaryWilsonRelativeKernel_finsetProd_sub_selectedDegreeProd_positiveSemidefiniteCertificate
    {ι : Type*}
    (N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (s : Finset ι)
    (degree : ι → ℕ) :
    RealKernelPositiveSemidefiniteCertificate
      (ι → Matrix.specialUnitaryGroup (Fin N) ℂ)
      (fun u v =>
        (∏ i ∈ s,
          specialUnitaryWilsonRelativeKernel N beta (u i) (v i)) -
        ∏ i ∈ s,
          specialUnitaryWilsonRelativeSelectedDegreeKernel
            N beta (degree i) (u i) (v i)) := by
  classical
  refine RealKernelPositiveSemidefiniteCertificate.finsetProd_sub_finsetProd
    s
    (fun i u v => specialUnitaryWilsonRelativeKernel N beta (u i) (v i))
    (fun i u v =>
      specialUnitaryWilsonRelativeSelectedDegreeKernel
        N beta (degree i) (u i) (v i)) ?_ ?_ ?_
  · intro i _hi
    exact
      ((specialUnitaryWilsonRelativeKernelFeature N hN beta hbeta).comap
        (fun u : ι → Matrix.specialUnitaryGroup (Fin N) ℂ => u i)).toPositiveSemidefiniteCertificate
  · intro i _hi
    exact
      ((specialUnitaryWilsonRelativeSelectedDegreeFeature
          N hN beta hbeta (degree i)).comap
        (fun u : ι → Matrix.specialUnitaryGroup (Fin N) ℂ => u i)).toPositiveSemidefiniteCertificate
  · intro i _hi
    simpa [specialUnitaryWilsonRelativeSelectedRemainderKernel] using
      (specialUnitaryWilsonRelativeSelectedRemainderCertificate
        N hN beta hbeta (degree i)).comap
          (fun u : ι → Matrix.specialUnitaryGroup (Fin N) ℂ => u i)

/-- Pointwise exact decomposition corresponding to the finite-product PSD
certificate: the full product is the selected product plus its exact Schur-PSD
complement. -/
theorem specialUnitaryWilsonRelativeKernel_finsetProd_eq_remainder_add_selectedDegreeProd
    {ι : Type*}
    (N : ℕ)
    (beta : ℝ)
    (s : Finset ι)
    (degree : ι → ℕ)
    (u v : ι → Matrix.specialUnitaryGroup (Fin N) ℂ) :
    (∏ i ∈ s,
      specialUnitaryWilsonRelativeKernel N beta (u i) (v i)) =
      ((∏ i ∈ s,
          specialUnitaryWilsonRelativeKernel N beta (u i) (v i)) -
        ∏ i ∈ s,
          specialUnitaryWilsonRelativeSelectedDegreeKernel
            N beta (degree i) (u i) (v i)) +
      ∏ i ∈ s,
        specialUnitaryWilsonRelativeSelectedDegreeKernel
          N beta (degree i) (u i) (v i) := by
  ring

end

end MathlibAnalytic
end MGAP4D
