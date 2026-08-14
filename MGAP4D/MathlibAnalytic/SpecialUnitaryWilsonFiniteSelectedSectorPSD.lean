import MGAP4D.MathlibAnalytic.RealKernelPositiveSemidefiniteCertificateFiniteProduct
import MGAP4D.MathlibAnalytic.SpecialUnitaryWilsonKernelPositiveSemidefiniteCertificate
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
    {ι : Type}
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
  let X : Type := ι → Matrix.specialUnitaryGroup (Fin N) ℂ
  let full : ι → X → X → ℝ := fun i u v =>
    specialUnitaryWilsonRelativeKernel N beta (u i) (v i)
  let selected : ι → X → X → ℝ := fun i u v =>
    specialUnitaryWilsonRelativeSelectedDegreeKernel
      N beta (degree i) (u i) (v i)
  have Cfull : ∀ i ∈ s,
      RealKernelPositiveSemidefiniteCertificate X (full i) := by
    intro i _hi
    have Cbase :=
      specialUnitaryWilsonRelativeKernel_positiveSemidefiniteCertificate
        N hN beta hbeta
    simpa [X, full] using
      Cbase.comap (fun u : X => u i)
  have Cselected : ∀ i ∈ s,
      RealKernelPositiveSemidefiniteCertificate X (selected i) := by
    intro i _hi
    have Cbase :=
      (specialUnitaryWilsonRelativeSelectedDegreeFeature
        N hN beta hbeta (degree i)).toPositiveSemidefiniteCertificate
    simpa [X, selected] using
      Cbase.comap (fun u : X => u i)
  have Cremainder : ∀ i ∈ s,
      RealKernelPositiveSemidefiniteCertificate X
        (fun u v => full i u v - selected i u v) := by
    intro i _hi
    have Cbase :=
      specialUnitaryWilsonRelativeSelectedRemainderCertificate
        N hN beta hbeta (degree i)
    have Cpull := Cbase.comap (fun u : X => u i)
    simpa [X, full, selected,
      specialUnitaryWilsonRelativeSelectedRemainderKernel] using Cpull
  have Cprod :=
    RealKernelPositiveSemidefiniteCertificate.finsetProd_sub_finsetProd
      s full selected Cfull Cselected Cremainder
  simpa [X, full, selected] using Cprod

/-- Pointwise exact decomposition corresponding to the finite-product PSD
certificate: the full product is the selected product plus its exact Schur-PSD
complement. -/
theorem specialUnitaryWilsonRelativeKernel_finsetProd_eq_remainder_add_selectedDegreeProd
    {ι : Type}
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
