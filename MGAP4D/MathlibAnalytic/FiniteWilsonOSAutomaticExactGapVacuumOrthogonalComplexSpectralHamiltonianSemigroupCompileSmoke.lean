import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalComplexSpectralHamiltonianSemigroup

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped ComplexOrder

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
variable
  (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
variable (n : ℕ)

example :
    D.vacuumOrthogonalComplexSpectralHamiltonianSemigroup n 0 = 1 :=
  finite_wilson_vacuum_orthogonal_complex_spectral_hamiltonianSemigroup_zero D n

example (s t : ℝ) :
    D.vacuumOrthogonalComplexSpectralHamiltonianSemigroup n (s + t) =
      D.vacuumOrthogonalComplexSpectralHamiltonianSemigroup n s *
        D.vacuumOrthogonalComplexSpectralHamiltonianSemigroup n t :=
  finite_wilson_vacuum_orthogonal_complex_spectral_hamiltonianSemigroup_add D n s t

example :
    D.vacuumOrthogonalComplexSpectralHamiltonianSemigroup n 1 =
      D.vacuumOrthogonalComplexSpectralTransferOperator n :=
  finite_wilson_vacuum_orthogonal_complex_spectral_hamiltonianSemigroup_one D n

example (t : ℝ) (i : Fin D.gapData.ExcitedDimension) :
    D.vacuumOrthogonalComplexSpectralHamiltonianSemigroup n t
        (D.vacuumOrthogonalComplexSpectralBasis i) =
      (Real.exp (-(t *
        (finite_wilson_vacuum_orthogonal_restricted_hamiltonian_symmetric
          D.gapData n).eigenvalues D.gapData.excitedFinrank i)) : ℂ) •
        D.vacuumOrthogonalComplexSpectralBasis i :=
  finite_wilson_vacuum_orthogonal_complex_spectral_hamiltonianSemigroup_on_basis
    D n t i

example (t : ℝ) :
    (D.vacuumOrthogonalComplexSpectralHamiltonianSemigroup n t).IsPositive :=
  finite_wilson_vacuum_orthogonal_complex_spectral_hamiltonianSemigroup_isPositive D n t

example (t : ℝ) :
    IsSelfAdjoint (D.vacuumOrthogonalComplexSpectralHamiltonianSemigroup n t) :=
  finite_wilson_vacuum_orthogonal_complex_spectral_hamiltonianSemigroup_isSelfAdjoint D n t

example (t : ℝ) (ht : 0 ≤ t) :
    D.vacuumOrthogonalComplexSpectralHamiltonianSemigroup n t ∈
      Set.Icc
        (0 : D.vacuumOrthogonalComplexSpectralStateSpace →L[ℂ]
          D.vacuumOrthogonalComplexSpectralStateSpace)
        1 :=
  finite_wilson_vacuum_orthogonal_complex_spectral_hamiltonianSemigroup_mem_Icc
    D n t ht

example (t : ℝ) (ht : 0 ≤ t) :
    D.vacuumOrthogonalComplexSpectralHamiltonianSemigroup n t ≤
      algebraMap ℝ
        (D.vacuumOrthogonalComplexSpectralStateSpace →L[ℂ]
          D.vacuumOrthogonalComplexSpectralStateSpace)
        (Real.exp (-(t * exactGapValueReal))) :=
  finite_wilson_vacuum_orthogonal_complex_spectral_hamiltonianSemigroup_le_exactGap_exp
    D n t ht

end

end MathlibAnalytic
end MGAP4D
