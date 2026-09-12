import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedComplexSpectralHamiltonianSemigroup
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalComplexSpectralLogHamiltonianEigenaction

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped ComplexOrder

/-- The continuous-time complex spectral Hamiltonian semigroup on the physical
vacuum-orthogonal excitation sector `Ω⊥`. -/
noncomputable def
    FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData.vacuumOrthogonalComplexSpectralHamiltonianSemigroup
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (t : ℝ) :
    D.vacuumOrthogonalComplexSpectralStateSpace →L[ℂ]
      D.vacuumOrthogonalComplexSpectralStateSpace :=
  D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData.complexSpectralHamiltonianSemigroup n t

/-- Time zero is the identity on the vacuum-orthogonal complex spectral sector. -/
@[simp]
theorem finite_wilson_vacuum_orthogonal_complex_spectral_hamiltonianSemigroup_zero
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    D.vacuumOrthogonalComplexSpectralHamiltonianSemigroup n 0 = 1 :=
  finite_wilson_constructed_complex_spectral_hamiltonianSemigroup_zero
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

/-- The vacuum-orthogonal complex spectral time slices satisfy the semigroup law. -/
theorem finite_wilson_vacuum_orthogonal_complex_spectral_hamiltonianSemigroup_add
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (s t : ℝ) :
    D.vacuumOrthogonalComplexSpectralHamiltonianSemigroup n (s + t) =
      D.vacuumOrthogonalComplexSpectralHamiltonianSemigroup n s *
        D.vacuumOrthogonalComplexSpectralHamiltonianSemigroup n t :=
  finite_wilson_constructed_complex_spectral_hamiltonianSemigroup_add
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n s t

/-- Time one recovers the vacuum-orthogonal complex spectral transfer operator. -/
theorem finite_wilson_vacuum_orthogonal_complex_spectral_hamiltonianSemigroup_one
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    D.vacuumOrthogonalComplexSpectralHamiltonianSemigroup n 1 =
      D.vacuumOrthogonalComplexSpectralTransferOperator n :=
  finite_wilson_constructed_complex_spectral_hamiltonianSemigroup_one
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

/-- The vacuum-orthogonal semigroup acts modewise by the restricted energy
factor `exp (-tEᵢ)`. -/
theorem finite_wilson_vacuum_orthogonal_complex_spectral_hamiltonianSemigroup_on_basis
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (t : ℝ)
    (i : Fin D.gapData.ExcitedDimension) :
    D.vacuumOrthogonalComplexSpectralHamiltonianSemigroup n t
        (D.vacuumOrthogonalComplexSpectralBasis i) =
      (Real.exp (-(t *
        (finite_wilson_vacuum_orthogonal_restricted_hamiltonian_symmetric
          D.gapData n).eigenvalues D.gapData.excitedFinrank i)) : ℂ) •
        D.vacuumOrthogonalComplexSpectralBasis i :=
  finite_wilson_constructed_complex_spectral_hamiltonianSemigroup_on_basis
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n t i

/-- Every vacuum-orthogonal complex spectral time slice is positive. -/
theorem finite_wilson_vacuum_orthogonal_complex_spectral_hamiltonianSemigroup_isPositive
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (t : ℝ) :
    (D.vacuumOrthogonalComplexSpectralHamiltonianSemigroup n t).IsPositive :=
  finite_wilson_constructed_complex_spectral_hamiltonianSemigroup_isPositive
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n t

/-- Every vacuum-orthogonal complex spectral time slice is self-adjoint. -/
theorem finite_wilson_vacuum_orthogonal_complex_spectral_hamiltonianSemigroup_isSelfAdjoint
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (t : ℝ) :
    IsSelfAdjoint (D.vacuumOrthogonalComplexSpectralHamiltonianSemigroup n t) :=
  finite_wilson_constructed_complex_spectral_hamiltonianSemigroup_isSelfAdjoint
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n t

/-- At nonnegative time the vacuum-orthogonal complex spectral time slice lies
below the identity. -/
theorem finite_wilson_vacuum_orthogonal_complex_spectral_hamiltonianSemigroup_le_one
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (t : ℝ)
    (ht : 0 ≤ t) :
    D.vacuumOrthogonalComplexSpectralHamiltonianSemigroup n t ≤ 1 :=
  finite_wilson_constructed_complex_spectral_hamiltonianSemigroup_le_one
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n t ht

/-- At nonnegative time the vacuum-orthogonal complex spectral time slice lies
in `[0,I]`. -/
theorem finite_wilson_vacuum_orthogonal_complex_spectral_hamiltonianSemigroup_mem_Icc
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (t : ℝ)
    (ht : 0 ≤ t) :
    D.vacuumOrthogonalComplexSpectralHamiltonianSemigroup n t ∈
      Set.Icc
        (0 : D.vacuumOrthogonalComplexSpectralStateSpace →L[ℂ]
          D.vacuumOrthogonalComplexSpectralStateSpace)
        1 :=
  finite_wilson_constructed_complex_spectral_hamiltonianSemigroup_mem_Icc
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n t ht

/-- The physical excitation exact gap gives the exponential decay estimate
`Sₜ ≤ exp (-tδ) I`, without imposing a positive bound on the vacuum line. -/
theorem finite_wilson_vacuum_orthogonal_complex_spectral_hamiltonianSemigroup_le_exactGap_exp
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (t : ℝ)
    (ht : 0 ≤ t) :
    D.vacuumOrthogonalComplexSpectralHamiltonianSemigroup n t ≤
      algebraMap ℝ
        (D.vacuumOrthogonalComplexSpectralStateSpace →L[ℂ]
          D.vacuumOrthogonalComplexSpectralStateSpace)
        (Real.exp (-(t * exactGapValueReal))) :=
  finite_wilson_constructed_complex_spectral_hamiltonianSemigroup_le_exactGap_exp
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n t ht

end

end MathlibAnalytic
end MGAP4D
