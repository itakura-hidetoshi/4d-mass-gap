import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedComplexSpectralLogHamiltonianEigenaction
import MGAP4D.MathlibAnalytic.OrthonormalComplexDiagonalHamiltonianSemigroup

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open scoped ComplexOrder

/-- The explicit continuous-time Hamiltonian semigroup on the constructed
complex spectral realization. -/
noncomputable def
    FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.complexSpectralHamiltonianSemigroup
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t : ℝ) :
    D.complexSpectralStateSpace →L[ℂ] D.complexSpectralStateSpace :=
  orthonormalComplexDiagonalHamiltonianSemigroup D.complexSpectralBasis
    (fun i => (D.hamiltonianSymmetric n).eigenvalues D.stateFinrank i) t

/-- Time zero is the identity on the constructed complex spectral space. -/
@[simp]
theorem finite_wilson_constructed_complex_spectral_hamiltonianSemigroup_zero
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    D.complexSpectralHamiltonianSemigroup n 0 = 1 := by
  unfold FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.complexSpectralHamiltonianSemigroup
  exact orthonormalComplexDiagonalHamiltonianSemigroup_zero _ _

/-- The constructed complex spectral time slices satisfy the semigroup law. -/
theorem finite_wilson_constructed_complex_spectral_hamiltonianSemigroup_add
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (s t : ℝ) :
    D.complexSpectralHamiltonianSemigroup n (s + t) =
      D.complexSpectralHamiltonianSemigroup n s *
        D.complexSpectralHamiltonianSemigroup n t := by
  unfold FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.complexSpectralHamiltonianSemigroup
  exact orthonormalComplexDiagonalHamiltonianSemigroup_add _ _ s t

/-- Time one recovers the constructed complex spectral transfer operator. -/
theorem finite_wilson_constructed_complex_spectral_hamiltonianSemigroup_one
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    D.complexSpectralHamiltonianSemigroup n 1 =
      D.complexSpectralTransferOperator n := by
  unfold FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.complexSpectralHamiltonianSemigroup
  unfold FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.complexSpectralTransferOperator
  exact orthonormalComplexDiagonalHamiltonianSemigroup_one _ _

/-- The constructed semigroup is the exponential of the negative scaled
explicit Hamiltonian. -/
theorem finite_wilson_constructed_complex_spectral_exp_neg_scaled_hamiltonian
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t : ℝ) :
    NormedSpace.exp
        (-orthonormalComplexDiagonalOperator D.complexSpectralBasis
          (fun i => t * (D.hamiltonianSymmetric n).eigenvalues D.stateFinrank i)) =
      D.complexSpectralHamiltonianSemigroup n t := by
  unfold FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.complexSpectralHamiltonianSemigroup
  exact normedSpace_exp_neg_scaled_orthonormalComplexDiagonalOperator _ _ t

/-- The constructed semigroup acts modewise by `exp (-tEᵢ)`. -/
theorem finite_wilson_constructed_complex_spectral_hamiltonianSemigroup_on_basis
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t : ℝ)
    (i : Fin D.StateDimension) :
    D.complexSpectralHamiltonianSemigroup n t (D.complexSpectralBasis i) =
      (Real.exp (-(t * (D.hamiltonianSymmetric n).eigenvalues D.stateFinrank i)) : ℂ) •
        D.complexSpectralBasis i := by
  unfold FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.complexSpectralHamiltonianSemigroup
  exact orthonormalComplexDiagonalHamiltonianSemigroup_apply_basis _ _ t i

/-- Every constructed complex spectral time slice is positive. -/
theorem finite_wilson_constructed_complex_spectral_hamiltonianSemigroup_isPositive
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t : ℝ) :
    (D.complexSpectralHamiltonianSemigroup n t).IsPositive := by
  unfold FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.complexSpectralHamiltonianSemigroup
  exact orthonormalComplexDiagonalHamiltonianSemigroup_isPositive _ _ t

/-- Every constructed complex spectral time slice is self-adjoint. -/
theorem finite_wilson_constructed_complex_spectral_hamiltonianSemigroup_isSelfAdjoint
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t : ℝ) :
    IsSelfAdjoint (D.complexSpectralHamiltonianSemigroup n t) :=
  (finite_wilson_constructed_complex_spectral_hamiltonianSemigroup_isPositive D n t).isSelfAdjoint

/-- At nonnegative time the constructed complex spectral time slice lies below
the identity. -/
theorem finite_wilson_constructed_complex_spectral_hamiltonianSemigroup_le_one
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t : ℝ)
    (ht : 0 ≤ t) :
    D.complexSpectralHamiltonianSemigroup n t ≤ 1 := by
  unfold FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.complexSpectralHamiltonianSemigroup
  exact orthonormalComplexDiagonalHamiltonianSemigroup_le_one _ _
    (finite_wilson_constructed_complex_spectral_hamiltonian_eigenvalue_nonneg D n)
    t ht

/-- At nonnegative time the constructed complex spectral time slice belongs to
`[0,I]`. -/
theorem finite_wilson_constructed_complex_spectral_hamiltonianSemigroup_mem_Icc
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t : ℝ)
    (ht : 0 ≤ t) :
    D.complexSpectralHamiltonianSemigroup n t ∈
      Set.Icc (0 : D.complexSpectralStateSpace →L[ℂ] D.complexSpectralStateSpace) 1 :=
  ⟨(ContinuousLinearMap.nonneg_iff_isPositive
      (D.complexSpectralHamiltonianSemigroup n t)).2
        (finite_wilson_constructed_complex_spectral_hamiltonianSemigroup_isPositive D n t),
    finite_wilson_constructed_complex_spectral_hamiltonianSemigroup_le_one D n t ht⟩

/-- The constructed exact Hamiltonian gap gives exponential semigroup decay. -/
theorem finite_wilson_constructed_complex_spectral_hamiltonianSemigroup_le_exactGap_exp
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (t : ℝ)
    (ht : 0 ≤ t) :
    D.complexSpectralHamiltonianSemigroup n t ≤
      algebraMap ℝ
        (D.complexSpectralStateSpace →L[ℂ] D.complexSpectralStateSpace)
        (Real.exp (-(t * exactGapValueReal))) := by
  unfold FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.complexSpectralHamiltonianSemigroup
  exact orthonormalComplexDiagonalHamiltonianSemigroup_le_exp_neg_lowerBound
    D.complexSpectralBasis
    (fun i => (D.hamiltonianSymmetric n).eigenvalues D.stateFinrank i)
    exactGapValueReal
    (D.hamiltonianEigenvalues_ge_exactGap n)
    t ht

end

end MathlibAnalytic
end MGAP4D
