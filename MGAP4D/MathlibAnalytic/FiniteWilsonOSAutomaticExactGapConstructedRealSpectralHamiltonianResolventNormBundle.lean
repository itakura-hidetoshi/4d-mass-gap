import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianResolventNormBundle
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorAsymptoticIncrementalSteadyBiasBundle

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The actual shifted constructed finite Wilson Hamiltonian `Hₙ - λI`. -/
noncomputable def finite_wilson_constructed_real_spectral_hamiltonianShiftedOperator
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (lambda : ℝ) : D.StateSpace →L[ℝ] D.StateSpace :=
  LinearMap.toContinuousLinearMap (D.hamiltonian n) -
    lambda • (1 : D.StateSpace →L[ℝ] D.StateSpace)

/-- The real resolvent of the constructed finite Wilson Hamiltonian. -/
noncomputable def finite_wilson_constructed_real_spectral_hamiltonianResolvent
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (lambda : ℝ) : D.StateSpace →L[ℝ] D.StateSpace :=
  orthonormalDiagonalHamiltonianResolvent
    ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
    ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
    lambda

/-- The eigenbasis shift agrees with the actual constructed Hamiltonian shift. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianShiftedOperator_diagonal_eq
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (lambda : ℝ) :
    orthonormalDiagonalHamiltonianShiftedOperator
        ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
        ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
        lambda =
      finite_wilson_constructed_real_spectral_hamiltonianShiftedOperator
        D n lambda := by
  simpa [finite_wilson_constructed_real_spectral_hamiltonianShiftedOperator,
    finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n] using
    (orthonormalDiagonalHamiltonianShiftedOperator_eq_sub_smul_id
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      lambda)

/-- Below the exact gap, the constructed resolvent is a left inverse. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_mul_shiftedOperator
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (lambda : ℝ) (hlambda : lambda < exactGapValueReal) :
    finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda *
        finite_wilson_constructed_real_spectral_hamiltonianShiftedOperator D n lambda = 1 := by
  simpa [finite_wilson_constructed_real_spectral_hamiltonianResolvent,
    finite_wilson_constructed_real_spectral_hamiltonianShiftedOperator,
    orthonormalDiagonalHamiltonianShiftedOperator_eq_sub_smul_id,
    finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n] using
    (orthonormalDiagonalHamiltonianResolvent_mul_shiftedOperator
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal lambda
      (D.hamiltonianEigenvalues_ge_exactGap n) hlambda)

/-- Below the exact gap, the constructed resolvent is also a right inverse. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianShiftedOperator_mul_resolvent
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (lambda : ℝ) (hlambda : lambda < exactGapValueReal) :
    finite_wilson_constructed_real_spectral_hamiltonianShiftedOperator D n lambda *
        finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda = 1 := by
  simpa [finite_wilson_constructed_real_spectral_hamiltonianResolvent,
    finite_wilson_constructed_real_spectral_hamiltonianShiftedOperator,
    orthonormalDiagonalHamiltonianShiftedOperator_eq_sub_smul_id,
    finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n] using
    (orthonormalDiagonalHamiltonianShiftedOperator_mul_resolvent
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal lambda
      (D.hamiltonianEigenvalues_ge_exactGap n) hlambda)

/-- Exact reciprocal distance-to-gap norm bound for the constructed resolvent. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_norm_le
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (lambda : ℝ) (hlambda : lambda < exactGapValueReal) :
    ‖finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda‖ ≤
      (exactGapValueReal - lambda)⁻¹ := by
  exact
    orthonormalDiagonalHamiltonianResolvent_norm_le_inv_sub
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal lambda
      (D.hamiltonianEigenvalues_ge_exactGap n) hlambda

/-- Pointwise constructed resolvent control. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_apply_norm_le
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (lambda : ℝ) (hlambda : lambda < exactGapValueReal)
    (x : D.StateSpace) :
    ‖finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda x‖ ≤
      (exactGapValueReal - lambda)⁻¹ * ‖x‖ := by
  exact
    orthonormalDiagonalHamiltonianResolvent_apply_norm_le
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal lambda
      (D.hamiltonianEigenvalues_ge_exactGap n) hlambda x

/-- Left constructed resolvent response bound. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_mul_norm_le
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (lambda : ℝ) (hlambda : lambda < exactGapValueReal)
    (Q : D.StateSpace →L[ℝ] D.StateSpace) :
    ‖finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda * Q‖ ≤
      (exactGapValueReal - lambda)⁻¹ * ‖Q‖ := by
  exact
    orthonormalDiagonalHamiltonianResolvent_mul_norm_le
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal lambda
      (D.hamiltonianEigenvalues_ge_exactGap n) hlambda Q

/-- Right constructed resolvent response bound, without commutation. -/
theorem finite_wilson_constructed_real_spectral_hamiltonian_mul_resolvent_norm_le
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (lambda : ℝ) (hlambda : lambda < exactGapValueReal)
    (Q : D.StateSpace →L[ℝ] D.StateSpace) :
    ‖Q * finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda‖ ≤
      (exactGapValueReal - lambda)⁻¹ * ‖Q‖ := by
  exact
    orthonormalDiagonalHamiltonian_mul_resolvent_norm_le
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal lambda
      (D.hamiltonianEigenvalues_ge_exactGap n) hlambda Q

@[simp]
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_zero
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    finite_wilson_constructed_real_spectral_hamiltonianResolvent D n 0 =
      finite_wilson_constructed_real_spectral_hamiltonianInverse D n := by
  simp [finite_wilson_constructed_real_spectral_hamiltonianResolvent,
    finite_wilson_constructed_real_spectral_hamiltonianInverse]

/-- The constructed Hamiltonian inverse has reciprocal exact-gap norm. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianInverse_norm_le
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    ‖finite_wilson_constructed_real_spectral_hamiltonianInverse D n‖ ≤
      exactGapValueReal⁻¹ := by
  exact
    orthonormalDiagonalHamiltonianInverse_norm_le_inv
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos

/-- Constructed left steady response has reciprocal exact-gap gain. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseLeft_norm_le
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (Qinf : D.StateSpace →L[ℝ] D.StateSpace) :
    ‖finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseLeft D n Qinf‖ ≤
      exactGapValueReal⁻¹ * ‖Qinf‖ := by
  exact
    orthonormalDiagonalHamiltonianSteadyResponseLeft_norm_le
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos Qinf

/-- Constructed right steady response has the same gain without commutation. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseRight_norm_le
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (Qinf : D.StateSpace →L[ℝ] D.StateSpace) :
    ‖finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseRight D n Qinf‖ ≤
      exactGapValueReal⁻¹ * ‖Qinf‖ := by
  exact
    orthonormalDiagonalHamiltonianSteadyResponseRight_norm_le
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos Qinf

/-- Every constructed left equilibrium is the exact inverse-Hamiltonian response. -/
theorem eq_finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseLeft_of_equilibrium
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (Qinf X : D.StateSpace →L[ℝ] D.StateSpace)
    (hX : LinearMap.toContinuousLinearMap (D.hamiltonian n) * X = Qinf) :
    X = finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseLeft D n Qinf := by
  simpa [finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseLeft,
    finite_wilson_constructed_real_spectral_hamiltonianInverse,
    finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n] using
    (eq_orthonormalDiagonalHamiltonianSteadyResponseLeft_of_equilibrium
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos Qinf X hX)

/-- Every constructed right equilibrium is `Qinf H⁻¹`, without commutation. -/
theorem eq_finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseRight_of_equilibrium
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (Qinf X : D.StateSpace →L[ℝ] D.StateSpace)
    (hX : X * LinearMap.toContinuousLinearMap (D.hamiltonian n) = Qinf) :
    X = finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseRight D n Qinf := by
  simpa [finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseRight,
    finite_wilson_constructed_real_spectral_hamiltonianInverse,
    finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n] using
    (eq_orthonormalDiagonalHamiltonianSteadyResponseRight_of_equilibrium
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos Qinf X hX)

end

end MathlibAnalytic
end MGAP4D
