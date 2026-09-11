import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianResolventNormBundle
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalRealSpectralHamiltonianSemigroupOperatorAsymptoticIncrementalSteadyBiasBundle

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The shifted finite Wilson Hamiltonian restricted to `Ω⊥`. -/
noncomputable def finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianShiftedOperator
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (lambda : ℝ) :
    D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace :=
  finite_wilson_constructed_real_spectral_hamiltonianShiftedOperator
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n lambda

/-- The real resolvent of the finite Wilson Hamiltonian on `Ω⊥`. -/
noncomputable def finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (lambda : ℝ) :
    D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace :=
  finite_wilson_constructed_real_spectral_hamiltonianResolvent
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n lambda

/-- Below the exact gap, the `Ω⊥` resolvent is a left inverse. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_mul_shiftedOperator
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (lambda : ℝ) (hlambda : lambda < exactGapValueReal) :
    finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda *
        finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianShiftedOperator D n lambda = 1 := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_mul_shiftedOperator
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n lambda hlambda

/-- Below the exact gap, the `Ω⊥` resolvent is also a right inverse. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianShiftedOperator_mul_resolvent
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (lambda : ℝ) (hlambda : lambda < exactGapValueReal) :
    finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianShiftedOperator D n lambda *
        finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda = 1 := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianShiftedOperator_mul_resolvent
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n lambda hlambda

/-- Exact reciprocal distance-to-gap bound on `Ω⊥`. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_norm_le
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (lambda : ℝ) (hlambda : lambda < exactGapValueReal) :
    ‖finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda‖ ≤
      (exactGapValueReal - lambda)⁻¹ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_norm_le
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n lambda hlambda

/-- Pointwise `Ω⊥` resolvent control. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_apply_norm_le
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (lambda : ℝ) (hlambda : lambda < exactGapValueReal)
    (x : D.gapData.ExcitedStateSpace) :
    ‖finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda x‖ ≤
      (exactGapValueReal - lambda)⁻¹ * ‖x‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_apply_norm_le
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n lambda hlambda x

/-- Left `Ω⊥` resolvent response bound. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_mul_norm_le
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (lambda : ℝ) (hlambda : lambda < exactGapValueReal)
    (Q : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace) :
    ‖finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda * Q‖ ≤
      (exactGapValueReal - lambda)⁻¹ * ‖Q‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_mul_norm_le
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n lambda hlambda Q

/-- Right `Ω⊥` resolvent response bound, without commutation. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonian_mul_resolvent_norm_le
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) (lambda : ℝ) (hlambda : lambda < exactGapValueReal)
    (Q : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace) :
    ‖Q * finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda‖ ≤
      (exactGapValueReal - lambda)⁻¹ * ‖Q‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonian_mul_resolvent_norm_le
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n lambda hlambda Q

@[simp]
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_zero
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n 0 =
      finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianInverse D n := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_zero
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

/-- The `Ω⊥` Hamiltonian inverse has reciprocal exact-gap norm. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianInverse_norm_le
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    ‖finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianInverse D n‖ ≤
      exactGapValueReal⁻¹ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianInverse_norm_le
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

/-- The left `Ω⊥` steady response has reciprocal exact-gap gain. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseLeft_norm_le
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (Qinf : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace) :
    ‖finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseLeft D n Qinf‖ ≤
      exactGapValueReal⁻¹ * ‖Qinf‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseLeft_norm_le
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n Qinf

/-- The right `Ω⊥` steady response has the same gain without commutation. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseRight_norm_le
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (Qinf : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace) :
    ‖finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseRight D n Qinf‖ ≤
      exactGapValueReal⁻¹ * ‖Qinf‖ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseRight_norm_le
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n Qinf

/-- Every left equilibrium on `Ω⊥` is the exact inverse-Hamiltonian response. -/
theorem eq_finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseLeft_of_equilibrium
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (Qinf X : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (hX : LinearMap.toContinuousLinearMap (D.gapData.restrictedHamiltonian n) * X = Qinf) :
    X = finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseLeft D n Qinf := by
  exact
    eq_finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseLeft_of_equilibrium
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n Qinf X hX

/-- Every right equilibrium on `Ω⊥` is `Qinf H⁻¹`, without commutation. -/
theorem eq_finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseRight_of_equilibrium
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (Qinf X : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
    (hX : X * LinearMap.toContinuousLinearMap (D.gapData.restrictedHamiltonian n) = Qinf) :
    X = finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseRight D n Qinf := by
  exact
    eq_finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseRight_of_equilibrium
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n Qinf X hX

end

end MathlibAnalytic
end MGAP4D
