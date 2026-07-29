import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedComplexSpectralHamiltonianSemigroupGenerator
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalComplexSpectralHamiltonianSemigroupContinuity
import Mathlib.Analysis.Complex.Basic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance vacuumEuclideanComplexContinuousSMulReal
    {ι : Type*}
    [Fintype ι] :
    ContinuousSMul ℝ (EuclideanSpace ℂ ι) where
  continuous_smul := by
    have hcoe : Continuous
        (fun p : ℝ × EuclideanSpace ℂ ι => (p.1 : ℂ) • p.2) :=
      (Complex.continuous_ofReal.comp
        (continuous_fst : Continuous
          (fun p : ℝ × EuclideanSpace ℂ ι => p.1))).smul
            (continuous_snd : Continuous
              (fun p : ℝ × EuclideanSpace ℂ ι => p.2))
    simpa only [Complex.coe_smul] using hcoe

/-- On every vacuum-orthogonal complex spectral excitation state, the strong
derivative at time zero is the negative explicit Hamiltonian action. -/
theorem finite_wilson_vacuum_orthogonal_complex_spectral_hamiltonianSemigroup_hasDerivAt_zero
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (x : EuclideanSpace ℂ (Fin D.gapData.ExcitedDimension)) :
    HasDerivAt
      (fun t : ℝ =>
        (D.vacuumOrthogonalComplexSpectralHamiltonianSemigroup n t x :
          EuclideanSpace ℂ (Fin D.gapData.ExcitedDimension)))
      ((-(D.vacuumOrthogonalComplexSpectralHamiltonian n x)) :
        EuclideanSpace ℂ (Fin D.gapData.ExcitedDimension)) 0 :=
  finite_wilson_constructed_complex_spectral_hamiltonianSemigroup_hasDerivAt_zero
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n x

/-- The vacuum-orthogonal complex spectral semigroup generator is the negative
canonical logarithmic Hamiltonian, with no new assumption on the vacuum line. -/
theorem finite_wilson_vacuum_orthogonal_complex_spectral_hamiltonianSemigroup_hasDerivAt_zero_logHamiltonian
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (x : EuclideanSpace ℂ (Fin D.gapData.ExcitedDimension)) :
    HasDerivAt
      (fun t : ℝ =>
        (D.vacuumOrthogonalComplexSpectralHamiltonianSemigroup n t x :
          EuclideanSpace ℂ (Fin D.gapData.ExcitedDimension)))
      ((-(D.vacuumOrthogonalComplexSpectralLogHamiltonian n x)) :
        EuclideanSpace ℂ (Fin D.gapData.ExcitedDimension)) 0 :=
  finite_wilson_constructed_complex_spectral_hamiltonianSemigroup_hasDerivAt_zero_logHamiltonian
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n x

/-- Ordinary derivative form of the physical excitation-sector generator
identity. -/
theorem finite_wilson_vacuum_orthogonal_complex_spectral_hamiltonianSemigroup_deriv_zero
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (x : EuclideanSpace ℂ (Fin D.gapData.ExcitedDimension)) :
    deriv
        (fun t : ℝ =>
          (D.vacuumOrthogonalComplexSpectralHamiltonianSemigroup n t x :
            EuclideanSpace ℂ (Fin D.gapData.ExcitedDimension)))
        0 =
      ((-(D.vacuumOrthogonalComplexSpectralLogHamiltonian n x)) :
        EuclideanSpace ℂ (Fin D.gapData.ExcitedDimension)) :=
  (finite_wilson_vacuum_orthogonal_complex_spectral_hamiltonianSemigroup_hasDerivAt_zero_logHamiltonian
    D n x).deriv

end

end MathlibAnalytic
end MGAP4D
