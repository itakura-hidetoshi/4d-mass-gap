import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedComplexSpectralHamiltonianSemigroupContinuity
import MGAP4D.MathlibAnalytic.OrthonormalComplexDiagonalHamiltonianSemigroupGenerator
import Mathlib.Analysis.Complex.Basic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance euclideanComplexContinuousSMulReal
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

/-- On every constructed complex spectral state, the strong derivative at time
zero is the negative explicit Hamiltonian action. -/
theorem finite_wilson_constructed_complex_spectral_hamiltonianSemigroup_hasDerivAt_zero
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (x : EuclideanSpace ℂ (Fin D.StateDimension)) :
    HasDerivAt
      (fun t : ℝ =>
        (D.complexSpectralHamiltonianSemigroup n t x :
          EuclideanSpace ℂ (Fin D.StateDimension)))
      ((-(D.complexSpectralHamiltonian n x)) :
        EuclideanSpace ℂ (Fin D.StateDimension)) 0 := by
  unfold FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.complexSpectralHamiltonianSemigroup
  unfold FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.complexSpectralHamiltonian
  exact orthonormalComplexDiagonalHamiltonianSemigroup_hasDerivAt_zero
    D.complexSpectralBasis
    (fun i => (D.hamiltonianSymmetric n).eigenvalues D.stateFinrank i)
    x

/-- The constructed semigroup generator is the negative canonical logarithmic
Hamiltonian on every complex spectral state. -/
theorem finite_wilson_constructed_complex_spectral_hamiltonianSemigroup_hasDerivAt_zero_logHamiltonian
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (x : EuclideanSpace ℂ (Fin D.StateDimension)) :
    HasDerivAt
      (fun t : ℝ =>
        (D.complexSpectralHamiltonianSemigroup n t x :
          EuclideanSpace ℂ (Fin D.StateDimension)))
      ((-(D.complexSpectralLogHamiltonian n x)) :
        EuclideanSpace ℂ (Fin D.StateDimension)) 0 := by
  rw [finite_wilson_constructed_complex_spectral_logHamiltonian_eq_hamiltonian D n]
  exact finite_wilson_constructed_complex_spectral_hamiltonianSemigroup_hasDerivAt_zero
    D n x

/-- Ordinary derivative form of the constructed generator identity. -/
theorem finite_wilson_constructed_complex_spectral_hamiltonianSemigroup_deriv_zero
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (x : EuclideanSpace ℂ (Fin D.StateDimension)) :
    deriv
        (fun t : ℝ =>
          (D.complexSpectralHamiltonianSemigroup n t x :
            EuclideanSpace ℂ (Fin D.StateDimension)))
        0 =
      ((-(D.complexSpectralLogHamiltonian n x)) :
        EuclideanSpace ℂ (Fin D.StateDimension)) :=
  (finite_wilson_constructed_complex_spectral_hamiltonianSemigroup_hasDerivAt_zero_logHamiltonian
    D n x).deriv

end

end MathlibAnalytic
end MGAP4D
