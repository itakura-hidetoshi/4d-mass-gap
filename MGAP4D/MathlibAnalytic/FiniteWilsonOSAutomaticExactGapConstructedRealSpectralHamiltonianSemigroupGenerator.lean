import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupGenerator
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedComplexSpectralScalarExtension
import Mathlib.Analysis.Complex.Basic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance euclideanComplexContinuousSMulRealForScalarExtension
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

/-- The constructed real spectral semigroup is smooth in operator norm. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_contDiff
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    ContDiff ℝ ⊤ (D.realSpectralHamiltonianSemigroup n) := by
  simpa [FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.realSpectralHamiltonianSemigroup,
    orthonormalDiagonalHamiltonianSemigroup] using
    orthonormalDiagonalHamiltonianSemigroup_contDiff
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)

/-- The constructed real spectral semigroup is continuous in operator norm. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_continuous
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    Continuous (D.realSpectralHamiltonianSemigroup n) :=
  (finite_wilson_constructed_real_spectral_hamiltonianSemigroup_contDiff D n).continuous

/-- The constructed real spectral semigroup is strongly continuous on every
state. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_stronglyContinuous
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (x : D.StateSpace) :
    Continuous (fun t : ℝ => D.realSpectralHamiltonianSemigroup n t x) :=
  (finite_wilson_constructed_real_spectral_hamiltonianSemigroup_continuous D n).clm_apply
    continuous_const

/-- In operator norm, the constructed real spectral semigroup has generator
`-H` at time zero. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_hasDerivAt_zero_operator
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    HasDerivAt
      (D.realSpectralHamiltonianSemigroup n)
      (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) 0 := by
  have hdiag := symmetric_eq_orthonormalDiagonalLinearMap
    (D.hamiltonian n) (D.hamiltonianSymmetric n) D.stateFinrank
  have hop :
      orthonormalDiagonalOperator
          ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
          ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank) =
        LinearMap.toContinuousLinearMap (D.hamiltonian n) := by
    unfold orthonormalDiagonalOperator
    exact congrArg LinearMap.toContinuousLinearMap hdiag.symm
  have h := orthonormalDiagonalHamiltonianSemigroup_hasDerivAt_zero_operator
    ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
    ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
  simpa [FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData.realSpectralHamiltonianSemigroup,
    orthonormalDiagonalHamiltonianSemigroup, hop] using h

/-- On every constructed real state, the strong derivative at time zero is the
negative original Hamiltonian action. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_hasDerivAt_zero
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (x : D.StateSpace) :
    HasDerivAt
      (fun t : ℝ => D.realSpectralHamiltonianSemigroup n t x)
      (-(D.hamiltonian n x)) 0 := by
  have h :=
    (finite_wilson_constructed_real_spectral_hamiltonianSemigroup_hasDerivAt_zero_operator
      D n).clm_apply (hasDerivAt_const (0 : ℝ) x)
  simpa using h

/-- Ordinary derivative form of the constructed real generator identity. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_deriv_zero
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (x : D.StateSpace) :
    deriv (fun t : ℝ => D.realSpectralHamiltonianSemigroup n t x) 0 =
      -(D.hamiltonian n x) :=
  (finite_wilson_constructed_real_spectral_hamiltonianSemigroup_hasDerivAt_zero
    D n x).deriv

/-- After literal scalar extension, the complex spectral generator is exactly
the image of the real Hamiltonian generator. -/
theorem finite_wilson_constructed_complex_scalarExtension_generator_compatible
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (y : D.complexScalarExtensionStateSpace) :
    HasDerivAt
      (fun t : ℝ =>
        D.complexSpectralHamiltonianSemigroup n t
          (D.complexSpectralScalarExtensionEquiv n y))
      (D.complexSpectralScalarExtensionEquiv n
        (-((D.hamiltonian n).baseChange ℂ y))) 0 := by
  have hgen :=
    finite_wilson_constructed_complex_spectral_hamiltonianSemigroup_hasDerivAt_zero
      D n (D.complexSpectralScalarExtensionEquiv n y)
  have hinter :=
    finite_wilson_constructed_complex_spectral_scalarExtension_intertwines_hamiltonian
      D n
  have happ := LinearMap.congr_fun hinter y
  change
    D.complexSpectralScalarExtensionEquiv n
        ((D.hamiltonian n).baseChange ℂ y) =
      D.complexSpectralHamiltonian n
        (D.complexSpectralScalarExtensionEquiv n y) at happ
  convert hgen using 1
  rw [map_neg, happ]

/-- The same transported generator is the negative canonical complex logarithmic
Hamiltonian. -/
theorem finite_wilson_constructed_complex_scalarExtension_logGenerator_compatible
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ)
    (y : D.complexScalarExtensionStateSpace) :
    HasDerivAt
      (fun t : ℝ =>
        D.complexSpectralHamiltonianSemigroup n t
          (D.complexSpectralScalarExtensionEquiv n y))
      (-(D.complexSpectralLogHamiltonian n
        (D.complexSpectralScalarExtensionEquiv n y))) 0 :=
  finite_wilson_constructed_complex_spectral_hamiltonianSemigroup_hasDerivAt_zero_logHamiltonian
    D n (D.complexSpectralScalarExtensionEquiv n y)

end

end MathlibAnalytic
end MGAP4D
