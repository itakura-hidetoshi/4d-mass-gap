import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalComplexSpectralHamiltonianSemigroupGenerator
import Mathlib.Analysis.Complex.Basic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

local instance compileSmokeComplexModuleContinuousSMulReal
    {E : Type*}
    [TopologicalSpace E]
    [MulAction ℂ E]
    [SMul ℝ E]
    [IsScalarTower ℝ ℂ E]
    [ContinuousSMul ℂ E] :
    ContinuousSMul ℝ E where
  continuous_smul := by
    have hcoe : Continuous (fun p : ℝ × E => (p.1 : ℂ) • p.2) :=
      (Complex.continuous_ofReal.comp
        (continuous_fst : Continuous (fun p : ℝ × E => p.1))).smul
          (continuous_snd : Continuous (fun p : ℝ × E => p.2))
    simpa only [Complex.coe_smul] using hcoe

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
variable
  (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
variable (n : ℕ)

example :
    ContDiff ℝ ⊤ (D.vacuumOrthogonalComplexSpectralHamiltonianSemigroup n) :=
  finite_wilson_vacuum_orthogonal_complex_spectral_hamiltonianSemigroup_contDiff D n

example :
    Continuous (D.vacuumOrthogonalComplexSpectralHamiltonianSemigroup n) :=
  finite_wilson_vacuum_orthogonal_complex_spectral_hamiltonianSemigroup_continuous D n

example (x : D.vacuumOrthogonalComplexSpectralStateSpace) :
    Continuous (fun t : ℝ =>
      D.vacuumOrthogonalComplexSpectralHamiltonianSemigroup n t x) :=
  finite_wilson_vacuum_orthogonal_complex_spectral_hamiltonianSemigroup_stronglyContinuous
    D n x

example (x : EuclideanSpace ℂ (Fin D.gapData.ExcitedDimension)) :
    HasDerivAt
      (fun t : ℝ =>
        (D.vacuumOrthogonalComplexSpectralHamiltonianSemigroup n t x :
          EuclideanSpace ℂ (Fin D.gapData.ExcitedDimension)))
      ((-(D.vacuumOrthogonalComplexSpectralLogHamiltonian n x)) :
        EuclideanSpace ℂ (Fin D.gapData.ExcitedDimension)) 0 :=
  finite_wilson_vacuum_orthogonal_complex_spectral_hamiltonianSemigroup_hasDerivAt_zero_logHamiltonian
    D n x

example (x : EuclideanSpace ℂ (Fin D.gapData.ExcitedDimension)) :
    deriv
        (fun t : ℝ =>
          (D.vacuumOrthogonalComplexSpectralHamiltonianSemigroup n t x :
            EuclideanSpace ℂ (Fin D.gapData.ExcitedDimension)))
        0 =
      ((-(D.vacuumOrthogonalComplexSpectralLogHamiltonian n x)) :
        EuclideanSpace ℂ (Fin D.gapData.ExcitedDimension)) :=
  finite_wilson_vacuum_orthogonal_complex_spectral_hamiltonianSemigroup_deriv_zero
    D n x

end

end MathlibAnalytic
end MGAP4D
