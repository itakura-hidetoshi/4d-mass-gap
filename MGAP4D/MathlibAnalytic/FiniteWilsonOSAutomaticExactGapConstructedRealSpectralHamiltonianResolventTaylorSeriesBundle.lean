import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianResolventTaylorSeriesBundle
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianResolventFactorialDerivativeBundle
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianResolventNeumannSeriesRemainderBundle

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace LinearPMap ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

/-- The normalized constructed finite Wilson resolvent derivative is exactly the
next resolvent power. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_invFactorial_smul_iteratedDeriv_eq_pow
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n k : ℕ) {lambda : ℝ} (hlambda : lambda < exactGapValueReal) :
    ((k.factorial : ℝ)⁻¹) • iteratedDeriv k
        (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n) lambda =
      (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda) ^
        (k + 1) := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_invFactorial_smul_iteratedDeriv_eq_pow
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      k hlambda)

/-- Each ordered constructed finite Wilson Neumann term is the corresponding
scalar-power resolvent term. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_neumann_term_eq_power_term
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n k : ℕ) (lambda mu : ℝ) :
    (((mu - lambda) •
        finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda) ^ k) *
        finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda =
      (mu - lambda) ^ k •
        (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda) ^
          (k + 1) := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_neumann_term_eq_power_term
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      k lambda mu)

/-- The exact constructed finite Wilson Taylor term equals its ordered Neumann
term. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_taylor_term_eq_neumann_term
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n k : ℕ) {lambda mu : ℝ} (hlambda : lambda < exactGapValueReal) :
    (((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) • iteratedDeriv k
        (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n) lambda) =
      (((mu - lambda) •
          finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda) ^ k) *
        finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_taylor_term_eq_neumann_term
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      k hlambda)

/-- Every finite constructed finite Wilson Taylor partial sum equals the
corresponding ordered Neumann partial sum. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_taylor_partialSum_eq_neumann_partialSum
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n N : ℕ) {lambda mu : ℝ} (hlambda : lambda < exactGapValueReal) :
    (∑ k ∈ Finset.range N,
        ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) • iteratedDeriv k
          (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n) lambda) =
      (∑ k ∈ Finset.range N,
        ((mu - lambda) •
          finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda) ^ k) *
        finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_taylor_partialSum_eq_neumann_partialSum
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      N hlambda)

/-- The exact-derivative Taylor series for the constructed finite Wilson
resolvent sums in operator norm to the target resolvent. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_taylor_hasSum_of_norm_sub_lt
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) {lambda mu : ℝ} (hlambda : lambda < exactGapValueReal)
    (hdist : ‖mu - lambda‖ < exactGapValueReal - lambda) :
    HasSum
      (fun k : ℕ => ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) • iteratedDeriv k
        (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n) lambda)
      (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu) := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_taylor_hasSum_of_norm_sub_lt
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      hlambda hdist)

/-- The exact-derivative Taylor series for the constructed finite Wilson
resolvent is summable in operator norm. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_taylor_summable_of_norm_sub_lt
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) {lambda mu : ℝ} (hlambda : lambda < exactGapValueReal)
    (hdist : ‖mu - lambda‖ < exactGapValueReal - lambda) :
    Summable
      (fun k : ℕ => ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) • iteratedDeriv k
        (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n) lambda) := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_taylor_summable_of_norm_sub_lt
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      hlambda hdist)

/-- The constructed finite Wilson operator-norm Taylor sum is exactly the target
resolvent. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_taylor_tsum_eq_of_norm_sub_lt
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) {lambda mu : ℝ} (hlambda : lambda < exactGapValueReal)
    (hdist : ‖mu - lambda‖ < exactGapValueReal - lambda) :
    (∑' k : ℕ, ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) • iteratedDeriv k
      (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n) lambda) =
      finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_taylor_tsum_eq_of_norm_sub_lt
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      hlambda hdist)

/-- Constructed finite Wilson exact-derivative Taylor partial sums converge in
operator norm to the target resolvent. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_taylor_partialSum_tendsto_of_norm_sub_lt
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) {lambda mu : ℝ} (hlambda : lambda < exactGapValueReal)
    (hdist : ‖mu - lambda‖ < exactGapValueReal - lambda) :
    Tendsto
      (fun N : ℕ => ∑ k ∈ Finset.range N,
        ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) • iteratedDeriv k
          (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n) lambda)
      atTop
      (𝓝 (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu)) := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_taylor_partialSum_tendsto_of_norm_sub_lt
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      hlambda hdist)

/-- Exact ordered remainder for every constructed finite Wilson derivative
Taylor truncation. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_sub_taylor_partialSum_eq
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n N : ℕ) {lambda mu : ℝ} (hlambda : lambda < exactGapValueReal)
    (hdist : ‖mu - lambda‖ < exactGapValueReal - lambda) :
    finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu -
        (∑ k ∈ Finset.range N,
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) • iteratedDeriv k
            (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n) lambda) =
      ((mu - lambda) •
        finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda) ^ N *
        finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_sub_taylor_partialSum_eq
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      N hlambda hdist)

/-- Explicit gap-controlled geometric error for every constructed finite Wilson
derivative Taylor truncation. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_sub_taylor_partialSum_norm_le
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n N : ℕ) {lambda mu : ℝ} (hlambda : lambda < exactGapValueReal)
    (hdist : ‖mu - lambda‖ < exactGapValueReal - lambda) :
    ‖finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu -
        (∑ k ∈ Finset.range N,
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) • iteratedDeriv k
            (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n) lambda)‖ ≤
      (‖mu - lambda‖ * (exactGapValueReal - lambda)⁻¹) ^ N *
        (exactGapValueReal - mu)⁻¹ := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_sub_taylor_partialSum_norm_le
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      N hlambda hdist)

end MathlibAnalytic
end MGAP4D

end
