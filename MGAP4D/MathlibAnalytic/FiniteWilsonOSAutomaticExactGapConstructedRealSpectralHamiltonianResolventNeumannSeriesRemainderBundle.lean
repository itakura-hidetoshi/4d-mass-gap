import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianResolventNeumannSeriesRemainderBundle
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianResolventAnalyticNeumannBundle

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace LinearPMap ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

/-- The ordered Neumann terms for the constructed finite Wilson resolvent sum
in operator norm to the target resolvent. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_neumann_hasSum_of_norm_sub_lt
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) {lambda mu : ℝ} (hlambda : lambda < exactGapValueReal)
    (hdist : ‖mu - lambda‖ < exactGapValueReal - lambda) :
    HasSum
      (fun k : ℕ =>
        (((mu - lambda) •
          finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda) ^ k) *
            finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda)
      (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu) := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_neumann_hasSum_of_norm_sub_lt
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      hlambda hdist)

/-- The ordered local Neumann series for the constructed finite Wilson
resolvent is summable in operator norm. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_neumann_summable_of_norm_sub_lt
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) {lambda mu : ℝ} (hlambda : lambda < exactGapValueReal)
    (hdist : ‖mu - lambda‖ < exactGapValueReal - lambda) :
    Summable
      (fun k : ℕ =>
        (((mu - lambda) •
          finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda) ^ k) *
            finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda) := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_neumann_summable_of_norm_sub_lt
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      hlambda hdist)

/-- The infinite ordered Neumann sum for the constructed finite Wilson
resolvent equals the target resolvent exactly. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_neumann_tsum_eq_of_norm_sub_lt
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) {lambda mu : ℝ} (hlambda : lambda < exactGapValueReal)
    (hdist : ‖mu - lambda‖ < exactGapValueReal - lambda) :
    (∑' k : ℕ,
      (((mu - lambda) •
        finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda) ^ k) *
          finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda) =
      finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_neumann_tsum_eq_of_norm_sub_lt
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      hlambda hdist)

/-- The finite ordered Neumann partial sums converge in operator norm to the
constructed finite Wilson resolvent. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_neumann_partialSum_tendsto_of_norm_sub_lt
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) {lambda mu : ℝ} (hlambda : lambda < exactGapValueReal)
    (hdist : ‖mu - lambda‖ < exactGapValueReal - lambda) :
    Tendsto
      (fun N : ℕ =>
        (∑ k ∈ Finset.range N,
          ((mu - lambda) •
            finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda) ^ k) *
          finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda)
      atTop
      (𝓝 (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu)) := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_neumann_partialSum_tendsto_of_norm_sub_lt
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      hlambda hdist)

/-- Exact ordered remainder identity for every constructed finite Wilson
Neumann truncation. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_sub_neumann_partialSum_eq
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n N : ℕ) {lambda mu : ℝ} (hlambda : lambda < exactGapValueReal)
    (hdist : ‖mu - lambda‖ < exactGapValueReal - lambda) :
    finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu -
        (∑ k ∈ Finset.range N,
          ((mu - lambda) •
            finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda) ^ k) *
          finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda =
      ((mu - lambda) •
        finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda) ^ N *
        finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_sub_neumann_partialSum_eq
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      N hlambda hdist)

/-- Operator-norm remainder bound for every constructed finite Wilson Neumann
truncation. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_sub_neumann_partialSum_norm_le
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n N : ℕ) {lambda mu : ℝ} (hlambda : lambda < exactGapValueReal)
    (hdist : ‖mu - lambda‖ < exactGapValueReal - lambda) :
    ‖finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu -
        (∑ k ∈ Finset.range N,
          ((mu - lambda) •
            finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda) ^ k) *
          finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda‖ ≤
      ‖(mu - lambda) •
          finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda‖ ^ N *
        (exactGapValueReal - mu)⁻¹ := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_sub_neumann_partialSum_norm_le
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      N hlambda hdist)

/-- Explicit geometric truncation error for the constructed finite Wilson
resolvent. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_sub_neumann_partialSum_norm_le_explicit
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n N : ℕ) {lambda mu : ℝ} (hlambda : lambda < exactGapValueReal)
    (hdist : ‖mu - lambda‖ < exactGapValueReal - lambda) :
    ‖finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu -
        (∑ k ∈ Finset.range N,
          ((mu - lambda) •
            finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda) ^ k) *
          finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda‖ ≤
      (‖mu - lambda‖ * (exactGapValueReal - lambda)⁻¹) ^ N *
        (exactGapValueReal - mu)⁻¹ := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_sub_neumann_partialSum_norm_le_explicit
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      N hlambda hdist)

/-- Infinite Neumann summation, partial-sum convergence, exact remainder, and
explicit geometric error for the constructed finite Wilson resolvent. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolventNeumannSeriesRemainder_package
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) :
    ∀ {lambda mu : ℝ} (hlambda : lambda < exactGapValueReal)
        (hdist : ‖mu - lambda‖ < exactGapValueReal - lambda),
      HasSum (fun k : ℕ => (((mu - lambda) •
        finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda) ^ k) *
        finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda)
        (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu) ∧
      Tendsto (fun N : ℕ => (∑ k ∈ Finset.range N, ((mu - lambda) •
        finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda) ^ k) *
        finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda) atTop
        (𝓝 (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu)) ∧
      ∀ N : ℕ, finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu -
        (∑ k ∈ Finset.range N, ((mu - lambda) •
          finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda) ^ k) *
          finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda =
        ((mu - lambda) •
          finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda) ^ N *
          finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu ∧
        ‖finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu -
          (∑ k ∈ Finset.range N, ((mu - lambda) •
            finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda) ^ k) *
            finite_wilson_constructed_real_spectral_hamiltonianResolvent D n lambda‖ ≤
          (‖mu - lambda‖ * (exactGapValueReal - lambda)⁻¹) ^ N *
            (exactGapValueReal - mu)⁻¹ := by
  intro lambda mu hlambda hdist
  refine ⟨finite_wilson_constructed_real_spectral_hamiltonianResolvent_neumann_hasSum_of_norm_sub_lt
      D n hlambda hdist,
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_neumann_partialSum_tendsto_of_norm_sub_lt
      D n hlambda hdist, ?_⟩
  intro N
  exact ⟨finite_wilson_constructed_real_spectral_hamiltonianResolvent_sub_neumann_partialSum_eq
      D n N hlambda hdist,
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_sub_neumann_partialSum_norm_le_explicit
      D n N hlambda hdist⟩

end MathlibAnalytic
end MGAP4D

end