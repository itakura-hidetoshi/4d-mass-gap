import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianResolventNeumannSeriesRemainderBundle
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalRealSpectralHamiltonianResolventAnalyticNeumannBundle

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace LinearPMap ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

/-- The ordered Neumann terms for the finite Wilson `Ω⊥` resolvent sum in
operator norm to the target resolvent. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_neumann_hasSum_of_norm_sub_lt
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) {lambda mu : ℝ} (hlambda : lambda < exactGapValueReal)
    (hdist : ‖mu - lambda‖ < exactGapValueReal - lambda) :
    HasSum
      (fun k : ℕ =>
        (((mu - lambda) •
          finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda) ^ k) *
            finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda)
      (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n mu) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_neumann_hasSum_of_norm_sub_lt
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n hlambda hdist

/-- The ordered local Neumann series for the finite Wilson `Ω⊥` resolvent is
summable in operator norm. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_neumann_summable_of_norm_sub_lt
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) {lambda mu : ℝ} (hlambda : lambda < exactGapValueReal)
    (hdist : ‖mu - lambda‖ < exactGapValueReal - lambda) :
    Summable
      (fun k : ℕ =>
        (((mu - lambda) •
          finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda) ^ k) *
            finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_neumann_summable_of_norm_sub_lt
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n hlambda hdist

/-- The infinite ordered Neumann sum for the finite Wilson `Ω⊥` resolvent is
the target resolvent exactly. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_neumann_tsum_eq_of_norm_sub_lt
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) {lambda mu : ℝ} (hlambda : lambda < exactGapValueReal)
    (hdist : ‖mu - lambda‖ < exactGapValueReal - lambda) :
    (∑' k : ℕ,
      (((mu - lambda) •
        finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda) ^ k) *
          finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda) =
      finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n mu := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_neumann_tsum_eq_of_norm_sub_lt
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n hlambda hdist

/-- The finite ordered Neumann partial sums converge in operator norm to the
finite Wilson `Ω⊥` resolvent. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_neumann_partialSum_tendsto_of_norm_sub_lt
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) {lambda mu : ℝ} (hlambda : lambda < exactGapValueReal)
    (hdist : ‖mu - lambda‖ < exactGapValueReal - lambda) :
    Tendsto
      (fun N : ℕ =>
        (∑ k ∈ Finset.range N,
          ((mu - lambda) •
            finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda) ^ k) *
          finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda)
      atTop
      (𝓝 (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n mu)) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_neumann_partialSum_tendsto_of_norm_sub_lt
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n hlambda hdist

/-- Exact ordered remainder identity for every finite Wilson `Ω⊥` Neumann
truncation. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_sub_neumann_partialSum_eq
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n N : ℕ) {lambda mu : ℝ} (hlambda : lambda < exactGapValueReal)
    (hdist : ‖mu - lambda‖ < exactGapValueReal - lambda) :
    finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n mu -
        (∑ k ∈ Finset.range N,
          ((mu - lambda) •
            finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda) ^ k) *
          finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda =
      ((mu - lambda) •
        finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda) ^ N *
        finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n mu := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_sub_neumann_partialSum_eq
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n N hlambda hdist

/-- Operator-norm remainder bound for every finite Wilson `Ω⊥` Neumann
truncation. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_sub_neumann_partialSum_norm_le
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n N : ℕ) {lambda mu : ℝ} (hlambda : lambda < exactGapValueReal)
    (hdist : ‖mu - lambda‖ < exactGapValueReal - lambda) :
    ‖finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n mu -
        (∑ k ∈ Finset.range N,
          ((mu - lambda) •
            finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda) ^ k) *
          finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda‖ ≤
      ‖(mu - lambda) •
          finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda‖ ^ N *
        (exactGapValueReal - mu)⁻¹ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_sub_neumann_partialSum_norm_le
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n N hlambda hdist

/-- Explicit geometric truncation error for the finite Wilson `Ω⊥` resolvent. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent_sub_neumann_partialSum_norm_le_explicit
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n N : ℕ) {lambda mu : ℝ} (hlambda : lambda < exactGapValueReal)
    (hdist : ‖mu - lambda‖ < exactGapValueReal - lambda) :
    ‖finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n mu -
        (∑ k ∈ Finset.range N,
          ((mu - lambda) •
            finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda) ^ k) *
          finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda‖ ≤
      (‖mu - lambda‖ * (exactGapValueReal - lambda)⁻¹) ^ N *
        (exactGapValueReal - mu)⁻¹ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_sub_neumann_partialSum_norm_le_explicit
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n N hlambda hdist

/-- Infinite Neumann summation, partial-sum convergence, exact remainder, and
explicit geometric error for the finite Wilson `Ω⊥` resolvent. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolventNeumannSeriesRemainder_package
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    ∀ {lambda mu : ℝ} (hlambda : lambda < exactGapValueReal)
        (hdist : ‖mu - lambda‖ < exactGapValueReal - lambda),
      HasSum (fun k : ℕ => (((mu - lambda) •
        finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda) ^ k) *
        finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda)
        (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n mu) ∧
      Tendsto (fun N : ℕ => (∑ k ∈ Finset.range N, ((mu - lambda) •
        finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda) ^ k) *
        finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda) atTop
        (𝓝 (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n mu)) ∧
      ∀ N : ℕ, finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n mu -
        (∑ k ∈ Finset.range N, ((mu - lambda) •
          finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda) ^ k) *
          finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda =
        ((mu - lambda) •
          finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda) ^ N *
          finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n mu ∧
        ‖finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n mu -
          (∑ k ∈ Finset.range N, ((mu - lambda) •
            finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda) ^ k) *
            finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianResolvent D n lambda‖ ≤
          (‖mu - lambda‖ * (exactGapValueReal - lambda)⁻¹) ^ N *
            (exactGapValueReal - mu)⁻¹ := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolventNeumannSeriesRemainder_package
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

end MathlibAnalytic
end MGAP4D

end