import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianResolventTaylorStateMatrixElementBundle
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianResolventTaylorUniformClosedBallBundle

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace LinearPMap ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

/-- The constructed finite Wilson exact derivative Taylor series may be evaluated
termwise on every fixed state. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_taylor_apply_hasSum_of_norm_sub_lt
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) {lambda mu : ℝ} (hlambda : lambda < exactGapValueReal)
    (hdist : ‖mu - lambda‖ < exactGapValueReal - lambda) (y : D.StateSpace) :
    HasSum
      (fun k : ℕ =>
        (((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) • iteratedDeriv k
          (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)
          lambda) y)
      (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu y) := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_taylor_apply_hasSum_of_norm_sub_lt
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      hlambda hdist y)

/-- The constructed finite Wilson pointwise Taylor `tsum` equals the target
resolvent action. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_taylor_apply_tsum_eq_of_norm_sub_lt
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) {lambda mu : ℝ} (hlambda : lambda < exactGapValueReal)
    (hdist : ‖mu - lambda‖ < exactGapValueReal - lambda) (y : D.StateSpace) :
    (∑' k : ℕ,
      (((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) • iteratedDeriv k
        (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)
        lambda) y) =
      finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu y := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_taylor_apply_tsum_eq_of_norm_sub_lt
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      hlambda hdist y)

/-- Constructed finite Wilson fixed-state Taylor truncations inherit the exact
closed-subball geometric envelope. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_taylor_apply_error_norm_le_closedBall
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n N : ℕ) {lambda r mu : ℝ}
    (hlambda : lambda < exactGapValueReal)
    (hr0 : 0 ≤ r) (hrlt : r < exactGapValueReal - lambda)
    (hmu : ‖mu - lambda‖ ≤ r) (y : D.StateSpace) :
    ‖(finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu -
        ∑ k ∈ Finset.range N,
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) • iteratedDeriv k
            (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)
            lambda) y‖ ≤
      ((r * (exactGapValueReal - lambda)⁻¹) ^ N *
        (exactGapValueReal - lambda - r)⁻¹) * ‖y‖ := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_taylor_apply_error_norm_le_closedBall
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      hlambda hr0 hrlt hmu N y)

/-- Constructed finite Wilson fixed-state Taylor partial sums converge uniformly
on every strict closed subgap ball. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_taylor_apply_partialSum_tendstoUniformlyOn_closedBall
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) {lambda r : ℝ}
    (hlambda : lambda < exactGapValueReal)
    (hr0 : 0 ≤ r) (hrlt : r < exactGapValueReal - lambda)
    (y : D.StateSpace) :
    TendstoUniformlyOn
      (fun N : ℕ => fun mu : ℝ =>
        (∑ k ∈ Finset.range N,
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) • iteratedDeriv k
            (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)
            lambda) y)
      (fun mu : ℝ =>
        finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu y)
      atTop (Metric.closedBall lambda r) := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_taylor_apply_partialSum_tendstoUniformlyOn_closedBall
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      hlambda hr0 hrlt y)

/-- Every constructed finite Wilson real matrix element of the exact derivative
Taylor series may be summed termwise. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_taylor_matrixElement_hasSum_of_norm_sub_lt
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) {lambda mu : ℝ} (hlambda : lambda < exactGapValueReal)
    (hdist : ‖mu - lambda‖ < exactGapValueReal - lambda)
    (x y : D.StateSpace) :
    HasSum
      (fun k : ℕ => inner ℝ x
        ((((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) • iteratedDeriv k
          (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)
          lambda) y))
      (inner ℝ x
        (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu y)) := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_taylor_matrixElement_hasSum_of_norm_sub_lt
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      hlambda hdist x y)

/-- The constructed finite Wilson scalar matrix-element Taylor `tsum` equals the
target matrix element. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_taylor_matrixElement_tsum_eq_of_norm_sub_lt
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) {lambda mu : ℝ} (hlambda : lambda < exactGapValueReal)
    (hdist : ‖mu - lambda‖ < exactGapValueReal - lambda)
    (x y : D.StateSpace) :
    (∑' k : ℕ, inner ℝ x
      ((((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) • iteratedDeriv k
        (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)
        lambda) y)) =
      inner ℝ x
        (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu y) := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_taylor_matrixElement_tsum_eq_of_norm_sub_lt
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      hlambda hdist x y)

/-- Constructed finite Wilson matrix-element Taylor truncations inherit the exact
closed-subball geometric envelope with the two state norms. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_taylor_matrixElement_error_abs_le_closedBall
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n N : ℕ) {lambda r mu : ℝ}
    (hlambda : lambda < exactGapValueReal)
    (hr0 : 0 ≤ r) (hrlt : r < exactGapValueReal - lambda)
    (hmu : ‖mu - lambda‖ ≤ r) (x y : D.StateSpace) :
    |inner ℝ x
      ((finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu -
        ∑ k ∈ Finset.range N,
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) • iteratedDeriv k
            (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)
            lambda) y)| ≤
      ((r * (exactGapValueReal - lambda)⁻¹) ^ N *
        (exactGapValueReal - lambda - r)⁻¹) * ‖x‖ * ‖y‖ := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_taylor_matrixElement_error_abs_le_closedBall
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      hlambda hr0 hrlt hmu N x y)

/-- Constructed finite Wilson scalar matrix-element Taylor series converge
uniformly on every strict closed subgap ball. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_taylor_matrixElement_partialSum_tendstoUniformlyOn_closedBall
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) {lambda r : ℝ}
    (hlambda : lambda < exactGapValueReal)
    (hr0 : 0 ≤ r) (hrlt : r < exactGapValueReal - lambda)
    (x y : D.StateSpace) :
    TendstoUniformlyOn
      (fun N : ℕ => fun mu : ℝ => inner ℝ x
        ((∑ k ∈ Finset.range N,
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) • iteratedDeriv k
            (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)
            lambda) y))
      (fun mu : ℝ => inner ℝ x
        (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu y))
      atTop (Metric.closedBall lambda r) := by
  simpa only [finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_taylor_matrixElement_partialSum_tendstoUniformlyOn_closedBall
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      hlambda hr0 hrlt x y)

end MathlibAnalytic
end MGAP4D

end
