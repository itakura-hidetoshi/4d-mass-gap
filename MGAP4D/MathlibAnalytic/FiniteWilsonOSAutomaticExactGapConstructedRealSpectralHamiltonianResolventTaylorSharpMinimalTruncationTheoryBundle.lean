import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianResolventTaylorSharpMinimalTruncationTheoryBundle
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianResolventTaylorExplicitLogCeilTruncationOrderBundle

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace LinearPMap ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

/-- The sharp envelope-minimal Taylor order for the exact finite Wilson gap and
a closed spectral-parameter ball. -/
noncomputable def finiteWilsonExactGapResolventTaylorSharpTruncationOrder
    (lambda r epsilon : ℝ) : ℕ :=
  resolventTaylorClosedBall_sharpTruncationOrder
    exactGapValueReal lambda r epsilon

/-- The finite Wilson sharp order exactly characterizes the natural degrees for
which the common exact-gap geometric envelope is below tolerance. -/
theorem finiteWilsonExactGapResolventTaylorSharpTruncationOrder_le_iff
    {lambda r epsilon : ℝ}
    (hlambda : lambda < exactGapValueReal)
    (hr0 : 0 ≤ r) (hrlt : r < exactGapValueReal - lambda)
    (hepsilon : 0 < epsilon)
    (N : ℕ) :
    finiteWilsonExactGapResolventTaylorSharpTruncationOrder
        lambda r epsilon ≤ N ↔
      (r * (exactGapValueReal - lambda)⁻¹) ^ N *
        (exactGapValueReal - lambda - r)⁻¹ < epsilon := by
  simpa [finiteWilsonExactGapResolventTaylorSharpTruncationOrder] using
    (resolventTaylorClosedBall_sharpTruncationOrder_le_iff
      hlambda hr0 hrlt hepsilon N)

/-- The finite Wilson sharp order is the least natural degree satisfying the
common exact-gap geometric envelope tolerance. -/
theorem finiteWilsonExactGapResolventTaylorSharpTruncationOrder_isLeast
    {lambda r epsilon : ℝ}
    (hlambda : lambda < exactGapValueReal)
    (hr0 : 0 ≤ r) (hrlt : r < exactGapValueReal - lambda)
    (hepsilon : 0 < epsilon) :
    IsLeast
      {N : ℕ |
        (r * (exactGapValueReal - lambda)⁻¹) ^ N *
          (exactGapValueReal - lambda - r)⁻¹ < epsilon}
      (finiteWilsonExactGapResolventTaylorSharpTruncationOrder
        lambda r epsilon) := by
  simpa [finiteWilsonExactGapResolventTaylorSharpTruncationOrder] using
    (resolventTaylorClosedBall_sharpTruncationOrder_isLeast
      hlambda hr0 hrlt hepsilon)

/-- The previously introduced logarithmic-ceiling finite Wilson order is
conservative by at most one Taylor degree relative to the sharp threshold. -/
theorem finiteWilsonExactGapResolventTaylorSharpExplicit_sandwich
    {lambda r epsilon : ℝ}
    (hlambda : lambda < exactGapValueReal)
    (hr0 : 0 ≤ r) (hrlt : r < exactGapValueReal - lambda)
    (hepsilon : 0 < epsilon) :
    finiteWilsonExactGapResolventTaylorSharpTruncationOrder lambda r epsilon ≤
      finiteWilsonExactGapResolventTaylorExplicitTruncationOrder lambda r epsilon ∧
    finiteWilsonExactGapResolventTaylorExplicitTruncationOrder lambda r epsilon ≤
      finiteWilsonExactGapResolventTaylorSharpTruncationOrder lambda r epsilon + 1 := by
  simpa [finiteWilsonExactGapResolventTaylorSharpTruncationOrder,
    finiteWilsonExactGapResolventTaylorExplicitTruncationOrder] using
    (resolventTaylorClosedBall_sharp_explicit_sandwich
      hlambda hr0 hrlt hepsilon)

/-- Enlarging the finite Wilson parameter-ball radius cannot decrease the sharp
Taylor degree. -/
theorem finiteWilsonExactGapResolventTaylorSharpTruncationOrder_mono_radius
    {lambda r₁ r₂ epsilon : ℝ}
    (hlambda : lambda < exactGapValueReal)
    (hr₁0 : 0 ≤ r₁) (hr₁₂ : r₁ ≤ r₂)
    (hr₂lt : r₂ < exactGapValueReal - lambda)
    (hepsilon : 0 < epsilon) :
    finiteWilsonExactGapResolventTaylorSharpTruncationOrder
        lambda r₁ epsilon ≤
      finiteWilsonExactGapResolventTaylorSharpTruncationOrder
        lambda r₂ epsilon := by
  simpa [finiteWilsonExactGapResolventTaylorSharpTruncationOrder] using
    (resolventTaylorClosedBall_sharpTruncationOrder_mono_radius
      hlambda hr₁0 hr₁₂ hr₂lt hepsilon)

/-- Moving the finite Wilson Taylor center toward the exact gap cannot decrease
the sharp truncation requirement. -/
theorem finiteWilsonExactGapResolventTaylorSharpTruncationOrder_mono_center
    {lambda₁ lambda₂ r epsilon : ℝ}
    (hlambda₁₂ : lambda₁ ≤ lambda₂)
    (hlambda₂ : lambda₂ < exactGapValueReal)
    (hr0 : 0 ≤ r) (hrlt₂ : r < exactGapValueReal - lambda₂)
    (hepsilon : 0 < epsilon) :
    finiteWilsonExactGapResolventTaylorSharpTruncationOrder
        lambda₁ r epsilon ≤
      finiteWilsonExactGapResolventTaylorSharpTruncationOrder
        lambda₂ r epsilon := by
  simpa [finiteWilsonExactGapResolventTaylorSharpTruncationOrder] using
    (resolventTaylorClosedBall_sharpTruncationOrder_mono_center
      hlambda₁₂ hlambda₂ hr0 hrlt₂ hepsilon)

/-- Increasing the tolerance cannot increase the finite Wilson sharp Taylor
degree. -/
theorem finiteWilsonExactGapResolventTaylorSharpTruncationOrder_antitone_epsilon
    {lambda r epsilon₁ epsilon₂ : ℝ}
    (hlambda : lambda < exactGapValueReal)
    (hr0 : 0 ≤ r) (hrlt : r < exactGapValueReal - lambda)
    (hepsilon₁ : 0 < epsilon₁) (hepsilon₂ : 0 < epsilon₂)
    (heps : epsilon₁ ≤ epsilon₂) :
    finiteWilsonExactGapResolventTaylorSharpTruncationOrder
        lambda r epsilon₂ ≤
      finiteWilsonExactGapResolventTaylorSharpTruncationOrder
        lambda r epsilon₁ := by
  simpa [finiteWilsonExactGapResolventTaylorSharpTruncationOrder] using
    (resolventTaylorClosedBall_sharpTruncationOrder_antitone_epsilon
      hlambda hr0 hrlt hepsilon₁ hepsilon₂ heps)

/-- Every degree at or above the sharp envelope threshold controls the
operator-norm Taylor remainder simultaneously for all constructed finite Wilson
indices. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_taylor_operatorNorm_error_lt_closedBall_allIndices_of_sharpTruncationOrder
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    {lambda r epsilon : ℝ} (hlambda : lambda < exactGapValueReal)
    (hr0 : 0 ≤ r) (hrlt : r < exactGapValueReal - lambda)
    (hepsilon : 0 < epsilon)
    {N : ℕ}
    (hN : finiteWilsonExactGapResolventTaylorSharpTruncationOrder
      lambda r epsilon ≤ N)
    (n : ℕ) (mu : ℝ) (hmu : ‖mu - lambda‖ ≤ r) :
    ‖finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu -
        (∑ k ∈ Finset.range N,
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) • iteratedDeriv k
            (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)
            lambda)‖ < epsilon := by
  simpa only [finiteWilsonExactGapResolventTaylorSharpTruncationOrder,
    finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_taylor_operatorNorm_error_lt_closedBall_family_of_sharpTruncationOrder
      (fun n : ℕ =>
        (D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      (fun n : ℕ =>
        (D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal
      (fun n : ℕ => D.hamiltonianEigenvalues_ge_exactGap n)
      hlambda hr0 hrlt hepsilon hN n mu hmu)

/-- The same sharp degree controls every two-unit-ball matrix element for all
constructed finite Wilson indices. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_taylor_matrixElement_error_abs_lt_closedBall_unitBalls_allIndices_of_sharpTruncationOrder
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    {lambda r epsilon : ℝ} (hlambda : lambda < exactGapValueReal)
    (hr0 : 0 ≤ r) (hrlt : r < exactGapValueReal - lambda)
    (hepsilon : 0 < epsilon)
    {N : ℕ}
    (hN : finiteWilsonExactGapResolventTaylorSharpTruncationOrder
      lambda r epsilon ≤ N)
    (n : ℕ) (mu : ℝ) (hmu : ‖mu - lambda‖ ≤ r)
    (x y : D.StateSpace) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    |inner ℝ x
      ((finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu -
        ∑ k ∈ Finset.range N,
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) • iteratedDeriv k
            (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)
            lambda) y)| < epsilon := by
  simpa only [finiteWilsonExactGapResolventTaylorSharpTruncationOrder,
    finite_wilson_constructed_real_spectral_hamiltonianResolvent] using
    (orthonormalDiagonalHamiltonianResolvent_taylor_matrixElement_error_abs_lt_closedBall_unitBalls_family_of_sharpTruncationOrder
      (fun n : ℕ =>
        (D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      (fun n : ℕ =>
        (D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal
      (fun n : ℕ => D.hamiltonianEigenvalues_ge_exactGap n)
      hlambda hr0 hrlt hepsilon hN n mu hmu x y hx hy)

/-- At the sharp envelope degree itself, all constructed finite Wilson
operator-norm Taylor errors are below tolerance. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_taylor_operatorNorm_error_lt_closedBall_allIndices_at_sharpTruncationOrder
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    {lambda r epsilon : ℝ} (hlambda : lambda < exactGapValueReal)
    (hr0 : 0 ≤ r) (hrlt : r < exactGapValueReal - lambda)
    (hepsilon : 0 < epsilon)
    (n : ℕ) (mu : ℝ) (hmu : ‖mu - lambda‖ ≤ r) :
    ‖finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu -
        (∑ k ∈ Finset.range
          (finiteWilsonExactGapResolventTaylorSharpTruncationOrder
            lambda r epsilon),
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) • iteratedDeriv k
            (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)
            lambda)‖ < epsilon := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_taylor_operatorNorm_error_lt_closedBall_allIndices_of_sharpTruncationOrder
      D hlambda hr0 hrlt hepsilon le_rfl n mu hmu

/-- At the sharp envelope degree itself, all constructed finite Wilson
matrix elements on the two unit balls are below tolerance. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianResolvent_taylor_matrixElement_error_abs_lt_closedBall_unitBalls_allIndices_at_sharpTruncationOrder
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    {lambda r epsilon : ℝ} (hlambda : lambda < exactGapValueReal)
    (hr0 : 0 ≤ r) (hrlt : r < exactGapValueReal - lambda)
    (hepsilon : 0 < epsilon)
    (n : ℕ) (mu : ℝ) (hmu : ‖mu - lambda‖ ≤ r)
    (x y : D.StateSpace) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    |inner ℝ x
      ((finite_wilson_constructed_real_spectral_hamiltonianResolvent D n mu -
        ∑ k ∈ Finset.range
          (finiteWilsonExactGapResolventTaylorSharpTruncationOrder
            lambda r epsilon),
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) • iteratedDeriv k
            (finite_wilson_constructed_real_spectral_hamiltonianResolvent D n)
            lambda) y)| < epsilon := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianResolvent_taylor_matrixElement_error_abs_lt_closedBall_unitBalls_allIndices_of_sharpTruncationOrder
      D hlambda hr0 hrlt hepsilon le_rfl n mu hmu x y hx hy

end MathlibAnalytic
end MGAP4D

end
