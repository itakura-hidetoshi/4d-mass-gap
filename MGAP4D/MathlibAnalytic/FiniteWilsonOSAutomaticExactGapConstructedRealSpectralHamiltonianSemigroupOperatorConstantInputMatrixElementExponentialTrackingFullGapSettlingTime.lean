import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorConstantInputMatrixElementExponentialTrackingFullGapSettlingTime
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorConstantInputMatrixElementExponentialTrackingFullGap
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Constructed finite Wilson left matrix elements reach every positive tolerance
    after the explicit exact-gap logarithmic waiting time. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_constantInput_matrixElement_abs_le_epsilon_after_exponentialTracking_fullGap_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ : ℝ)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace) (x y : D.StateSpace)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F_lim) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            ((‖A - finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim‖ *
                ‖x‖ * ‖y‖) / ε) / exactGapValueReal) ≤ t →
        |inner ℝ x
          ((U t - finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim) y)| ≤ ε := by
  refine realFunction_abs_le_epsilon_after_exponentialBound
    exactGapValueReal ε
      (‖A - finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim‖ * ‖x‖ * ‖y‖)
      t₀ exactGapValueReal_pos hε ?_
      (fun t : ℝ => inner ℝ x
        ((U t - finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim) y)) ?_
  · positivity
  · intro t ht
    have hmatrix :=
      finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_constantInput_matrixElement_exponentialTracking_fullGap_left
        D n t₀ t ht A U F_lim x y hU0 hU
    calc
      |inner ℝ x
          ((U t - finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim) y)| ≤
          (‖A - finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim‖ *
            Real.exp (-((t - t₀) * exactGapValueReal))) * ‖x‖ * ‖y‖ := hmatrix
      _ = (‖A - finiteWilsonConstructedHamiltonianLeftSteadyState D n F_lim‖ *
            ‖x‖ * ‖y‖) * Real.exp (-((t - t₀) * exactGapValueReal)) := by ring

/-- Constructed finite Wilson right matrix elements have the identical settling
    time and require no commutation hypothesis. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_constantInput_matrixElement_abs_le_epsilon_after_exponentialTracking_fullGap_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ : ℝ)
    (A : D.StateSpace →L[ℝ] D.StateSpace)
    (U : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F_lim : D.StateSpace →L[ℝ] D.StateSpace) (x y : D.StateSpace)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F_lim) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            ((‖A - finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim‖ *
                ‖x‖ * ‖y‖) / ε) / exactGapValueReal) ≤ t →
        |inner ℝ x
          ((U t - finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim) y)| ≤ ε := by
  refine realFunction_abs_le_epsilon_after_exponentialBound
    exactGapValueReal ε
      (‖A - finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim‖ * ‖x‖ * ‖y‖)
      t₀ exactGapValueReal_pos hε ?_
      (fun t : ℝ => inner ℝ x
        ((U t - finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim) y)) ?_
  · positivity
  · intro t ht
    have hmatrix :=
      finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_constantInput_matrixElement_exponentialTracking_fullGap_right
        D n t₀ t ht A U F_lim x y hU0 hU
    calc
      |inner ℝ x
          ((U t - finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim) y)| ≤
          (‖A - finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim‖ *
            Real.exp (-((t - t₀) * exactGapValueReal))) * ‖x‖ * ‖y‖ := hmatrix
      _ = (‖A - finiteWilsonConstructedHamiltonianRightSteadyState D n F_lim‖ *
            ‖x‖ * ‖y‖) * Real.exp (-((t - t₀) * exactGapValueReal)) := by ring

end

end MathlibAnalytic
end MGAP4D
