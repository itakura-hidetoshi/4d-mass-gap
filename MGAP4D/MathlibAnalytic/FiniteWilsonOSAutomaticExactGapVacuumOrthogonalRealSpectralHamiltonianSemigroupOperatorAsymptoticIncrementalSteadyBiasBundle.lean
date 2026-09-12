import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorAsymptoticIncrementalSteadyBiasBundle
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapVacuumOrthogonalRealSpectralHamiltonianSemigroupOperatorVanishingInputDifferencePairwiseAsymptoticIncrementalStabilityBundle

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter

/-- Exact inverse of the finite Wilson Hamiltonian restricted to `Ω⊥`. -/
noncomputable def finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianInverse
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ) :
    D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace :=
  finite_wilson_constructed_real_spectral_hamiltonianInverse
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n

/-- Left `Ω⊥` steady response `H_{Ω⊥}⁻¹ Qinf`. -/
noncomputable def finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseLeft
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (Qinf : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace) :
    D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace :=
  finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseLeft
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n Qinf

/-- Right `Ω⊥` steady response `Qinf H_{Ω⊥}⁻¹`. -/
noncomputable def finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseRight
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (Qinf : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace) :
    D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace :=
  finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseRight
    D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n Qinf

/-- The left `Ω⊥` steady response solves `H_{Ω⊥} W∞ = Qinf`. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseLeft_equilibrium
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (Qinf : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace) :
    LinearMap.toContinuousLinearMap (D.gapData.restrictedHamiltonian n) *
      finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseLeft D n Qinf = Qinf := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseLeft_equilibrium
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n Qinf

/-- The right `Ω⊥` steady response solves `W∞ H_{Ω⊥} = Qinf` without commutation. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseRight_equilibrium
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
    (n : ℕ)
    (Qinf : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace) :
    finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseRight D n Qinf *
      LinearMap.toContinuousLinearMap (D.gapData.restrictedHamiltonian n) = Qinf := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSteadyResponseRight_equilibrium
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData n Qinf
section Left

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
variable (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
variable (n : ℕ)
variable (Qinf : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
variable (F G U V : ℝ →
  (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
variable (hF : Continuous F) (hG : Continuous G)
variable (hFGinf : Tendsto (fun t : ℝ => ‖(F t - G t) - Qinf‖) atTop (nhds 0))
variable (hU : ∀ r : ℝ, HasDerivAt U ((-LinearMap.toContinuousLinearMap (D.gapData.restrictedHamiltonian n)) * U r + F r) r)
variable (hV : ∀ r : ℝ, HasDerivAt V ((-LinearMap.toContinuousLinearMap (D.gapData.restrictedHamiltonian n)) * V r + G r) r)

include n F G hF hG hFGinf hU hV
/-- On `Ω⊥`, the left mismatch converges in norm to its exact steady bias. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_norm_sub_steadyResponse_zero_left :
    Tendsto (fun t : ℝ => ‖(U t - V t) - finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseLeft D n Qinf‖) atTop (nhds 0) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_norm_sub_steadyResponse_zero_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n Qinf F G U V hF hG hFGinf hU hV

/-- On `Ω⊥`, the left mismatch converges in operator space to its steady response. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_steadyResponse_left :
    Tendsto (fun t : ℝ => U t - V t) atTop (nhds (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseLeft D n Qinf)) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_steadyResponse_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n Qinf F G U V hF hG hFGinf hU hV

/-- On `Ω⊥`, the left mismatch converges strongly on each state. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_apply_steadyResponse_left
    (y : D.gapData.ExcitedStateSpace) :
    Tendsto (fun t : ℝ => (U t - V t) y) atTop (nhds (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseLeft D n Qinf y)) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_apply_steadyResponse_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n Qinf F G U V hF hG hFGinf hU hV y

/-- Direct `Ω⊥` left action differences converge to the steady response. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_apply_difference_steadyResponse_left
    (y : D.gapData.ExcitedStateSpace) :
    Tendsto (fun t : ℝ => U t y - V t y) atTop (nhds (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseLeft D n Qinf y)) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_apply_difference_steadyResponse_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n Qinf F G U V hF hG hFGinf hU hV y

/-- `Ω⊥` left matrix-element differences converge to the steady value. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_matrixElement_difference_steadyResponse_left
    (x y : D.gapData.ExcitedStateSpace) :
    Tendsto (fun t : ℝ => inner ℝ x (U t y) - inner ℝ x (V t y))
      atTop (nhds (inner ℝ x (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseLeft D n Qinf y))) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_matrixElement_difference_steadyResponse_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n Qinf F G U V hF hG hFGinf hU hV x y

/-- Absolute `Ω⊥` left matrix elements converge to the absolute steady value. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_abs_matrixElement_difference_steadyResponse_left
    (x y : D.gapData.ExcitedStateSpace) :
    Tendsto (fun t : ℝ => |inner ℝ x (U t y) - inner ℝ x (V t y)|)
      atTop (nhds |inner ℝ x (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseLeft D n Qinf y)|) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_abs_matrixElement_difference_steadyResponse_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n Qinf F G U V hF hG hFGinf hU hV x y

/-- One time controls the `Ω⊥` left steady-bias error on both unit balls. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_eventually_uniform_unitBall_matrixElement_error_left :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ in atTop,
      ∀ x y : D.gapData.ExcitedStateSpace, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
        |inner ℝ x (U t y) - inner ℝ x (V t y) - inner ℝ x (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseLeft D n Qinf y)| < ε := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_eventually_uniform_unitBall_matrixElement_error_left
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n Qinf F G U V hF hG hFGinf hU hV

end Left

section Right

variable {W : FiniteWilsonOSAutomaticApproximationFamily}
variable (D : FiniteWilsonOSAutomaticExactGapVacuumOrthogonalCoerciveTransferOrbitContractionData W)
variable (n : ℕ)
variable (Qinf : D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace)
variable (F G U V : ℝ →
  (D.gapData.ExcitedStateSpace →L[ℝ] D.gapData.ExcitedStateSpace))
variable (hF : Continuous F) (hG : Continuous G)
variable (hFGinf : Tendsto (fun t : ℝ => ‖(F t - G t) - Qinf‖) atTop (nhds 0))
variable (hU : ∀ r : ℝ, HasDerivAt U (U r * (-LinearMap.toContinuousLinearMap (D.gapData.restrictedHamiltonian n)) + F r) r)
variable (hV : ∀ r : ℝ, HasDerivAt V (V r * (-LinearMap.toContinuousLinearMap (D.gapData.restrictedHamiltonian n)) + G r) r)

include n F G hF hG hFGinf hU hV
/-- On `Ω⊥`, the right mismatch converges in norm to its exact steady bias. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_norm_sub_steadyResponse_zero_right :
    Tendsto (fun t : ℝ => ‖(U t - V t) - finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseRight D n Qinf‖) atTop (nhds 0) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_norm_sub_steadyResponse_zero_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n Qinf F G U V hF hG hFGinf hU hV

/-- On `Ω⊥`, the right mismatch converges in operator space to its steady response. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_steadyResponse_right :
    Tendsto (fun t : ℝ => U t - V t) atTop (nhds (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseRight D n Qinf)) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_steadyResponse_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n Qinf F G U V hF hG hFGinf hU hV

/-- On `Ω⊥`, the right mismatch converges strongly on each state. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_apply_steadyResponse_right
    (y : D.gapData.ExcitedStateSpace) :
    Tendsto (fun t : ℝ => (U t - V t) y) atTop (nhds (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseRight D n Qinf y)) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_apply_steadyResponse_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n Qinf F G U V hF hG hFGinf hU hV y

/-- Direct `Ω⊥` right action differences converge to the steady response. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_apply_difference_steadyResponse_right
    (y : D.gapData.ExcitedStateSpace) :
    Tendsto (fun t : ℝ => U t y - V t y) atTop (nhds (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseRight D n Qinf y)) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_apply_difference_steadyResponse_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n Qinf F G U V hF hG hFGinf hU hV y

/-- `Ω⊥` right matrix-element differences converge to the steady value. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_matrixElement_difference_steadyResponse_right
    (x y : D.gapData.ExcitedStateSpace) :
    Tendsto (fun t : ℝ => inner ℝ x (U t y) - inner ℝ x (V t y))
      atTop (nhds (inner ℝ x (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseRight D n Qinf y))) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_matrixElement_difference_steadyResponse_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n Qinf F G U V hF hG hFGinf hU hV x y

/-- Absolute `Ω⊥` right matrix elements converge to the absolute steady value. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_abs_matrixElement_difference_steadyResponse_right
    (x y : D.gapData.ExcitedStateSpace) :
    Tendsto (fun t : ℝ => |inner ℝ x (U t y) - inner ℝ x (V t y)|)
      atTop (nhds |inner ℝ x (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseRight D n Qinf y)|) := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_abs_matrixElement_difference_steadyResponse_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n Qinf F G U V hF hG hFGinf hU hV x y

/-- One time controls the `Ω⊥` right steady-bias error on both unit balls. -/
theorem finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_eventually_uniform_unitBall_matrixElement_error_right :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ in atTop,
      ∀ x y : D.gapData.ExcitedStateSpace, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
        |inner ℝ x (U t y) - inner ℝ x (V t y) - inner ℝ x (finite_wilson_vacuum_orthogonal_real_spectral_hamiltonianSteadyResponseRight D n Qinf y)| < ε := by
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_eventually_uniform_unitBall_matrixElement_error_right
      D.toCoerciveTransferOrbitData.toConstructedTransferOrbitData
      n Qinf F G U V hF hG hFGinf hU hV

end Right

end

end MathlibAnalytic
end MGAP4D
