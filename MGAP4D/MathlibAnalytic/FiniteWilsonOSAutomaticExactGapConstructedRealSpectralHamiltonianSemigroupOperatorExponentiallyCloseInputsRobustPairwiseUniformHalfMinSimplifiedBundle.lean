import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorExponentiallyCloseInputsRobustPairwiseUniformHalfMinSimplifiedBundle
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorDuhamelAsymptoticallyConstantInputMatrixElementUniformHalfMinSimplifiedBundle

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Constructed finite Wilson left trajectories with exponentially close inputs obey
    the robust exact-gap half-min envelope. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_exponentialTracking_uniform_halfMin_simplified_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (μ : ℝ) (hμpos : 0 < μ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (F G U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - G s‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * V r + G r) r) :
    ‖U t - V t‖ ≤
      (‖A - B‖ + 2 * C / max exactGapValueReal μ) *
        Real.exp (-((t - t₀) * (min exactGapValueReal μ / 2))) := by
  have hUdiag : ∀ r : ℝ,
      HasDerivAt U
        ((-orthonormalDiagonalOperator
          ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
          ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)) * U r + F r) r := by
    intro r
    simpa [finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n] using hU r
  have hVdiag : ∀ r : ℝ,
      HasDerivAt V
        ((-orthonormalDiagonalOperator
          ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
          ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)) * V r + G r) r := by
    intro r
    simpa [finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n] using hV r
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_exponentialTracking_uniform_halfMin_simplified_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal μ (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos hμpos t₀ t ht A B F G U V C hC hF hG hFG
      hU0 hV0 hUdiag hVdiag

/-- The constructed finite Wilson right-action envelope is identical. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_exponentialTracking_uniform_halfMin_simplified_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (μ : ℝ) (hμpos : 0 < μ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (F G U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - G s‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        (V r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + G r) r) :
    ‖U t - V t‖ ≤
      (‖A - B‖ + 2 * C / max exactGapValueReal μ) *
        Real.exp (-((t - t₀) * (min exactGapValueReal μ / 2))) := by
  have hUdiag : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-orthonormalDiagonalOperator
          ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
          ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)) + F r) r := by
    intro r
    simpa [finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n] using hU r
  have hVdiag : ∀ r : ℝ,
      HasDerivAt V
        (V r * (-orthonormalDiagonalOperator
          ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
          ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)) + G r) r := by
    intro r
    simpa [finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n] using hV r
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_exponentialTracking_uniform_halfMin_simplified_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal μ (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos hμpos t₀ t ht A B F G U V C hC hF hG hFG
      hU0 hV0 hUdiag hVdiag

/-- Constructed finite Wilson left operator distance has the explicit robust waiting time. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_norm_sub_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (μ : ℝ) (hμpos : 0 < μ) (t₀ : ℝ)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (F G U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - G s‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * V r + G r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log (((‖A - B‖ + 2 * C / max exactGapValueReal μ) / ε)) /
            (min exactGapValueReal μ / 2)) ≤ t →
        ‖U t - V t‖ ≤ ε := by
  intro t ht
  have hmaxpos : 0 < max exactGapValueReal μ :=
    lt_of_lt_of_le exactGapValueReal_pos (le_max_left _ _)
  have hcoeff : 0 ≤ ‖A - B‖ + 2 * C / max exactGapValueReal μ :=
    add_nonneg (norm_nonneg _)
      (div_nonneg (mul_nonneg (by norm_num) hC) hmaxpos.le)
  have hsettle :=
    realFunction_abs_le_epsilon_after_exponentialBound
      (min exactGapValueReal μ / 2) ε
      (‖A - B‖ + 2 * C / max exactGapValueReal μ) t₀
      (div_pos (lt_min exactGapValueReal_pos hμpos) (by norm_num)) hε hcoeff
      (fun t : ℝ => ‖U t - V t‖)
      (by
        intro s hs
        have henv :=
          finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_exponentialTracking_uniform_halfMin_simplified_left
            D n μ hμpos t₀ s hs A B F G U V C hC hF hG hFG hU0 hV0 hU hV
        simpa [abs_of_nonneg (norm_nonneg (U s - V s))] using henv)
  simpa [abs_of_nonneg (norm_nonneg (U t - V t))] using hsettle t ht

/-- Constructed finite Wilson right operator distance has the identical waiting time. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_norm_sub_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (μ : ℝ) (hμpos : 0 < μ) (t₀ : ℝ)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (F G U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - G s‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        (V r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + G r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log (((‖A - B‖ + 2 * C / max exactGapValueReal μ) / ε)) /
            (min exactGapValueReal μ / 2)) ≤ t →
        ‖U t - V t‖ ≤ ε := by
  intro t ht
  have hmaxpos : 0 < max exactGapValueReal μ :=
    lt_of_lt_of_le exactGapValueReal_pos (le_max_left _ _)
  have hcoeff : 0 ≤ ‖A - B‖ + 2 * C / max exactGapValueReal μ :=
    add_nonneg (norm_nonneg _)
      (div_nonneg (mul_nonneg (by norm_num) hC) hmaxpos.le)
  have hsettle :=
    realFunction_abs_le_epsilon_after_exponentialBound
      (min exactGapValueReal μ / 2) ε
      (‖A - B‖ + 2 * C / max exactGapValueReal μ) t₀
      (div_pos (lt_min exactGapValueReal_pos hμpos) (by norm_num)) hε hcoeff
      (fun t : ℝ => ‖U t - V t‖)
      (by
        intro s hs
        have henv :=
          finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_exponentialTracking_uniform_halfMin_simplified_right
            D n μ hμpos t₀ s hs A B F G U V C hC hF hG hFG hU0 hV0 hU hV
        simpa [abs_of_nonneg (norm_nonneg (U s - V s))] using henv)
  simpa [abs_of_nonneg (norm_nonneg (U t - V t))] using hsettle t ht

/-- Constructed finite Wilson left robust tracking acts pointwise. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_pointwise_exponentialTracking_uniform_halfMin_simplified_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (μ : ℝ) (hμpos : 0 < μ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (F G U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - G s‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (y : D.StateSpace) (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * V r + G r) r) :
    ‖(U t - V t) y‖ ≤
      ((‖A - B‖ + 2 * C / max exactGapValueReal μ) *
        Real.exp (-((t - t₀) * (min exactGapValueReal μ / 2)))) * ‖y‖ := by
  have henv :=
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_exponentialTracking_uniform_halfMin_simplified_left
      D n μ hμpos t₀ t ht A B F G U V C hC hF hG hFG hU0 hV0 hU hV
  exact (U t - V t).le_opNorm y |>.trans
    (mul_le_mul_of_nonneg_right henv (norm_nonneg y))

/-- Constructed finite Wilson right robust tracking acts pointwise. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_pointwise_exponentialTracking_uniform_halfMin_simplified_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (μ : ℝ) (hμpos : 0 < μ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (F G U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - G s‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (y : D.StateSpace) (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        (V r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + G r) r) :
    ‖(U t - V t) y‖ ≤
      ((‖A - B‖ + 2 * C / max exactGapValueReal μ) *
        Real.exp (-((t - t₀) * (min exactGapValueReal μ / 2)))) * ‖y‖ := by
  have henv :=
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_exponentialTracking_uniform_halfMin_simplified_right
      D n μ hμpos t₀ t ht A B F G U V C hC hF hG hFG hU0 hV0 hU hV
  exact (U t - V t).le_opNorm y |>.trans
    (mul_le_mul_of_nonneg_right henv (norm_nonneg y))

/-- Constructed finite Wilson left pairwise matrix elements have the robust envelope. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_matrixElement_exponentialTracking_uniform_halfMin_simplified_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (μ : ℝ) (hμpos : 0 < μ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (F G U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - G s‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (x y : D.StateSpace) (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * V r + G r) r) :
    |inner ℝ x ((U t - V t) y)| ≤
      ((‖A - B‖ + 2 * C / max exactGapValueReal μ) *
        Real.exp (-((t - t₀) * (min exactGapValueReal μ / 2)))) * ‖x‖ * ‖y‖ := by
  have hpoint :=
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_pointwise_exponentialTracking_uniform_halfMin_simplified_left
      D n μ hμpos t₀ t ht A B F G U V C hC hF hG hFG y hU0 hV0 hU hV
  have hinner : |inner ℝ x ((U t - V t) y)| ≤ ‖x‖ * ‖(U t - V t) y‖ := by
    simpa only [Real.norm_eq_abs] using
      (norm_inner_le_norm (𝕜 := ℝ) x ((U t - V t) y))
  calc
    |inner ℝ x ((U t - V t) y)| ≤ ‖x‖ * ‖(U t - V t) y‖ := hinner
    _ ≤ ‖x‖ *
        (((‖A - B‖ + 2 * C / max exactGapValueReal μ) *
          Real.exp (-((t - t₀) * (min exactGapValueReal μ / 2)))) * ‖y‖) :=
      mul_le_mul_of_nonneg_left hpoint (norm_nonneg x)
    _ = ((‖A - B‖ + 2 * C / max exactGapValueReal μ) *
          Real.exp (-((t - t₀) * (min exactGapValueReal μ / 2)))) * ‖x‖ * ‖y‖ := by ring

/-- Constructed finite Wilson right pairwise matrix elements have the same envelope. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_matrixElement_exponentialTracking_uniform_halfMin_simplified_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (μ : ℝ) (hμpos : 0 < μ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (F G U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - G s‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (x y : D.StateSpace) (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        (V r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + G r) r) :
    |inner ℝ x ((U t - V t) y)| ≤
      ((‖A - B‖ + 2 * C / max exactGapValueReal μ) *
        Real.exp (-((t - t₀) * (min exactGapValueReal μ / 2)))) * ‖x‖ * ‖y‖ := by
  have hpoint :=
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_pointwise_exponentialTracking_uniform_halfMin_simplified_right
      D n μ hμpos t₀ t ht A B F G U V C hC hF hG hFG y hU0 hV0 hU hV
  have hinner : |inner ℝ x ((U t - V t) y)| ≤ ‖x‖ * ‖(U t - V t) y‖ := by
    simpa only [Real.norm_eq_abs] using
      (norm_inner_le_norm (𝕜 := ℝ) x ((U t - V t) y))
  calc
    |inner ℝ x ((U t - V t) y)| ≤ ‖x‖ * ‖(U t - V t) y‖ := hinner
    _ ≤ ‖x‖ *
        (((‖A - B‖ + 2 * C / max exactGapValueReal μ) *
          Real.exp (-((t - t₀) * (min exactGapValueReal μ / 2)))) * ‖y‖) :=
      mul_le_mul_of_nonneg_left hpoint (norm_nonneg x)
    _ = ((‖A - B‖ + 2 * C / max exactGapValueReal μ) *
          Real.exp (-((t - t₀) * (min exactGapValueReal μ / 2)))) * ‖x‖ * ‖y‖ := by ring

/-- Constructed finite Wilson left direct matrix-element differences obey the robust envelope. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_matrixElement_sub_exponentialTracking_uniform_halfMin_simplified_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (μ : ℝ) (hμpos : 0 < μ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (F G U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - G s‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (x y : D.StateSpace) (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * V r + G r) r) :
    |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤
      ((‖A - B‖ + 2 * C / max exactGapValueReal μ) *
        Real.exp (-((t - t₀) * (min exactGapValueReal μ / 2)))) * ‖x‖ * ‖y‖ := by
  rw [continuousLinearMap_abs_inner_apply_sub_inner_apply_eq_abs_inner_sub_apply]
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_matrixElement_exponentialTracking_uniform_halfMin_simplified_left
      D n μ hμpos t₀ t ht A B F G U V C hC hF hG hFG x y hU0 hV0 hU hV

/-- Constructed finite Wilson right direct matrix-element differences obey the same envelope. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_matrixElement_sub_exponentialTracking_uniform_halfMin_simplified_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (μ : ℝ) (hμpos : 0 < μ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (F G U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - G s‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (x y : D.StateSpace) (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        (V r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + G r) r) :
    |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤
      ((‖A - B‖ + 2 * C / max exactGapValueReal μ) *
        Real.exp (-((t - t₀) * (min exactGapValueReal μ / 2)))) * ‖x‖ * ‖y‖ := by
  rw [continuousLinearMap_abs_inner_apply_sub_inner_apply_eq_abs_inner_sub_apply]
  exact
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_matrixElement_exponentialTracking_uniform_halfMin_simplified_right
      D n μ hμpos t₀ t ht A B F G U V C hC hF hG hFG x y hU0 hV0 hU hV

/-- Constructed finite Wilson left fixed matrix elements have the robust settling time. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_matrixElement_sub_abs_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (μ : ℝ) (hμpos : 0 < μ) (t₀ : ℝ)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (F G U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - G s‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (x y : D.StateSpace) (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * V r + G r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            ((((‖A - B‖ + 2 * C / max exactGapValueReal μ) * ‖x‖ * ‖y‖) / ε)) /
              (min exactGapValueReal μ / 2)) ≤ t →
        |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤ ε := by
  have hmaxpos : 0 < max exactGapValueReal μ :=
    lt_of_lt_of_le exactGapValueReal_pos (le_max_left _ _)
  have hcoeff : 0 ≤
      (‖A - B‖ + 2 * C / max exactGapValueReal μ) * ‖x‖ * ‖y‖ := by
    exact mul_nonneg
      (mul_nonneg
        (add_nonneg (norm_nonneg _)
          (div_nonneg (mul_nonneg (by norm_num) hC) hmaxpos.le))
        (norm_nonneg x))
      (norm_nonneg y)
  refine realFunction_abs_le_epsilon_after_exponentialBound
    (min exactGapValueReal μ / 2) ε
      ((‖A - B‖ + 2 * C / max exactGapValueReal μ) * ‖x‖ * ‖y‖) t₀
      (div_pos (lt_min exactGapValueReal_pos hμpos) (by norm_num)) hε hcoeff
      (fun t : ℝ => inner ℝ x (U t y) - inner ℝ x (V t y)) ?_
  intro t ht
  have hmatrix :=
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_matrixElement_sub_exponentialTracking_uniform_halfMin_simplified_left
      D n μ hμpos t₀ t ht A B F G U V C hC hF hG hFG x y hU0 hV0 hU hV
  calc
    |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤
        ((‖A - B‖ + 2 * C / max exactGapValueReal μ) *
          Real.exp (-((t - t₀) * (min exactGapValueReal μ / 2)))) * ‖x‖ * ‖y‖ := hmatrix
    _ = ((‖A - B‖ + 2 * C / max exactGapValueReal μ) * ‖x‖ * ‖y‖) *
          Real.exp (-((t - t₀) * (min exactGapValueReal μ / 2))) := by ring

/-- Constructed finite Wilson right fixed matrix elements have the same settling time. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_matrixElement_sub_abs_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (μ : ℝ) (hμpos : 0 < μ) (t₀ : ℝ)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (F G U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - G s‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (x y : D.StateSpace) (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        (V r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + G r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log
            ((((‖A - B‖ + 2 * C / max exactGapValueReal μ) * ‖x‖ * ‖y‖) / ε)) /
              (min exactGapValueReal μ / 2)) ≤ t →
        |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤ ε := by
  have hmaxpos : 0 < max exactGapValueReal μ :=
    lt_of_lt_of_le exactGapValueReal_pos (le_max_left _ _)
  have hcoeff : 0 ≤
      (‖A - B‖ + 2 * C / max exactGapValueReal μ) * ‖x‖ * ‖y‖ := by
    exact mul_nonneg
      (mul_nonneg
        (add_nonneg (norm_nonneg _)
          (div_nonneg (mul_nonneg (by norm_num) hC) hmaxpos.le))
        (norm_nonneg x))
      (norm_nonneg y)
  refine realFunction_abs_le_epsilon_after_exponentialBound
    (min exactGapValueReal μ / 2) ε
      ((‖A - B‖ + 2 * C / max exactGapValueReal μ) * ‖x‖ * ‖y‖) t₀
      (div_pos (lt_min exactGapValueReal_pos hμpos) (by norm_num)) hε hcoeff
      (fun t : ℝ => inner ℝ x (U t y) - inner ℝ x (V t y)) ?_
  intro t ht
  have hmatrix :=
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_matrixElement_sub_exponentialTracking_uniform_halfMin_simplified_right
      D n μ hμpos t₀ t ht A B F G U V C hC hF hG hFG x y hU0 hV0 hU hV
  calc
    |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤
        ((‖A - B‖ + 2 * C / max exactGapValueReal μ) *
          Real.exp (-((t - t₀) * (min exactGapValueReal μ / 2)))) * ‖x‖ * ‖y‖ := hmatrix
    _ = ((‖A - B‖ + 2 * C / max exactGapValueReal μ) * ‖x‖ * ‖y‖) *
          Real.exp (-((t - t₀) * (min exactGapValueReal μ / 2))) := by ring

/-- Constructed finite Wilson left unit-ball matrix elements settle uniformly. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_unitBall_matrixElement_sub_abs_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (μ : ℝ) (hμpos : 0 < μ) (t₀ : ℝ)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (F G U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - G s‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * V r + G r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log (((‖A - B‖ + 2 * C / max exactGapValueReal μ) / ε)) /
            (min exactGapValueReal μ / 2)) ≤ t →
        ∀ x y : D.StateSpace, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
          |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤ ε := by
  intro t ht x y hx hy
  have hmatrix :=
    continuousLinearMap_abs_inner_apply_sub_inner_apply_le_norm_of_norm_le_one
      (U t) (V t) x y hx hy
  exact hmatrix.trans
    (finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_norm_sub_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_left
      D n μ hμpos t₀ A B F G U V C hC hF hG hFG hU0 hV0 hU hV ε hε t ht)

/-- Constructed finite Wilson right unit-ball matrix elements settle uniformly. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_unitBall_matrixElement_sub_abs_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (μ : ℝ) (hμpos : 0 < μ) (t₀ : ℝ)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (F G U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s →
      ‖F s - G s‖ ≤ C * Real.exp (-((s - t₀) * μ)))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        (V r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + G r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log (((‖A - B‖ + 2 * C / max exactGapValueReal μ) / ε)) /
            (min exactGapValueReal μ / 2)) ≤ t →
        ∀ x y : D.StateSpace, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
          |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤ ε := by
  intro t ht x y hx hy
  have hmatrix :=
    continuousLinearMap_abs_inner_apply_sub_inner_apply_le_norm_of_norm_le_one
      (U t) (V t) x y hx hy
  exact hmatrix.trans
    (finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_exponentiallyCloseInputs_pairwise_norm_sub_le_epsilon_after_exponentialTracking_uniform_halfMin_simplified_right
      D n μ hμpos t₀ A B F G U V C hC hF hG hFG hU0 hV0 hU hV ε hε t ht)

end

end MathlibAnalytic
end MGAP4D
