import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorCommonInputPairwiseFullGapBundle
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapConstructedRealSpectralHamiltonianSemigroupOperatorConstantInputExponentialTrackingEnvelopeFullGap

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Constructed finite Wilson left trajectories driven by the same arbitrary input
    contract at the full exact-gap rate. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_exponentialContraction_fullGap_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * V r + F r) r) :
    ‖U t - V t‖ ≤ ‖A - B‖ * Real.exp (-((t - t₀) * exactGapValueReal)) := by
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
          ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)) * V r + F r) r := by
    intro r
    simpa [finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n] using hV r
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_exponentialContraction_fullGap_left
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos t₀ t ht A B U V F hU0 hV0 hUdiag hVdiag

/-- Constructed finite Wilson right trajectories have the identical full exact-gap
    contraction estimate. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_exponentialContraction_fullGap_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        (V r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r) :
    ‖U t - V t‖ ≤ ‖A - B‖ * Real.exp (-((t - t₀) * exactGapValueReal)) := by
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
          ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)) + F r) r := by
    intro r
    simpa [finite_wilson_constructed_eigenDiagonalOperator_eq_hamiltonian D n] using hV r
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_commonInput_pairwise_exponentialContraction_fullGap_right
      ((D.hamiltonianSymmetric n).eigenvectorBasis D.stateFinrank)
      ((D.hamiltonianSymmetric n).eigenvalues D.stateFinrank)
      exactGapValueReal (D.hamiltonianEigenvalues_ge_exactGap n)
      exactGapValueReal_pos t₀ t ht A B U V F hU0 hV0 hUdiag hVdiag

/-- Constructed finite Wilson left pairwise operator distance reaches every positive
    tolerance after the exact-gap logarithmic waiting time. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_norm_sub_le_epsilon_after_exponentialContraction_fullGap_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ : ℝ)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * V r + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0 (Real.log (‖A - B‖ / ε) / exactGapValueReal) ≤ t →
        ‖U t - V t‖ ≤ ε := by
  refine realFunction_abs_le_epsilon_after_exponentialBound
    exactGapValueReal ε ‖A - B‖ t₀ exactGapValueReal_pos hε (norm_nonneg _)
      (fun t : ℝ => ‖U t - V t‖) ?_
  intro t ht
  have hcontract :=
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_exponentialContraction_fullGap_left
      D n t₀ t ht A B U V F hU0 hV0 hU hV
  simpa [abs_of_nonneg (norm_nonneg (U t - V t))] using hcontract

/-- Constructed finite Wilson right pairwise operator distance has the identical
    exact-gap waiting time. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_norm_sub_le_epsilon_after_exponentialContraction_fullGap_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ : ℝ)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        (V r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0 (Real.log (‖A - B‖ / ε) / exactGapValueReal) ≤ t →
        ‖U t - V t‖ ≤ ε := by
  refine realFunction_abs_le_epsilon_after_exponentialBound
    exactGapValueReal ε ‖A - B‖ t₀ exactGapValueReal_pos hε (norm_nonneg _)
      (fun t : ℝ => ‖U t - V t‖) ?_
  intro t ht
  have hcontract :=
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_exponentialContraction_fullGap_right
      D n t₀ t ht A B U V F hU0 hV0 hU hV
  simpa [abs_of_nonneg (norm_nonneg (U t - V t))] using hcontract

/-- Constructed finite Wilson left pairwise contraction acts pointwise. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_pointwise_exponentialContraction_fullGap_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F : ℝ → (D.StateSpace →L[ℝ] D.StateSpace)) (y : D.StateSpace)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * V r + F r) r) :
    ‖(U t - V t) y‖ ≤
      (‖A - B‖ * Real.exp (-((t - t₀) * exactGapValueReal))) * ‖y‖ := by
  have hcontract :=
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_exponentialContraction_fullGap_left
      D n t₀ t ht A B U V F hU0 hV0 hU hV
  calc
    ‖(U t - V t) y‖ ≤ ‖U t - V t‖ * ‖y‖ := (U t - V t).le_opNorm y
    _ ≤ (‖A - B‖ * Real.exp (-((t - t₀) * exactGapValueReal))) * ‖y‖ :=
      mul_le_mul_of_nonneg_right hcontract (norm_nonneg y)

/-- Constructed finite Wilson right pairwise contraction acts pointwise. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_pointwise_exponentialContraction_fullGap_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F : ℝ → (D.StateSpace →L[ℝ] D.StateSpace)) (y : D.StateSpace)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        (V r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r) :
    ‖(U t - V t) y‖ ≤
      (‖A - B‖ * Real.exp (-((t - t₀) * exactGapValueReal))) * ‖y‖ := by
  have hcontract :=
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_exponentialContraction_fullGap_right
      D n t₀ t ht A B U V F hU0 hV0 hU hV
  calc
    ‖(U t - V t) y‖ ≤ ‖U t - V t‖ * ‖y‖ := (U t - V t).le_opNorm y
    _ ≤ (‖A - B‖ * Real.exp (-((t - t₀) * exactGapValueReal))) * ‖y‖ :=
      mul_le_mul_of_nonneg_right hcontract (norm_nonneg y)

/-- Constructed finite Wilson left pairwise matrix elements contract at the exact gap. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_matrixElement_exponentialContraction_fullGap_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F : ℝ → (D.StateSpace →L[ℝ] D.StateSpace)) (x y : D.StateSpace)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * V r + F r) r) :
    |inner ℝ x ((U t - V t) y)| ≤
      (‖A - B‖ * Real.exp (-((t - t₀) * exactGapValueReal))) * ‖x‖ * ‖y‖ := by
  have hpoint :=
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_pointwise_exponentialContraction_fullGap_left
      D n t₀ t ht A B U V F y hU0 hV0 hU hV
  have hcs : |inner ℝ x ((U t - V t) y)| ≤ ‖x‖ * ‖(U t - V t) y‖ := by
    simpa only [Real.norm_eq_abs] using
      (norm_inner_le_norm (𝕜 := ℝ) x ((U t - V t) y))
  calc
    |inner ℝ x ((U t - V t) y)| ≤ ‖x‖ * ‖(U t - V t) y‖ := hcs
    _ ≤ ‖x‖ *
        ((‖A - B‖ * Real.exp (-((t - t₀) * exactGapValueReal))) * ‖y‖) :=
      mul_le_mul_of_nonneg_left hpoint (norm_nonneg x)
    _ = (‖A - B‖ * Real.exp (-((t - t₀) * exactGapValueReal))) * ‖x‖ * ‖y‖ := by
      ring

/-- Constructed finite Wilson right pairwise matrix elements have the same estimate. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_matrixElement_exponentialContraction_fullGap_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F : ℝ → (D.StateSpace →L[ℝ] D.StateSpace)) (x y : D.StateSpace)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        (V r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r) :
    |inner ℝ x ((U t - V t) y)| ≤
      (‖A - B‖ * Real.exp (-((t - t₀) * exactGapValueReal))) * ‖x‖ * ‖y‖ := by
  have hpoint :=
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_pointwise_exponentialContraction_fullGap_right
      D n t₀ t ht A B U V F y hU0 hV0 hU hV
  have hcs : |inner ℝ x ((U t - V t) y)| ≤ ‖x‖ * ‖(U t - V t) y‖ := by
    simpa only [Real.norm_eq_abs] using
      (norm_inner_le_norm (𝕜 := ℝ) x ((U t - V t) y))
  calc
    |inner ℝ x ((U t - V t) y)| ≤ ‖x‖ * ‖(U t - V t) y‖ := hcs
    _ ≤ ‖x‖ *
        ((‖A - B‖ * Real.exp (-((t - t₀) * exactGapValueReal))) * ‖y‖) :=
      mul_le_mul_of_nonneg_left hpoint (norm_nonneg x)
    _ = (‖A - B‖ * Real.exp (-((t - t₀) * exactGapValueReal))) * ‖x‖ * ‖y‖ := by
      ring

/-- Constructed finite Wilson left pairwise matrix elements have an explicit
    vector-dependent exact-gap settling time. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_matrixElement_abs_le_epsilon_after_exponentialContraction_fullGap_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ : ℝ)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F : ℝ → (D.StateSpace →L[ℝ] D.StateSpace)) (x y : D.StateSpace)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * V r + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log ((‖A - B‖ * ‖x‖ * ‖y‖) / ε) / exactGapValueReal) ≤ t →
        |inner ℝ x ((U t - V t) y)| ≤ ε := by
  refine realFunction_abs_le_epsilon_after_exponentialBound
    exactGapValueReal ε (‖A - B‖ * ‖x‖ * ‖y‖) t₀ exactGapValueReal_pos hε
      (by positivity) (fun t : ℝ => inner ℝ x ((U t - V t) y)) ?_
  intro t ht
  have hmatrix :=
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_matrixElement_exponentialContraction_fullGap_left
      D n t₀ t ht A B U V F x y hU0 hV0 hU hV
  calc
    |inner ℝ x ((U t - V t) y)| ≤
        (‖A - B‖ * Real.exp (-((t - t₀) * exactGapValueReal))) * ‖x‖ * ‖y‖ :=
      hmatrix
    _ = (‖A - B‖ * ‖x‖ * ‖y‖) *
        Real.exp (-((t - t₀) * exactGapValueReal)) := by ring

/-- Constructed finite Wilson right pairwise matrix elements have the same explicit
    settling time. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_matrixElement_abs_le_epsilon_after_exponentialContraction_fullGap_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ : ℝ)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F : ℝ → (D.StateSpace →L[ℝ] D.StateSpace)) (x y : D.StateSpace)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        (V r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0
          (Real.log ((‖A - B‖ * ‖x‖ * ‖y‖) / ε) / exactGapValueReal) ≤ t →
        |inner ℝ x ((U t - V t) y)| ≤ ε := by
  refine realFunction_abs_le_epsilon_after_exponentialBound
    exactGapValueReal ε (‖A - B‖ * ‖x‖ * ‖y‖) t₀ exactGapValueReal_pos hε
      (by positivity) (fun t : ℝ => inner ℝ x ((U t - V t) y)) ?_
  intro t ht
  have hmatrix :=
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_matrixElement_exponentialContraction_fullGap_right
      D n t₀ t ht A B U V F x y hU0 hV0 hU hV
  calc
    |inner ℝ x ((U t - V t) y)| ≤
        (‖A - B‖ * Real.exp (-((t - t₀) * exactGapValueReal))) * ‖x‖ * ‖y‖ :=
      hmatrix
    _ = (‖A - B‖ * ‖x‖ * ‖y‖) *
        Real.exp (-((t - t₀) * exactGapValueReal)) := by ring

/-- Constructed finite Wilson left pairwise matrix elements settle uniformly on
    both closed unit balls after the operator-norm exact-gap waiting time. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_unitBall_matrixElement_abs_le_epsilon_after_exponentialContraction_fullGap_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ : ℝ)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * V r + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0 (Real.log (‖A - B‖ / ε) / exactGapValueReal) ≤ t →
        ∀ x y : D.StateSpace, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
          |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤ ε := by
  intro t ht x y hx hy
  have hmatrix :=
    continuousLinearMap_abs_inner_apply_sub_inner_apply_le_norm_of_norm_le_one
      (U t) (V t) x y hx hy
  exact hmatrix.trans
    (finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_norm_sub_le_epsilon_after_exponentialContraction_fullGap_left
      D n t₀ A B U V F hU0 hV0 hU hV ε hε t ht)

/-- Constructed finite Wilson right pairwise matrix elements have the same unit-ball
    uniform waiting time. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_unitBall_matrixElement_abs_le_epsilon_after_exponentialContraction_fullGap_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ : ℝ)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        (V r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ t : ℝ,
      t₀ + max 0 (Real.log (‖A - B‖ / ε) / exactGapValueReal) ≤ t →
        ∀ x y : D.StateSpace, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
          |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤ ε := by
  intro t ht x y hx hy
  have hmatrix :=
    continuousLinearMap_abs_inner_apply_sub_inner_apply_le_norm_of_norm_le_one
      (U t) (V t) x y hx hy
  exact hmatrix.trans
    (finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_norm_sub_le_epsilon_after_exponentialContraction_fullGap_right
      D n t₀ A B U V F hU0 hV0 hU hV ε hε t ht)

/-- Constructed finite Wilson left evolution under a common arbitrary input is
    forward unique from equal initial operators. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_eq_of_sameInitial_fullGap_left
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        ((-LinearMap.toContinuousLinearMap (D.hamiltonian n)) * V r + F r) r)
    (hAB : A = B) :
    U t = V t := by
  have hcontract :=
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_exponentialContraction_fullGap_left
      D n t₀ t ht A B U V F hU0 hV0 hU hV
  have hzero : ‖U t - V t‖ ≤ 0 := by
    simpa [hAB] using hcontract
  have hnorm : ‖U t - V t‖ = 0 := le_antisymm hzero (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

/-- Constructed finite Wilson right evolution has the same forward uniqueness. -/
theorem finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_eq_of_sameInitial_fullGap_right
    {W : FiniteWilsonOSAutomaticApproximationFamily}
    (D : FiniteWilsonOSAutomaticExactGapConstructedTransferOrbitContractionData W)
    (n : ℕ) (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : D.StateSpace →L[ℝ] D.StateSpace)
    (U V : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (F : ℝ → (D.StateSpace →L[ℝ] D.StateSpace))
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U
        (U r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V
        (V r * (-LinearMap.toContinuousLinearMap (D.hamiltonian n)) + F r) r)
    (hAB : A = B) :
    U t = V t := by
  have hcontract :=
    finite_wilson_constructed_real_spectral_hamiltonianSemigroup_operator_commonInput_pairwise_exponentialContraction_fullGap_right
      D n t₀ t ht A B U V F hU0 hV0 hU hV
  have hzero : ‖U t - V t‖ ≤ 0 := by
    simpa [hAB] using hcontract
  have hnorm : ‖U t - V t‖ = 0 := le_antisymm hzero (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

end

end MathlibAnalytic
end MGAP4D
