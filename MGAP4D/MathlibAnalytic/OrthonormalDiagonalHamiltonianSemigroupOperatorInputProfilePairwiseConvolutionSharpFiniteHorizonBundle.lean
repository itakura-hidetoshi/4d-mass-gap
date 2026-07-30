import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamelMassGapBound
import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorBoundedInputDifferencePairwiseInputToStateBundle
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open MeasureTheory

/-- The exponential memory of a constant input mismatch has the exact finite-horizon gain. -/
theorem intervalIntegral_exp_memory_mul_const_eq_finiteHorizonGain
    (δ C t₀ t : ℝ) (ht : t₀ ≤ t) (hδpos : 0 < δ) :
    (∫ s in t₀..t, Real.exp (-((t - s) * δ)) * C) =
      ((1 - Real.exp (-((t - t₀) * δ))) / δ) * C := by
  have hmemory :
      (∫ s in t₀..t, Real.exp (-((t - s) * δ))) =
        (1 - Real.exp (-((t - t₀) * δ))) / δ := by
    have hclosed :=
      intervalIntegral_exp_memory_mul_exp_tail_eq_div δ 0 t₀ t (by linarith)
    simpa using hclosed
  rw [intervalIntegral.integral_mul_const, hmemory]

/-- A continuous input mismatch bounded by `C` has at most the exact finite-horizon gain. -/
theorem intervalIntegral_exp_memory_norm_sub_le_finiteHorizonGain
    {E : Type*} [NormedAddCommGroup E]
    (δ C t₀ t : ℝ) (ht : t₀ ≤ t) (hδpos : 0 < δ)
    (F G : ℝ → E) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖F s - G s‖ ≤ C) :
    (∫ s in t₀..t, Real.exp (-((t - s) * δ)) * ‖F s - G s‖) ≤
      ((1 - Real.exp (-((t - t₀) * δ))) / δ) * C := by
  have hQ : Continuous (fun s : ℝ => F s - G s) := hF.sub hG
  have hleftContinuous : Continuous (fun s : ℝ =>
      Real.exp (-((t - s) * δ)) * ‖F s - G s‖) := by
    fun_prop
  have hrightContinuous : Continuous (fun s : ℝ =>
      Real.exp (-((t - s) * δ)) * C) := by
    fun_prop
  have hmono :
      (∫ s in t₀..t, Real.exp (-((t - s) * δ)) * ‖F s - G s‖) ≤
        ∫ s in t₀..t, Real.exp (-((t - s) * δ)) * C := by
    apply intervalIntegral.integral_mono_on ht
      (hleftContinuous.intervalIntegrable t₀ t)
      (hrightContinuous.intervalIntegrable t₀ t)
    intro s hs
    exact mul_le_mul_of_nonneg_left (hFG s hs.1) (Real.exp_pos _).le
  exact hmono.trans_eq
    (intervalIntegral_exp_memory_mul_const_eq_finiteHorizonGain
      δ C t₀ t ht hδpos)

private theorem orthonormalDiagonal_pairwise_left_deriv
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ)
    (F G U V : ℝ → (E →L[ℝ] E))
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V ((-orthonormalDiagonalOperator b a) * V r + G r) r) :
    ∀ r : ℝ,
      HasDerivAt (fun s : ℝ => U s - V s)
        ((-orthonormalDiagonalOperator b a) * (U r - V r) + (F r - G r)) r := by
  intro r
  have hsub := (hU r).sub (hV r)
  convert hsub using 1
  noncomm_ring

private theorem orthonormalDiagonal_pairwise_right_deriv
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ)
    (F G U V : ℝ → (E →L[ℝ] E))
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V (V r * (-orthonormalDiagonalOperator b a) + G r) r) :
    ∀ r : ℝ,
      HasDerivAt (fun s : ℝ => U s - V s)
        ((U r - V r) * (-orthonormalDiagonalOperator b a) + (F r - G r)) r := by
  intro r
  have hsub := (hU r).sub (hV r)
  convert hsub using 1
  noncomm_ring

/-- Left trajectories retain the complete exponentially weighted input-difference profile. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_inputProfile_pairwise_convolution_bound_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : E →L[ℝ] E)
    (F G U V : ℝ → (E →L[ℝ] E))
    (hF : Continuous F) (hG : Continuous G)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V ((-orthonormalDiagonalOperator b a) * V r + G r) r) :
    ‖U t - V t‖ ≤
      Real.exp (-((t - t₀) * δ)) * ‖A - B‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * δ)) * ‖F s - G s‖ := by
  have hQ : Continuous (fun r : ℝ => F r - G r) := hF.sub hG
  have hW0 : (fun r : ℝ => U r - V r) t₀ = A - B := by
    simp [hU0, hV0]
  have hmass :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_massGap_bound_left
      b a δ hδ t₀ t ht (A - B) (fun r : ℝ => F r - G r)
      (fun r : ℝ => U r - V r) hQ hW0
      (orthonormalDiagonal_pairwise_left_deriv b a F G U V hU hV)
  simpa using hmass

/-- Right trajectories have the identical profile-sensitive convolution estimate. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_inputProfile_pairwise_convolution_bound_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : E →L[ℝ] E)
    (F G U V : ℝ → (E →L[ℝ] E))
    (hF : Continuous F) (hG : Continuous G)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V (V r * (-orthonormalDiagonalOperator b a) + G r) r) :
    ‖U t - V t‖ ≤
      Real.exp (-((t - t₀) * δ)) * ‖A - B‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * δ)) * ‖F s - G s‖ := by
  have hQ : Continuous (fun r : ℝ => F r - G r) := hF.sub hG
  have hW0 : (fun r : ℝ => U r - V r) t₀ = A - B := by
    simp [hU0, hV0]
  have hmass :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_massGap_bound_right
      b a δ hδ t₀ t ht (A - B) (fun r : ℝ => F r - G r)
      (fun r : ℝ => U r - V r) hQ hW0
      (orthonormalDiagonal_pairwise_right_deriv b a F G U V hU hV)
  simpa using hmass

/-- The left convolution estimate acts pointwise. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_inputProfile_pairwise_pointwise_convolution_bound_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : E →L[ℝ] E) (F G U V : ℝ → (E →L[ℝ] E))
    (hF : Continuous F) (hG : Continuous G) (y : E)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V ((-orthonormalDiagonalOperator b a) * V r + G r) r) :
    ‖(U t - V t) y‖ ≤
      (Real.exp (-((t - t₀) * δ)) * ‖A - B‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * δ)) * ‖F s - G s‖) * ‖y‖ := by
  have henv :=
    orthonormalDiagonalHamiltonianSemigroup_operator_inputProfile_pairwise_convolution_bound_left
      b a δ hδ t₀ t ht A B F G U V hF hG hU0 hV0 hU hV
  calc
    ‖(U t - V t) y‖ ≤ ‖U t - V t‖ * ‖y‖ := (U t - V t).le_opNorm y
    _ ≤ (Real.exp (-((t - t₀) * δ)) * ‖A - B‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * δ)) * ‖F s - G s‖) * ‖y‖ :=
      mul_le_mul_of_nonneg_right henv (norm_nonneg y)

/-- The right convolution estimate acts pointwise without commutation. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_inputProfile_pairwise_pointwise_convolution_bound_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : E →L[ℝ] E) (F G U V : ℝ → (E →L[ℝ] E))
    (hF : Continuous F) (hG : Continuous G) (y : E)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V (V r * (-orthonormalDiagonalOperator b a) + G r) r) :
    ‖(U t - V t) y‖ ≤
      (Real.exp (-((t - t₀) * δ)) * ‖A - B‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * δ)) * ‖F s - G s‖) * ‖y‖ := by
  have henv :=
    orthonormalDiagonalHamiltonianSemigroup_operator_inputProfile_pairwise_convolution_bound_right
      b a δ hδ t₀ t ht A B F G U V hF hG hU0 hV0 hU hV
  calc
    ‖(U t - V t) y‖ ≤ ‖U t - V t‖ * ‖y‖ := (U t - V t).le_opNorm y
    _ ≤ (Real.exp (-((t - t₀) * δ)) * ‖A - B‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * δ)) * ‖F s - G s‖) * ‖y‖ :=
      mul_le_mul_of_nonneg_right henv (norm_nonneg y)

/-- Every left matrix element inherits the complete convolution profile. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_inputProfile_pairwise_matrixElement_convolution_bound_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : E →L[ℝ] E) (F G U V : ℝ → (E →L[ℝ] E))
    (hF : Continuous F) (hG : Continuous G) (x y : E)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V ((-orthonormalDiagonalOperator b a) * V r + G r) r) :
    |inner ℝ x ((U t - V t) y)| ≤
      (Real.exp (-((t - t₀) * δ)) * ‖A - B‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * δ)) * ‖F s - G s‖) * ‖x‖ * ‖y‖ := by
  have hpoint :=
    orthonormalDiagonalHamiltonianSemigroup_operator_inputProfile_pairwise_pointwise_convolution_bound_left
      b a δ hδ t₀ t ht A B F G U V hF hG y hU0 hV0 hU hV
  have hcs : |inner ℝ x ((U t - V t) y)| ≤ ‖x‖ * ‖(U t - V t) y‖ := by
    simpa only [Real.norm_eq_abs] using
      (norm_inner_le_norm (𝕜 := ℝ) x ((U t - V t) y))
  calc
    |inner ℝ x ((U t - V t) y)| ≤ ‖x‖ * ‖(U t - V t) y‖ := hcs
    _ ≤ ‖x‖ * ((Real.exp (-((t - t₀) * δ)) * ‖A - B‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * δ)) * ‖F s - G s‖) * ‖y‖ :=
      mul_le_mul_of_nonneg_left hpoint (norm_nonneg x)
    _ = (Real.exp (-((t - t₀) * δ)) * ‖A - B‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * δ)) * ‖F s - G s‖) * ‖x‖ * ‖y‖ := by ring

/-- Every right matrix element inherits the complete convolution profile. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_inputProfile_pairwise_matrixElement_convolution_bound_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : E →L[ℝ] E) (F G U V : ℝ → (E →L[ℝ] E))
    (hF : Continuous F) (hG : Continuous G) (x y : E)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V (V r * (-orthonormalDiagonalOperator b a) + G r) r) :
    |inner ℝ x ((U t - V t) y)| ≤
      (Real.exp (-((t - t₀) * δ)) * ‖A - B‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * δ)) * ‖F s - G s‖) * ‖x‖ * ‖y‖ := by
  have hpoint :=
    orthonormalDiagonalHamiltonianSemigroup_operator_inputProfile_pairwise_pointwise_convolution_bound_right
      b a δ hδ t₀ t ht A B F G U V hF hG y hU0 hV0 hU hV
  have hcs : |inner ℝ x ((U t - V t) y)| ≤ ‖x‖ * ‖(U t - V t) y‖ := by
    simpa only [Real.norm_eq_abs] using
      (norm_inner_le_norm (𝕜 := ℝ) x ((U t - V t) y))
  calc
    |inner ℝ x ((U t - V t) y)| ≤ ‖x‖ * ‖(U t - V t) y‖ := hcs
    _ ≤ ‖x‖ * ((Real.exp (-((t - t₀) * δ)) * ‖A - B‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * δ)) * ‖F s - G s‖) * ‖y‖ :=
      mul_le_mul_of_nonneg_left hpoint (norm_nonneg x)
    _ = (Real.exp (-((t - t₀) * δ)) * ‖A - B‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * δ)) * ‖F s - G s‖) * ‖x‖ * ‖y‖ := by ring

/-- Direct left matrix-element differences have the complete convolution bound. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_inputProfile_pairwise_matrixElement_sub_convolution_bound_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : E →L[ℝ] E) (F G U V : ℝ → (E →L[ℝ] E))
    (hF : Continuous F) (hG : Continuous G) (x y : E)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V ((-orthonormalDiagonalOperator b a) * V r + G r) r) :
    |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤
      (Real.exp (-((t - t₀) * δ)) * ‖A - B‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * δ)) * ‖F s - G s‖) * ‖x‖ * ‖y‖ := by
  rw [continuousLinearMap_abs_inner_apply_sub_inner_apply_eq_abs_inner_sub_apply]
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_inputProfile_pairwise_matrixElement_convolution_bound_left
      b a δ hδ t₀ t ht A B F G U V hF hG x y hU0 hV0 hU hV

/-- Direct right matrix-element differences have the complete convolution bound. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_inputProfile_pairwise_matrixElement_sub_convolution_bound_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : E →L[ℝ] E) (F G U V : ℝ → (E →L[ℝ] E))
    (hF : Continuous F) (hG : Continuous G) (x y : E)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V (V r * (-orthonormalDiagonalOperator b a) + G r) r) :
    |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤
      (Real.exp (-((t - t₀) * δ)) * ‖A - B‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * δ)) * ‖F s - G s‖) * ‖x‖ * ‖y‖ := by
  rw [continuousLinearMap_abs_inner_apply_sub_inner_apply_eq_abs_inner_sub_apply]
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_inputProfile_pairwise_matrixElement_convolution_bound_right
      b a δ hδ t₀ t ht A B F G U V hF hG x y hU0 hV0 hU hV

/-- One profile-sensitive bound controls all left matrix elements on both closed unit balls. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_inputProfile_pairwise_unitBall_matrixElement_sub_convolution_bound_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : E →L[ℝ] E) (F G U V : ℝ → (E →L[ℝ] E))
    (hF : Continuous F) (hG : Continuous G)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V ((-orthonormalDiagonalOperator b a) * V r + G r) r) :
    ∀ x y : E, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
      |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤
        Real.exp (-((t - t₀) * δ)) * ‖A - B‖ +
          ∫ s in t₀..t, Real.exp (-((t - s) * δ)) * ‖F s - G s‖ := by
  intro x y hx hy
  have hmatrix :=
    continuousLinearMap_abs_inner_apply_sub_inner_apply_le_norm_of_norm_le_one
      (U t) (V t) x y hx hy
  exact hmatrix.trans
    (orthonormalDiagonalHamiltonianSemigroup_operator_inputProfile_pairwise_convolution_bound_left
      b a δ hδ t₀ t ht A B F G U V hF hG hU0 hV0 hU hV)

/-- One profile-sensitive bound controls all right matrix elements on both unit balls. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_inputProfile_pairwise_unitBall_matrixElement_sub_convolution_bound_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : E →L[ℝ] E) (F G U V : ℝ → (E →L[ℝ] E))
    (hF : Continuous F) (hG : Continuous G)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V (V r * (-orthonormalDiagonalOperator b a) + G r) r) :
    ∀ x y : E, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
      |inner ℝ x (U t y) - inner ℝ x (V t y)| ≤
        Real.exp (-((t - t₀) * δ)) * ‖A - B‖ +
          ∫ s in t₀..t, Real.exp (-((t - s) * δ)) * ‖F s - G s‖ := by
  intro x y hx hy
  have hmatrix :=
    continuousLinearMap_abs_inner_apply_sub_inner_apply_le_norm_of_norm_le_one
      (U t) (V t) x y hx hy
  exact hmatrix.trans
    (orthonormalDiagonalHamiltonianSemigroup_operator_inputProfile_pairwise_convolution_bound_right
      b a δ hδ t₀ t ht A B F G U V hF hG hU0 hV0 hU hV)

/-- Uniformly bounded left input mismatch has the sharp finite-horizon gain. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_boundedInputDifference_pairwise_sharp_finiteHorizon_bound_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : E →L[ℝ] E) (F G U V : ℝ → (E →L[ℝ] E))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖F s - G s‖ ≤ C)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V ((-orthonormalDiagonalOperator b a) * V r + G r) r) :
    ‖U t - V t‖ ≤
      Real.exp (-((t - t₀) * δ)) * ‖A - B‖ +
        ((1 - Real.exp (-((t - t₀) * δ))) / δ) * C := by
  have hconv :=
    orthonormalDiagonalHamiltonianSemigroup_operator_inputProfile_pairwise_convolution_bound_left
      b a δ hδ t₀ t ht A B F G U V hF hG hU0 hV0 hU hV
  have hforcing :=
    intervalIntegral_exp_memory_norm_sub_le_finiteHorizonGain
      δ C t₀ t ht hδpos F G hF hG hFG
  exact hconv.trans (add_le_add_left hforcing _)

/-- Uniformly bounded right input mismatch has the same sharp finite-horizon gain. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_boundedInputDifference_pairwise_sharp_finiteHorizon_bound_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A B : E →L[ℝ] E) (F G U V : ℝ → (E →L[ℝ] E))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖F s - G s‖ ≤ C)
    (hU0 : U t₀ = A) (hV0 : V t₀ = B)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V (V r * (-orthonormalDiagonalOperator b a) + G r) r) :
    ‖U t - V t‖ ≤
      Real.exp (-((t - t₀) * δ)) * ‖A - B‖ +
        ((1 - Real.exp (-((t - t₀) * δ))) / δ) * C := by
  have hconv :=
    orthonormalDiagonalHamiltonianSemigroup_operator_inputProfile_pairwise_convolution_bound_right
      b a δ hδ t₀ t ht A B F G U V hF hG hU0 hV0 hU hV
  have hforcing :=
    intervalIntegral_exp_memory_norm_sub_le_finiteHorizonGain
      δ C t₀ t ht hδpos F G hF hG hFG
  exact hconv.trans (add_le_add_left hforcing _)

/-- With equal initial operators, the left trajectory difference is purely the finite-horizon input gain. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_boundedInputDifference_pairwise_equalInitial_sharp_finiteHorizon_gain_left
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A : E →L[ℝ] E) (F G U V : ℝ → (E →L[ℝ] E))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖F s - G s‖ ≤ C)
    (hU0 : U t₀ = A) (hV0 : V t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V ((-orthonormalDiagonalOperator b a) * V r + G r) r) :
    ‖U t - V t‖ ≤ ((1 - Real.exp (-((t - t₀) * δ))) / δ) * C := by
  have hsharp :=
    orthonormalDiagonalHamiltonianSemigroup_operator_boundedInputDifference_pairwise_sharp_finiteHorizon_bound_left
      b a δ hδ hδpos t₀ t ht A A F G U V C hC hF hG hFG hU0 hV0 hU hV
  simpa using hsharp

/-- With equal initial operators, the right trajectory difference is purely the finite-horizon input gain. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_boundedInputDifference_pairwise_equalInitial_sharp_finiteHorizon_gain_right
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ)
    (t₀ t : ℝ) (ht : t₀ ≤ t)
    (A : E →L[ℝ] E) (F G U V : ℝ → (E →L[ℝ] E))
    (C : ℝ) (hC : 0 ≤ C) (hF : Continuous F) (hG : Continuous G)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖F s - G s‖ ≤ C)
    (hU0 : U t₀ = A) (hV0 : V t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V (V r * (-orthonormalDiagonalOperator b a) + G r) r) :
    ‖U t - V t‖ ≤ ((1 - Real.exp (-((t - t₀) * δ))) / δ) * C := by
  have hsharp :=
    orthonormalDiagonalHamiltonianSemigroup_operator_boundedInputDifference_pairwise_sharp_finiteHorizon_bound_right
      b a δ hδ hδpos t₀ t ht A A F G U V C hC hF hG hFG hU0 hV0 hU hV
  simpa using hsharp

end

end MathlibAnalytic
end MGAP4D