import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorAsymptoticIncrementalSteadyBiasBundle
import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorInputProfilePairwiseConvolutionSharpFiniteHorizonBundle
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open MeasureTheory

private theorem orthonormalDiagonal_asymptoticIncrementalSteadyBiasFiniteHorizon_left_deriv
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ)
    (Qinf : E →L[ℝ] E)
    (F G U V : ℝ → (E →L[ℝ] E))
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V ((-orthonormalDiagonalOperator b a) * V r + G r) r) :
    ∀ r : ℝ,
      HasDerivAt
        (fun s : ℝ => (U s - V s) -
          orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf)
        ((-orthonormalDiagonalOperator b a) *
            ((U r - V r) -
              orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf) +
          ((F r - G r) - Qinf)) r := by
  intro r
  have hpair := (hU r).sub (hV r)
  have hshift := hpair.sub
    (hasDerivAt_const (x := r)
      (c := orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf))
  convert hshift using 1
  have heq := orthonormalDiagonalHamiltonianSteadyResponseLeft_equilibrium
    b a δ hδ hδpos Qinf
  noncomm_ring
  rw [heq]
  abel

private theorem orthonormalDiagonal_asymptoticIncrementalSteadyBiasFiniteHorizon_right_deriv
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ)
    (Qinf : E →L[ℝ] E)
    (F G U V : ℝ → (E →L[ℝ] E))
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
    (hV : ∀ r : ℝ,
      HasDerivAt V (V r * (-orthonormalDiagonalOperator b a) + G r) r) :
    ∀ r : ℝ,
      HasDerivAt
        (fun s : ℝ => (U s - V s) -
          orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf)
        (((U r - V r) -
              orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf) *
            (-orthonormalDiagonalOperator b a) +
          ((F r - G r) - Qinf)) r := by
  intro r
  have hpair := (hU r).sub (hV r)
  have hshift := hpair.sub
    (hasDerivAt_const (x := r)
      (c := orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf))
  convert hshift using 1
  have heq := orthonormalDiagonalHamiltonianSteadyResponseRight_equilibrium
    b a δ hδ hδpos Qinf
  noncomm_ring
  rw [heq]
  abel

section Left

variable {ι E : Type*}
variable [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
variable (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ)
variable (t₀ t : ℝ) (ht : t₀ ≤ t)
variable (A B Qinf : E →L[ℝ] E)
variable (F G U V : ℝ → (E →L[ℝ] E))
variable (hF : Continuous F) (hG : Continuous G)
variable (hU0 : U t₀ = A) (hV0 : V t₀ = B)
variable (hU : ∀ r : ℝ,
  HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
variable (hV : ∀ r : ℝ,
  HasDerivAt V ((-orthonormalDiagonalOperator b a) * V r + G r) r)

include hδ hδpos ht hF hG hU0 hV0 hU hV

/-- Complete finite-horizon convolution estimate for the error around the exact
left steady bias `H⁻¹ Qinf`. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_inputProfile_finiteHorizon_bound_left :
    ‖(U t - V t) -
        orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf‖ ≤
      Real.exp (-((t - t₀) * δ)) *
          ‖(A - B) -
            orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * δ)) *
          ‖(F s - G s) - Qinf‖ := by
  have hR : Continuous (fun s : ℝ => (F s - G s) - Qinf) :=
    (hF.sub hG).sub continuous_const
  have hZ0 :
      (fun s : ℝ => (U s - V s) -
        orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf) t₀ =
      (A - B) - orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf := by
    simp [hU0, hV0]
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_massGap_bound_left
      b a δ hδ t₀ t ht
      ((A - B) - orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf)
      (fun s : ℝ => (F s - G s) - Qinf)
      (fun s : ℝ => (U s - V s) -
        orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf)
      hR hZ0
      (orthonormalDiagonal_asymptoticIncrementalSteadyBiasFiniteHorizon_left_deriv
        b a δ hδ hδpos Qinf F G U V hU hV)

/-- The complete left affine finite-horizon estimate acts on every state. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_inputProfile_pointwise_finiteHorizon_bound_left
    (y : E) :
    ‖U t y - V t y -
        orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf y‖ ≤
      (Real.exp (-((t - t₀) * δ)) *
          ‖(A - B) -
            orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * δ)) *
          ‖(F s - G s) - Qinf‖) * ‖y‖ := by
  have henv :=
    orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_inputProfile_finiteHorizon_bound_left
      b a δ hδ hδpos t₀ t ht A B Qinf F G U V hF hG hU0 hV0 hU hV
  have hpoint :
      ‖((U t - V t) -
        orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf) y‖ ≤
      (Real.exp (-((t - t₀) * δ)) *
          ‖(A - B) -
            orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * δ)) *
          ‖(F s - G s) - Qinf‖) * ‖y‖ := by
    calc
      ‖((U t - V t) -
          orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf) y‖ ≤
          ‖(U t - V t) -
            orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf‖ * ‖y‖ :=
        ((U t - V t) -
          orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf).le_opNorm y
      _ ≤ (Real.exp (-((t - t₀) * δ)) *
          ‖(A - B) -
            orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * δ)) *
          ‖(F s - G s) - Qinf‖) * ‖y‖ :=
        mul_le_mul_of_nonneg_right henv (norm_nonneg y)
  simpa using hpoint

/-- Every left matrix-element error around the steady bias inherits the complete
finite-horizon profile. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_inputProfile_matrixElement_error_finiteHorizon_bound_left
    (x y : E) :
    |inner ℝ x (U t y) - inner ℝ x (V t y) -
        inner ℝ x
          (orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf y)| ≤
      (Real.exp (-((t - t₀) * δ)) *
          ‖(A - B) -
            orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * δ)) *
          ‖(F s - G s) - Qinf‖) * ‖x‖ * ‖y‖ := by
  have hpoint :=
    orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_inputProfile_pointwise_finiteHorizon_bound_left
      b a δ hδ hδpos t₀ t ht A B Qinf F G U V hF hG hU0 hV0 hU hV y
  have hcs :
      |inner ℝ x
        (((U t - V t) -
          orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf) y)| ≤
        ‖x‖ *
          ‖((U t - V t) -
            orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf) y‖ := by
    simpa only [Real.norm_eq_abs] using
      (norm_inner_le_norm (𝕜 := ℝ) x
        (((U t - V t) -
          orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf) y))
  have hmatrix :
      |inner ℝ x
        (((U t - V t) -
          orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf) y)| ≤
      (Real.exp (-((t - t₀) * δ)) *
          ‖(A - B) -
            orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * δ)) *
          ‖(F s - G s) - Qinf‖) * ‖x‖ * ‖y‖ := by
    calc
      |inner ℝ x
          (((U t - V t) -
            orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf) y)| ≤
          ‖x‖ *
            ‖((U t - V t) -
              orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf) y‖ := hcs
      _ ≤ ‖x‖ *
          ((Real.exp (-((t - t₀) * δ)) *
              ‖(A - B) -
                orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf‖ +
            ∫ s in t₀..t, Real.exp (-((t - s) * δ)) *
              ‖(F s - G s) - Qinf‖) * ‖y‖) :=
        mul_le_mul_of_nonneg_left hpoint (norm_nonneg x)
      _ = (Real.exp (-((t - t₀) * δ)) *
          ‖(A - B) -
            orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * δ)) *
          ‖(F s - G s) - Qinf‖) * ‖x‖ * ‖y‖ := by ring
  simpa [inner_sub_right] using hmatrix

/-- One profile-sensitive left bound controls all matrix-element errors on both
closed unit balls. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_inputProfile_unitBall_matrixElement_error_finiteHorizon_bound_left :
    ∀ x y : E, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
      |inner ℝ x (U t y) - inner ℝ x (V t y) -
        inner ℝ x
          (orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf y)| ≤
        Real.exp (-((t - t₀) * δ)) *
            ‖(A - B) -
              orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf‖ +
          ∫ s in t₀..t, Real.exp (-((t - s) * δ)) *
            ‖(F s - G s) - Qinf‖ := by
  intro x y hx hy
  have hmatrix :=
    continuousLinearMap_abs_inner_apply_sub_inner_apply_le_norm_of_norm_le_one
      (U t - V t)
      (orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf)
      x y hx hy
  have henv :=
    orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_inputProfile_finiteHorizon_bound_left
      b a δ hδ hδpos t₀ t ht A B Qinf F G U V hF hG hU0 hV0 hU hV
  have hbound := hmatrix.trans henv
  simpa [inner_sub_right] using hbound

/-- If the residual mismatch around `Qinf` is bounded by `C`, the left steady-bias
error has the sharp finite-horizon gain. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_boundedResidual_sharp_finiteHorizon_bound_left
    (C : ℝ) (hC : 0 ≤ C)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖(F s - G s) - Qinf‖ ≤ C) :
    ‖(U t - V t) -
        orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf‖ ≤
      Real.exp (-((t - t₀) * δ)) *
          ‖(A - B) -
            orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf‖ +
        ((1 - Real.exp (-((t - t₀) * δ))) / δ) * C := by
  have hprofile :=
    orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_inputProfile_finiteHorizon_bound_left
      b a δ hδ hδpos t₀ t ht A B Qinf F G U V hF hG hU0 hV0 hU hV
  have hforcing :=
    intervalIntegral_exp_memory_norm_sub_le_finiteHorizonGain
      δ C t₀ t ht hδpos
      (fun s : ℝ => F s - G s) (fun _ : ℝ => Qinf)
      (hF.sub hG) continuous_const
      (by
        intro s hs
        simpa using hFG s hs)
  exact hprofile.trans (add_le_add (le_refl _) hforcing)

/-- Sharp bounded-residual left control on every state. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_boundedResidual_pointwise_sharp_finiteHorizon_bound_left
    (C : ℝ) (hC : 0 ≤ C)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖(F s - G s) - Qinf‖ ≤ C)
    (y : E) :
    ‖U t y - V t y -
        orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf y‖ ≤
      (Real.exp (-((t - t₀) * δ)) *
          ‖(A - B) -
            orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf‖ +
        ((1 - Real.exp (-((t - t₀) * δ))) / δ) * C) * ‖y‖ := by
  have hsharp :=
    orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_boundedResidual_sharp_finiteHorizon_bound_left
      b a δ hδ hδpos t₀ t ht A B Qinf F G U V hF hG hU0 hV0 hU hV
      C hC hFG
  have hpoint :
      ‖((U t - V t) -
        orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf) y‖ ≤
      (Real.exp (-((t - t₀) * δ)) *
          ‖(A - B) -
            orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf‖ +
        ((1 - Real.exp (-((t - t₀) * δ))) / δ) * C) * ‖y‖ := by
    calc
      ‖((U t - V t) -
          orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf) y‖ ≤
          ‖(U t - V t) -
            orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf‖ * ‖y‖ :=
        ((U t - V t) -
          orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf).le_opNorm y
      _ ≤ (Real.exp (-((t - t₀) * δ)) *
          ‖(A - B) -
            orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf‖ +
        ((1 - Real.exp (-((t - t₀) * δ))) / δ) * C) * ‖y‖ :=
        mul_le_mul_of_nonneg_right hsharp (norm_nonneg y)
  simpa using hpoint

/-- Sharp bounded-residual left control for every matrix-element error. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_boundedResidual_matrixElement_error_sharp_finiteHorizon_bound_left
    (C : ℝ) (hC : 0 ≤ C)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖(F s - G s) - Qinf‖ ≤ C)
    (x y : E) :
    |inner ℝ x (U t y) - inner ℝ x (V t y) -
        inner ℝ x
          (orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf y)| ≤
      (Real.exp (-((t - t₀) * δ)) *
          ‖(A - B) -
            orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf‖ +
        ((1 - Real.exp (-((t - t₀) * δ))) / δ) * C) * ‖x‖ * ‖y‖ := by
  have hpoint :=
    orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_boundedResidual_pointwise_sharp_finiteHorizon_bound_left
      b a δ hδ hδpos t₀ t ht A B Qinf F G U V hF hG hU0 hV0 hU hV
      C hC hFG y
  have hcs :
      |inner ℝ x
        (((U t - V t) -
          orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf) y)| ≤
        ‖x‖ *
          ‖((U t - V t) -
            orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf) y‖ := by
    simpa only [Real.norm_eq_abs] using
      (norm_inner_le_norm (𝕜 := ℝ) x
        (((U t - V t) -
          orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf) y))
  have hmatrix :
      |inner ℝ x
        (((U t - V t) -
          orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf) y)| ≤
      (Real.exp (-((t - t₀) * δ)) *
          ‖(A - B) -
            orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf‖ +
        ((1 - Real.exp (-((t - t₀) * δ))) / δ) * C) * ‖x‖ * ‖y‖ := by
    calc
      |inner ℝ x
          (((U t - V t) -
            orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf) y)| ≤
          ‖x‖ *
            ‖((U t - V t) -
              orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf) y‖ := hcs
      _ ≤ ‖x‖ *
          ((Real.exp (-((t - t₀) * δ)) *
              ‖(A - B) -
                orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf‖ +
            ((1 - Real.exp (-((t - t₀) * δ))) / δ) * C) * ‖y‖) :=
        mul_le_mul_of_nonneg_left hpoint (norm_nonneg x)
      _ = (Real.exp (-((t - t₀) * δ)) *
          ‖(A - B) -
            orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf‖ +
        ((1 - Real.exp (-((t - t₀) * δ))) / δ) * C) * ‖x‖ * ‖y‖ := by ring
  simpa [inner_sub_right] using hmatrix

/-- One sharp bounded-residual left bound controls both closed unit balls. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_boundedResidual_unitBall_matrixElement_error_sharp_finiteHorizon_bound_left
    (C : ℝ) (hC : 0 ≤ C)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖(F s - G s) - Qinf‖ ≤ C) :
    ∀ x y : E, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
      |inner ℝ x (U t y) - inner ℝ x (V t y) -
        inner ℝ x
          (orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf y)| ≤
        Real.exp (-((t - t₀) * δ)) *
            ‖(A - B) -
              orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf‖ +
          ((1 - Real.exp (-((t - t₀) * δ))) / δ) * C := by
  intro x y hx hy
  have hmatrix :=
    continuousLinearMap_abs_inner_apply_sub_inner_apply_le_norm_of_norm_le_one
      (U t - V t)
      (orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf)
      x y hx hy
  have hsharp :=
    orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_boundedResidual_sharp_finiteHorizon_bound_left
      b a δ hδ hδpos t₀ t ht A B Qinf F G U V hF hG hU0 hV0 hU hV
      C hC hFG
  have hbound := hmatrix.trans hsharp
  simpa [inner_sub_right] using hbound

end Left

section Right

variable {ι E : Type*}
variable [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
variable (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ)
variable (t₀ t : ℝ) (ht : t₀ ≤ t)
variable (A B Qinf : E →L[ℝ] E)
variable (F G U V : ℝ → (E →L[ℝ] E))
variable (hF : Continuous F) (hG : Continuous G)
variable (hU0 : U t₀ = A) (hV0 : V t₀ = B)
variable (hU : ∀ r : ℝ,
  HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
variable (hV : ∀ r : ℝ,
  HasDerivAt V (V r * (-orthonormalDiagonalOperator b a) + G r) r)

include hδ hδpos ht hF hG hU0 hV0 hU hV

/-- Complete finite-horizon convolution estimate for the error around the exact
right steady bias `Qinf H⁻¹`, without any commutation hypothesis. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_inputProfile_finiteHorizon_bound_right :
    ‖(U t - V t) -
        orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf‖ ≤
      Real.exp (-((t - t₀) * δ)) *
          ‖(A - B) -
            orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * δ)) *
          ‖(F s - G s) - Qinf‖ := by
  have hR : Continuous (fun s : ℝ => (F s - G s) - Qinf) :=
    (hF.sub hG).sub continuous_const
  have hZ0 :
      (fun s : ℝ => (U s - V s) -
        orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf) t₀ =
      (A - B) - orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf := by
    simp [hU0, hV0]
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_massGap_bound_right
      b a δ hδ t₀ t ht
      ((A - B) - orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf)
      (fun s : ℝ => (F s - G s) - Qinf)
      (fun s : ℝ => (U s - V s) -
        orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf)
      hR hZ0
      (orthonormalDiagonal_asymptoticIncrementalSteadyBiasFiniteHorizon_right_deriv
        b a δ hδ hδpos Qinf F G U V hU hV)

/-- The complete right affine finite-horizon estimate acts on every state. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_inputProfile_pointwise_finiteHorizon_bound_right
    (y : E) :
    ‖U t y - V t y -
        orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf y‖ ≤
      (Real.exp (-((t - t₀) * δ)) *
          ‖(A - B) -
            orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * δ)) *
          ‖(F s - G s) - Qinf‖) * ‖y‖ := by
  have henv :=
    orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_inputProfile_finiteHorizon_bound_right
      b a δ hδ hδpos t₀ t ht A B Qinf F G U V hF hG hU0 hV0 hU hV
  have hpoint :
      ‖((U t - V t) -
        orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf) y‖ ≤
      (Real.exp (-((t - t₀) * δ)) *
          ‖(A - B) -
            orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * δ)) *
          ‖(F s - G s) - Qinf‖) * ‖y‖ := by
    calc
      ‖((U t - V t) -
          orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf) y‖ ≤
          ‖(U t - V t) -
            orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf‖ * ‖y‖ :=
        ((U t - V t) -
          orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf).le_opNorm y
      _ ≤ (Real.exp (-((t - t₀) * δ)) *
          ‖(A - B) -
            orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * δ)) *
          ‖(F s - G s) - Qinf‖) * ‖y‖ :=
        mul_le_mul_of_nonneg_right henv (norm_nonneg y)
  simpa using hpoint

/-- Every right matrix-element error inherits the complete finite-horizon
profile, without commutation. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_inputProfile_matrixElement_error_finiteHorizon_bound_right
    (x y : E) :
    |inner ℝ x (U t y) - inner ℝ x (V t y) -
        inner ℝ x
          (orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf y)| ≤
      (Real.exp (-((t - t₀) * δ)) *
          ‖(A - B) -
            orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * δ)) *
          ‖(F s - G s) - Qinf‖) * ‖x‖ * ‖y‖ := by
  have hpoint :=
    orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_inputProfile_pointwise_finiteHorizon_bound_right
      b a δ hδ hδpos t₀ t ht A B Qinf F G U V hF hG hU0 hV0 hU hV y
  have hcs :
      |inner ℝ x
        (((U t - V t) -
          orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf) y)| ≤
        ‖x‖ *
          ‖((U t - V t) -
            orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf) y‖ := by
    simpa only [Real.norm_eq_abs] using
      (norm_inner_le_norm (𝕜 := ℝ) x
        (((U t - V t) -
          orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf) y))
  have hmatrix :
      |inner ℝ x
        (((U t - V t) -
          orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf) y)| ≤
      (Real.exp (-((t - t₀) * δ)) *
          ‖(A - B) -
            orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * δ)) *
          ‖(F s - G s) - Qinf‖) * ‖x‖ * ‖y‖ := by
    calc
      |inner ℝ x
          (((U t - V t) -
            orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf) y)| ≤
          ‖x‖ *
            ‖((U t - V t) -
              orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf) y‖ := hcs
      _ ≤ ‖x‖ *
          ((Real.exp (-((t - t₀) * δ)) *
              ‖(A - B) -
                orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf‖ +
            ∫ s in t₀..t, Real.exp (-((t - s) * δ)) *
              ‖(F s - G s) - Qinf‖) * ‖y‖) :=
        mul_le_mul_of_nonneg_left hpoint (norm_nonneg x)
      _ = (Real.exp (-((t - t₀) * δ)) *
          ‖(A - B) -
            orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * δ)) *
          ‖(F s - G s) - Qinf‖) * ‖x‖ * ‖y‖ := by ring
  simpa [inner_sub_right] using hmatrix

/-- One profile-sensitive right bound controls all matrix-element errors on both
closed unit balls. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_inputProfile_unitBall_matrixElement_error_finiteHorizon_bound_right :
    ∀ x y : E, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
      |inner ℝ x (U t y) - inner ℝ x (V t y) -
        inner ℝ x
          (orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf y)| ≤
        Real.exp (-((t - t₀) * δ)) *
            ‖(A - B) -
              orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf‖ +
          ∫ s in t₀..t, Real.exp (-((t - s) * δ)) *
            ‖(F s - G s) - Qinf‖ := by
  intro x y hx hy
  have hmatrix :=
    continuousLinearMap_abs_inner_apply_sub_inner_apply_le_norm_of_norm_le_one
      (U t - V t)
      (orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf)
      x y hx hy
  have henv :=
    orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_inputProfile_finiteHorizon_bound_right
      b a δ hδ hδpos t₀ t ht A B Qinf F G U V hF hG hU0 hV0 hU hV
  have hbound := hmatrix.trans henv
  simpa [inner_sub_right] using hbound

/-- If the residual mismatch around `Qinf` is bounded by `C`, the right steady-bias
error has the same sharp finite-horizon gain without commutation. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_boundedResidual_sharp_finiteHorizon_bound_right
    (C : ℝ) (hC : 0 ≤ C)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖(F s - G s) - Qinf‖ ≤ C) :
    ‖(U t - V t) -
        orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf‖ ≤
      Real.exp (-((t - t₀) * δ)) *
          ‖(A - B) -
            orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf‖ +
        ((1 - Real.exp (-((t - t₀) * δ))) / δ) * C := by
  have hprofile :=
    orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_inputProfile_finiteHorizon_bound_right
      b a δ hδ hδpos t₀ t ht A B Qinf F G U V hF hG hU0 hV0 hU hV
  have hforcing :=
    intervalIntegral_exp_memory_norm_sub_le_finiteHorizonGain
      δ C t₀ t ht hδpos
      (fun s : ℝ => F s - G s) (fun _ : ℝ => Qinf)
      (hF.sub hG) continuous_const
      (by
        intro s hs
        simpa using hFG s hs)
  exact hprofile.trans (add_le_add (le_refl _) hforcing)

/-- Sharp bounded-residual right control on every state, without commutation. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_boundedResidual_pointwise_sharp_finiteHorizon_bound_right
    (C : ℝ) (hC : 0 ≤ C)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖(F s - G s) - Qinf‖ ≤ C)
    (y : E) :
    ‖U t y - V t y -
        orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf y‖ ≤
      (Real.exp (-((t - t₀) * δ)) *
          ‖(A - B) -
            orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf‖ +
        ((1 - Real.exp (-((t - t₀) * δ))) / δ) * C) * ‖y‖ := by
  have hsharp :=
    orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_boundedResidual_sharp_finiteHorizon_bound_right
      b a δ hδ hδpos t₀ t ht A B Qinf F G U V hF hG hU0 hV0 hU hV
      C hC hFG
  have hpoint :
      ‖((U t - V t) -
        orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf) y‖ ≤
      (Real.exp (-((t - t₀) * δ)) *
          ‖(A - B) -
            orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf‖ +
        ((1 - Real.exp (-((t - t₀) * δ))) / δ) * C) * ‖y‖ := by
    calc
      ‖((U t - V t) -
          orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf) y‖ ≤
          ‖(U t - V t) -
            orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf‖ * ‖y‖ :=
        ((U t - V t) -
          orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf).le_opNorm y
      _ ≤ (Real.exp (-((t - t₀) * δ)) *
          ‖(A - B) -
            orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf‖ +
        ((1 - Real.exp (-((t - t₀) * δ))) / δ) * C) * ‖y‖ :=
        mul_le_mul_of_nonneg_right hsharp (norm_nonneg y)
  simpa using hpoint

/-- Sharp bounded-residual right control for every matrix-element error. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_boundedResidual_matrixElement_error_sharp_finiteHorizon_bound_right
    (C : ℝ) (hC : 0 ≤ C)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖(F s - G s) - Qinf‖ ≤ C)
    (x y : E) :
    |inner ℝ x (U t y) - inner ℝ x (V t y) -
        inner ℝ x
          (orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf y)| ≤
      (Real.exp (-((t - t₀) * δ)) *
          ‖(A - B) -
            orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf‖ +
        ((1 - Real.exp (-((t - t₀) * δ))) / δ) * C) * ‖x‖ * ‖y‖ := by
  have hpoint :=
    orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_boundedResidual_pointwise_sharp_finiteHorizon_bound_right
      b a δ hδ hδpos t₀ t ht A B Qinf F G U V hF hG hU0 hV0 hU hV
      C hC hFG y
  have hcs :
      |inner ℝ x
        (((U t - V t) -
          orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf) y)| ≤
        ‖x‖ *
          ‖((U t - V t) -
            orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf) y‖ := by
    simpa only [Real.norm_eq_abs] using
      (norm_inner_le_norm (𝕜 := ℝ) x
        (((U t - V t) -
          orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf) y))
  have hmatrix :
      |inner ℝ x
        (((U t - V t) -
          orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf) y)| ≤
      (Real.exp (-((t - t₀) * δ)) *
          ‖(A - B) -
            orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf‖ +
        ((1 - Real.exp (-((t - t₀) * δ))) / δ) * C) * ‖x‖ * ‖y‖ := by
    calc
      |inner ℝ x
          (((U t - V t) -
            orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf) y)| ≤
          ‖x‖ *
            ‖((U t - V t) -
              orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf) y‖ := hcs
      _ ≤ ‖x‖ *
          ((Real.exp (-((t - t₀) * δ)) *
              ‖(A - B) -
                orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf‖ +
            ((1 - Real.exp (-((t - t₀) * δ))) / δ) * C) * ‖y‖) :=
        mul_le_mul_of_nonneg_left hpoint (norm_nonneg x)
      _ = (Real.exp (-((t - t₀) * δ)) *
          ‖(A - B) -
            orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf‖ +
        ((1 - Real.exp (-((t - t₀) * δ))) / δ) * C) * ‖x‖ * ‖y‖ := by ring
  simpa [inner_sub_right] using hmatrix

/-- One sharp bounded-residual right bound controls both closed unit balls. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_boundedResidual_unitBall_matrixElement_error_sharp_finiteHorizon_bound_right
    (C : ℝ) (hC : 0 ≤ C)
    (hFG : ∀ s : ℝ, t₀ ≤ s → ‖(F s - G s) - Qinf‖ ≤ C) :
    ∀ x y : E, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
      |inner ℝ x (U t y) - inner ℝ x (V t y) -
        inner ℝ x
          (orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf y)| ≤
        Real.exp (-((t - t₀) * δ)) *
            ‖(A - B) -
              orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf‖ +
          ((1 - Real.exp (-((t - t₀) * δ))) / δ) * C := by
  intro x y hx hy
  have hmatrix :=
    continuousLinearMap_abs_inner_apply_sub_inner_apply_le_norm_of_norm_le_one
      (U t - V t)
      (orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf)
      x y hx hy
  have hsharp :=
    orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_boundedResidual_sharp_finiteHorizon_bound_right
      b a δ hδ hδpos t₀ t ht A B Qinf F G U V hF hG hU0 hV0 hU hV
      C hC hFG
  have hbound := hmatrix.trans hsharp
  simpa [inner_sub_right] using hbound

end Right

end

end MathlibAnalytic
end MGAP4D
