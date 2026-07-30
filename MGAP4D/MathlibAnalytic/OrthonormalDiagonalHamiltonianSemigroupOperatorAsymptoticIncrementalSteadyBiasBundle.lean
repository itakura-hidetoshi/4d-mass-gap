import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorVanishingInputDifferencePairwiseAsymptoticIncrementalStabilityBundle
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter

/-- The inverse of a finite orthonormal-diagonal Hamiltonian, represented in the
same eigenbasis by reciprocal eigenvalues. The gap hypotheses below guarantee
that every reciprocal is taken at a nonzero eigenvalue. -/
noncomputable def orthonormalDiagonalHamiltonianInverse
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) : E →L[ℝ] E :=
  orthonormalDiagonalOperator b (fun i => (a i)⁻¹)

@[simp]
theorem orthonormalDiagonalHamiltonianInverse_apply_basis
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (i : ι) :
    orthonormalDiagonalHamiltonianInverse b a (b i) = (a i)⁻¹ • b i := by
  exact orthonormalDiagonalOperator_apply_basis b (fun j => (a j)⁻¹) i

private theorem orthonormalDiagonalHamiltonian_eigenvalue_ne_zero
    {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (δ : ℝ) (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) :
    ∀ i : ι, a i ≠ 0 := by
  intro i
  exact ne_of_gt (lt_of_lt_of_le hδpos (hδ i))

/-- The reciprocal diagonal operator is a left inverse of the Hamiltonian. -/
theorem orthonormalDiagonalHamiltonianInverse_mul_operator
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) :
    orthonormalDiagonalHamiltonianInverse b a *
        orthonormalDiagonalOperator b a = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  change orthonormalDiagonalHamiltonianInverse b a
      (orthonormalDiagonalOperator b a x) = x
  rw [← b.sum_repr' x]
  simp [orthonormalDiagonalHamiltonianInverse,
    orthonormalDiagonalHamiltonian_eigenvalue_ne_zero a δ hδ hδpos]

/-- The reciprocal diagonal operator is also a right inverse of the Hamiltonian. -/
theorem orthonormalDiagonalHamiltonianOperator_mul_inverse
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ) :
    orthonormalDiagonalOperator b a *
        orthonormalDiagonalHamiltonianInverse b a = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  change orthonormalDiagonalOperator b a
      (orthonormalDiagonalHamiltonianInverse b a x) = x
  rw [← b.sum_repr' x]
  simp [orthonormalDiagonalHamiltonianInverse,
    orthonormalDiagonalHamiltonian_eigenvalue_ne_zero a δ hδ hδpos]

/-- The steady response for left Hamiltonian action, `H⁻¹ Qinf`. -/
noncomputable def orthonormalDiagonalHamiltonianSteadyResponseLeft
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ)
    (Qinf : E →L[ℝ] E) : E →L[ℝ] E :=
  orthonormalDiagonalHamiltonianInverse b a * Qinf

/-- The steady response for right Hamiltonian action, `Qinf H⁻¹`. -/
noncomputable def orthonormalDiagonalHamiltonianSteadyResponseRight
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ)
    (Qinf : E →L[ℝ] E) : E →L[ℝ] E :=
  Qinf * orthonormalDiagonalHamiltonianInverse b a

/-- The left steady response solves `H W = Qinf`. -/
theorem orthonormalDiagonalHamiltonianSteadyResponseLeft_equilibrium
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ)
    (Qinf : E →L[ℝ] E) :
    orthonormalDiagonalOperator b a *
        orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf = Qinf := by
  rw [orthonormalDiagonalHamiltonianSteadyResponseLeft, ← mul_assoc,
    orthonormalDiagonalHamiltonianOperator_mul_inverse b a δ hδ hδpos,
    one_mul]

/-- The right steady response solves `W H = Qinf`, with no commutation assumption. -/
theorem orthonormalDiagonalHamiltonianSteadyResponseRight_equilibrium
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ)
    (Qinf : E →L[ℝ] E) :
    orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf *
        orthonormalDiagonalOperator b a = Qinf := by
  rw [orthonormalDiagonalHamiltonianSteadyResponseRight, mul_assoc,
    orthonormalDiagonalHamiltonianInverse_mul_operator b a δ hδ hδpos,
    mul_one]

private theorem orthonormalDiagonal_asymptoticIncrementalSteadyBias_left_deriv
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
  rw [← orthonormalDiagonalHamiltonianSteadyResponseLeft_equilibrium
    b a δ hδ hδpos Qinf]
  noncomm_ring

private theorem orthonormalDiagonal_asymptoticIncrementalSteadyBias_right_deriv
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
  rw [← orthonormalDiagonalHamiltonianSteadyResponseRight_equilibrium
    b a δ hδ hδpos Qinf]
  noncomm_ring

private theorem tendsto_real_inner_const_of_tendsto
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x : E) {f : ℝ → E} {y : E}
    (hf : Tendsto f atTop (nhds y)) :
    Tendsto (fun t : ℝ => inner ℝ x (f t)) atTop (nhds (inner ℝ x y)) := by
  have hx : Tendsto (fun _ : ℝ => x) atTop (nhds x) := tendsto_const_nhds
  exact hx.inner hf

private theorem eventually_uniform_unitBall_matrixElement_to_of_tendsto_norm_sub_zero
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : ℝ → (E →L[ℝ] E)) (S : E →L[ℝ] E)
    (hA : Tendsto (fun t : ℝ => ‖A t - S‖) atTop (nhds 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ in atTop,
      ∀ x y : E, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
        |inner ℝ x (A t y) - inner ℝ x (S y)| < ε := by
  intro ε hε
  have hsmall : ∀ᶠ t : ℝ in atTop, ‖A t - S‖ < ε :=
    hA.eventually_lt_const hε
  filter_upwards [hsmall] with t ht
  intro x y hx hy
  exact lt_of_le_of_lt
    (continuousLinearMap_abs_inner_apply_sub_inner_apply_le_norm_of_norm_le_one
      (A t) S x y hx hy) ht

section Left

variable {ι E : Type*}
variable [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
variable (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ)
variable (Qinf : E →L[ℝ] E)
variable (F G U V : ℝ → (E →L[ℝ] E))
variable (hF : Continuous F) (hG : Continuous G)
variable (hFGinf : Tendsto (fun t : ℝ => ‖(F t - G t) - Qinf‖) atTop (nhds 0))
variable (hU : ∀ r : ℝ,
  HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
variable (hV : ∀ r : ℝ,
  HasDerivAt V ((-orthonormalDiagonalOperator b a) * V r + G r) r)

include hδ hδpos F G hF hG hFGinf hU hV

/-- If the left input mismatch converges to `Qinf`, the trajectory mismatch
converges in norm to the exact steady bias `H⁻¹ Qinf`. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_norm_sub_steadyResponse_zero_left :
    Tendsto
      (fun t : ℝ => ‖(U t - V t) -
        orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf‖)
      atTop (nhds 0) := by
  have hQ : Continuous (fun t : ℝ => (F t - G t) - Qinf) :=
    (hF.sub hG).sub continuous_const
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_vanishingInput_tendsto_norm_zero_left
      b a δ hδ hδpos
      (fun t : ℝ => (F t - G t) - Qinf)
      (fun t : ℝ => (U t - V t) -
        orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf)
      hQ hFGinf
      (orthonormalDiagonal_asymptoticIncrementalSteadyBias_left_deriv
        b a δ hδ hδpos Qinf F G U V hU hV)

/-- Left trajectory mismatch converges in continuous-linear-map space to
`H⁻¹ Qinf`. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_steadyResponse_left :
    Tendsto (fun t : ℝ => U t - V t) atTop
      (nhds (orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf)) := by
  have hzero :
      Tendsto
        (fun t : ℝ => (U t - V t) -
          orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf)
        atTop (nhds 0) :=
    tendsto_zero_of_tendsto_norm_zero
      (orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_norm_sub_steadyResponse_zero_left
        b a δ hδ hδpos Qinf F G U V hF hG hFGinf hU hV)
  have hconst :
      Tendsto
        (fun _ : ℝ => orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf)
        atTop (nhds (orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf)) :=
    tendsto_const_nhds
  simpa using hzero.add hconst

/-- Left mismatch converges strongly on every fixed state to the steady bias. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_apply_steadyResponse_left
    (y : E) :
    Tendsto (fun t : ℝ => (U t - V t) y) atTop
      (nhds (orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf y)) := by
  have hzero :
      Tendsto
        (fun t : ℝ => ((U t - V t) -
          orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf) y)
        atTop (nhds 0) :=
    continuousLinearMap_tendsto_apply_zero_of_tendsto_zero
      (tendsto_zero_of_tendsto_norm_zero
        (orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_norm_sub_steadyResponse_zero_left
          b a δ hδ hδpos Qinf F G U V hF hG hFGinf hU hV)) y
  have hconst :
      Tendsto
        (fun _ : ℝ => orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf y)
        atTop (nhds (orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf y)) :=
    tendsto_const_nhds
  simpa using hzero.add hconst

/-- Direct left action differences converge to the steady response. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_apply_difference_steadyResponse_left
    (y : E) :
    Tendsto (fun t : ℝ => U t y - V t y) atTop
      (nhds (orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf y)) := by
  simpa using
    (orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_apply_steadyResponse_left
      b a δ hδ hδpos Qinf F G U V hF hG hFGinf hU hV y)

/-- Every fixed left matrix-element difference converges to its steady value. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_matrixElement_difference_steadyResponse_left
    (x y : E) :
    Tendsto (fun t : ℝ => inner ℝ x (U t y) - inner ℝ x (V t y))
      atTop
      (nhds (inner ℝ x
        (orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf y))) := by
  have happ :=
    orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_apply_difference_steadyResponse_left
      b a δ hδ hδpos Qinf F G U V hF hG hFGinf hU hV y
  have hinner := tendsto_real_inner_const_of_tendsto x happ
  simpa [inner_sub_right] using hinner

/-- Absolute left matrix-element differences converge to the absolute steady value. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_abs_matrixElement_difference_steadyResponse_left
    (x y : E) :
    Tendsto
      (fun t : ℝ => |inner ℝ x (U t y) - inner ℝ x (V t y)|)
      atTop
      (nhds |inner ℝ x
        (orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf y)|) := by
  have hscalar :=
    orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_matrixElement_difference_steadyResponse_left
      b a δ hδ hδpos Qinf F G U V hF hG hFGinf hU hV x y
  simpa [Real.norm_eq_abs] using hscalar.norm

/-- One eventual time controls the left steady-bias error on both closed unit balls. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_eventually_uniform_unitBall_matrixElement_error_left :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ in atTop,
      ∀ x y : E, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
        |inner ℝ x (U t y) - inner ℝ x (V t y) -
          inner ℝ x (orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf y)| < ε := by
  simpa [inner_sub_right] using
    (eventually_uniform_unitBall_matrixElement_to_of_tendsto_norm_sub_zero
      (fun t : ℝ => U t - V t)
      (orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf)
      (orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_norm_sub_steadyResponse_zero_left
        b a δ hδ hδpos Qinf F G U V hF hG hFGinf hU hV))

end Left

section Right

variable {ι E : Type*}
variable [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (δ : ℝ)
variable (hδ : ∀ i : ι, δ ≤ a i) (hδpos : 0 < δ)
variable (Qinf : E →L[ℝ] E)
variable (F G U V : ℝ → (E →L[ℝ] E))
variable (hF : Continuous F) (hG : Continuous G)
variable (hFGinf : Tendsto (fun t : ℝ => ‖(F t - G t) - Qinf‖) atTop (nhds 0))
variable (hU : ∀ r : ℝ,
  HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
variable (hV : ∀ r : ℝ,
  HasDerivAt V (V r * (-orthonormalDiagonalOperator b a) + G r) r)

include hδ hδpos F G hF hG hFGinf hU hV

/-- If the right input mismatch converges to `Qinf`, the trajectory mismatch
converges in norm to the noncommutative steady bias `Qinf H⁻¹`. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_norm_sub_steadyResponse_zero_right :
    Tendsto
      (fun t : ℝ => ‖(U t - V t) -
        orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf‖)
      atTop (nhds 0) := by
  have hQ : Continuous (fun t : ℝ => (F t - G t) - Qinf) :=
    (hF.sub hG).sub continuous_const
  exact
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_vanishingInput_tendsto_norm_zero_right
      b a δ hδ hδpos
      (fun t : ℝ => (F t - G t) - Qinf)
      (fun t : ℝ => (U t - V t) -
        orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf)
      hQ hFGinf
      (orthonormalDiagonal_asymptoticIncrementalSteadyBias_right_deriv
        b a δ hδ hδpos Qinf F G U V hU hV)

/-- Right trajectory mismatch converges in operator space to `Qinf H⁻¹`. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_steadyResponse_right :
    Tendsto (fun t : ℝ => U t - V t) atTop
      (nhds (orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf)) := by
  have hzero :
      Tendsto
        (fun t : ℝ => (U t - V t) -
          orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf)
        atTop (nhds 0) :=
    tendsto_zero_of_tendsto_norm_zero
      (orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_norm_sub_steadyResponse_zero_right
        b a δ hδ hδpos Qinf F G U V hF hG hFGinf hU hV)
  have hconst :
      Tendsto
        (fun _ : ℝ => orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf)
        atTop (nhds (orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf)) :=
    tendsto_const_nhds
  simpa using hzero.add hconst

/-- Right mismatch converges strongly on every fixed state. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_apply_steadyResponse_right
    (y : E) :
    Tendsto (fun t : ℝ => (U t - V t) y) atTop
      (nhds (orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf y)) := by
  have hzero :
      Tendsto
        (fun t : ℝ => ((U t - V t) -
          orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf) y)
        atTop (nhds 0) :=
    continuousLinearMap_tendsto_apply_zero_of_tendsto_zero
      (tendsto_zero_of_tendsto_norm_zero
        (orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_norm_sub_steadyResponse_zero_right
          b a δ hδ hδpos Qinf F G U V hF hG hFGinf hU hV)) y
  have hconst :
      Tendsto
        (fun _ : ℝ => orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf y)
        atTop (nhds (orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf y)) :=
    tendsto_const_nhds
  simpa using hzero.add hconst

/-- Direct right action differences converge to the right steady response. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_apply_difference_steadyResponse_right
    (y : E) :
    Tendsto (fun t : ℝ => U t y - V t y) atTop
      (nhds (orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf y)) := by
  simpa using
    (orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_apply_steadyResponse_right
      b a δ hδ hδpos Qinf F G U V hF hG hFGinf hU hV y)

/-- Every fixed right matrix-element difference converges to its steady value. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_matrixElement_difference_steadyResponse_right
    (x y : E) :
    Tendsto (fun t : ℝ => inner ℝ x (U t y) - inner ℝ x (V t y))
      atTop
      (nhds (inner ℝ x
        (orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf y))) := by
  have happ :=
    orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_apply_difference_steadyResponse_right
      b a δ hδ hδpos Qinf F G U V hF hG hFGinf hU hV y
  have hinner := tendsto_real_inner_const_of_tendsto x happ
  simpa [inner_sub_right] using hinner

/-- Absolute right matrix-element differences converge to the absolute steady value. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_abs_matrixElement_difference_steadyResponse_right
    (x y : E) :
    Tendsto
      (fun t : ℝ => |inner ℝ x (U t y) - inner ℝ x (V t y)|)
      atTop
      (nhds |inner ℝ x
        (orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf y)|) := by
  have hscalar :=
    orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_matrixElement_difference_steadyResponse_right
      b a δ hδ hδpos Qinf F G U V hF hG hFGinf hU hV x y
  simpa [Real.norm_eq_abs] using hscalar.norm

/-- One eventual time controls the right steady-bias error on both closed unit balls. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_eventually_uniform_unitBall_matrixElement_error_right :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ in atTop,
      ∀ x y : E, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
        |inner ℝ x (U t y) - inner ℝ x (V t y) -
          inner ℝ x (orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf y)| < ε := by
  simpa [inner_sub_right] using
    (eventually_uniform_unitBall_matrixElement_to_of_tendsto_norm_sub_zero
      (fun t : ℝ => U t - V t)
      (orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf)
      (orthonormalDiagonalHamiltonianSemigroup_operator_asymptoticIncrementalSteadyBias_tendsto_norm_sub_steadyResponse_zero_right
        b a δ hδ hδpos Qinf F G U V hF hG hFGinf hU hV))

end Right

end

end MathlibAnalytic
end MGAP4D
