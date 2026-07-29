import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamelVanishingInputAsymptoticStability
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter

/-- The inverse of a finite real orthonormal diagonal operator, obtained by
inverting every diagonal coefficient. -/
noncomputable def orthonormalDiagonalInverseOperator
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ) : E →L[ℝ] E :=
  orthonormalDiagonalOperator b (fun i => (a i)⁻¹)

@[simp]
theorem orthonormalDiagonalInverseOperator_apply_basis
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (i : ι) :
    orthonormalDiagonalInverseOperator b a (b i) = (a i)⁻¹ • b i := by
  simp [orthonormalDiagonalInverseOperator]

/-- A strictly positive lower diagonal bound makes the explicit reciprocal
operator a right inverse. -/
theorem orthonormalDiagonalOperator_mul_inverseOperator
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i)
    (hδpos : 0 < δ) :
    orthonormalDiagonalOperator b a *
        orthonormalDiagonalInverseOperator b a = 1 := by
  have ha : ∀ i : ι, a i ≠ 0 := fun i =>
    ne_of_gt (lt_of_lt_of_le hδpos (hδ i))
  apply ContinuousLinearMap.ext
  intro x
  rw [← b.sum_repr' x]
  simp [orthonormalDiagonalInverseOperator, ha]

/-- The same reciprocal diagonal operator is also a left inverse. -/
theorem orthonormalDiagonalInverseOperator_mul_operator
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i)
    (hδpos : 0 < δ) :
    orthonormalDiagonalInverseOperator b a *
        orthonormalDiagonalOperator b a = 1 := by
  have ha : ∀ i : ι, a i ≠ 0 := fun i =>
    ne_of_gt (lt_of_lt_of_le hδpos (hδ i))
  apply ContinuousLinearMap.ext
  intro x
  rw [← b.sum_repr' x]
  simp [orthonormalDiagonalInverseOperator, ha]

/-- The stationary response for left Hamiltonian multiplication. -/
noncomputable def orthonormalDiagonalHamiltonian_leftSteadyState
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (F∞ : E →L[ℝ] E) : E →L[ℝ] E :=
  orthonormalDiagonalInverseOperator b a * F∞

/-- The stationary response for right Hamiltonian multiplication. -/
noncomputable def orthonormalDiagonalHamiltonian_rightSteadyState
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (F∞ : E →L[ℝ] E) : E →L[ℝ] E :=
  F∞ * orthonormalDiagonalInverseOperator b a

/-- The explicit left steady state solves `H * S = F∞`. -/
theorem orthonormalDiagonalHamiltonian_leftSteadyState_stationary
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i)
    (hδpos : 0 < δ)
    (F∞ : E →L[ℝ] E) :
    orthonormalDiagonalOperator b a *
        orthonormalDiagonalHamiltonian_leftSteadyState b a F∞ = F∞ := by
  rw [orthonormalDiagonalHamiltonian_leftSteadyState, ← mul_assoc,
    orthonormalDiagonalOperator_mul_inverseOperator b a δ hδ hδpos,
    one_mul]

/-- The explicit right steady state solves `S * H = F∞`. -/
theorem orthonormalDiagonalHamiltonian_rightSteadyState_stationary
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i)
    (hδpos : 0 < δ)
    (F∞ : E →L[ℝ] E) :
    orthonormalDiagonalHamiltonian_rightSteadyState b a F∞ *
        orthonormalDiagonalOperator b a = F∞ := by
  rw [orthonormalDiagonalHamiltonian_rightSteadyState, mul_assoc,
    orthonormalDiagonalInverseOperator_mul_operator b a δ hδ hδpos,
    mul_one]

/-- The left stationary response is unique. -/
theorem orthonormalDiagonalHamiltonian_leftSteadyState_unique
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i)
    (hδpos : 0 < δ)
    (F∞ S : E →L[ℝ] E)
    (hS : orthonormalDiagonalOperator b a * S = F∞) :
    S = orthonormalDiagonalHamiltonian_leftSteadyState b a F∞ := by
  rw [orthonormalDiagonalHamiltonian_leftSteadyState]
  calc
    S = orthonormalDiagonalInverseOperator b a *
        (orthonormalDiagonalOperator b a * S) := by
      rw [← mul_assoc,
        orthonormalDiagonalInverseOperator_mul_operator b a δ hδ hδpos,
        one_mul]
    _ = orthonormalDiagonalInverseOperator b a * F∞ := by rw [hS]

/-- The right stationary response is unique. -/
theorem orthonormalDiagonalHamiltonian_rightSteadyState_unique
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i)
    (hδpos : 0 < δ)
    (F∞ S : E →L[ℝ] E)
    (hS : S * orthonormalDiagonalOperator b a = F∞) :
    S = orthonormalDiagonalHamiltonian_rightSteadyState b a F∞ := by
  rw [orthonormalDiagonalHamiltonian_rightSteadyState]
  calc
    S = (S * orthonormalDiagonalOperator b a) *
        orthonormalDiagonalInverseOperator b a := by
      rw [mul_assoc,
        orthonormalDiagonalOperator_mul_inverseOperator b a δ hδ hδpos,
        mul_one]
    _ = F∞ * orthonormalDiagonalInverseOperator b a := by rw [hS]

/-- Left evolution tracks the unique steady response when the forcing converges
in operator space to a constant limit. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tendsto_norm_sub_left
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i)
    (hδpos : 0 < δ)
    (F U : ℝ → (E →L[ℝ] E))
    (F∞ : E →L[ℝ] E)
    (hF : Continuous F)
    (hF∞ : Tendsto F atTop (nhds F∞))
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r) :
    Tendsto
      (fun t : ℝ =>
        ‖U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F∞‖)
      atTop (nhds 0) := by
  let S := orthonormalDiagonalHamiltonian_leftSteadyState b a F∞
  let G : ℝ → (E →L[ℝ] E) := fun t => F t - F∞
  let V : ℝ → (E →L[ℝ] E) := fun t => U t - S
  have hS : orthonormalDiagonalOperator b a * S = F∞ := by
    dsimp [S]
    exact orthonormalDiagonalHamiltonian_leftSteadyState_stationary
      b a δ hδ hδpos F∞
  have hG : Continuous G := by
    dsimp [G]
    exact hF.sub continuous_const
  have hGop : Tendsto G atTop (nhds 0) := by
    dsimp [G]
    simpa using hF∞.sub tendsto_const_nhds
  have hG0 : Tendsto (fun t : ℝ => ‖G t‖) atTop (nhds 0) := by
    simpa using hGop.norm
  have hV : ∀ r : ℝ,
      HasDerivAt V ((-orthonormalDiagonalOperator b a) * V r + G r) r := by
    intro r
    have hconst : HasDerivAt (fun _ : ℝ => S) 0 r :=
      hasDerivAt_const (x := r) (c := S)
    have hsub := (hU r).sub hconst
    have hderiv :
        (-orthonormalDiagonalOperator b a) * U r + F r =
          (-orthonormalDiagonalOperator b a) * (U r - S) +
            (F r - F∞) := by
      rw [← hS]
      noncomm_ring
    simpa [V, G, hderiv] using hsub
  have htrack :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_vanishingInput_tendsto_norm_zero_left
      b a δ hδ hδpos G V hG hG0 hV
  simpa [V, S] using htrack

/-- Right evolution tracks the unique steady response, without a commutation
hypothesis on the forcing limit. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tendsto_norm_sub_right
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i)
    (hδpos : 0 < δ)
    (F U : ℝ → (E →L[ℝ] E))
    (F∞ : E →L[ℝ] E)
    (hF : Continuous F)
    (hF∞ : Tendsto F atTop (nhds F∞))
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r) :
    Tendsto
      (fun t : ℝ =>
        ‖U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F∞‖)
      atTop (nhds 0) := by
  let S := orthonormalDiagonalHamiltonian_rightSteadyState b a F∞
  let G : ℝ → (E →L[ℝ] E) := fun t => F t - F∞
  let V : ℝ → (E →L[ℝ] E) := fun t => U t - S
  have hS : S * orthonormalDiagonalOperator b a = F∞ := by
    dsimp [S]
    exact orthonormalDiagonalHamiltonian_rightSteadyState_stationary
      b a δ hδ hδpos F∞
  have hG : Continuous G := by
    dsimp [G]
    exact hF.sub continuous_const
  have hGop : Tendsto G atTop (nhds 0) := by
    dsimp [G]
    simpa using hF∞.sub tendsto_const_nhds
  have hG0 : Tendsto (fun t : ℝ => ‖G t‖) atTop (nhds 0) := by
    simpa using hGop.norm
  have hV : ∀ r : ℝ,
      HasDerivAt V (V r * (-orthonormalDiagonalOperator b a) + G r) r := by
    intro r
    have hconst : HasDerivAt (fun _ : ℝ => S) 0 r :=
      hasDerivAt_const (x := r) (c := S)
    have hsub := (hU r).sub hconst
    have hderiv :
        U r * (-orthonormalDiagonalOperator b a) + F r =
          (U r - S) * (-orthonormalDiagonalOperator b a) +
            (F r - F∞) := by
      rw [← hS]
      noncomm_ring
    simpa [V, G, hderiv] using hsub
  have htrack :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_vanishingInput_tendsto_norm_zero_right
      b a δ hδ hδpos G V hG hG0 hV
  simpa [V, S] using htrack

/-- Left asymptotically constant-input evolution converges in operator space to
its unique stationary response. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tendsto_leftSteadyState_left
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i)
    (hδpos : 0 < δ)
    (F U : ℝ → (E →L[ℝ] E))
    (F∞ : E →L[ℝ] E)
    (hF : Continuous F)
    (hF∞ : Tendsto F atTop (nhds F∞))
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r) :
    Tendsto U atTop
      (nhds (orthonormalDiagonalHamiltonian_leftSteadyState b a F∞)) := by
  let S := orthonormalDiagonalHamiltonian_leftSteadyState b a F∞
  have hnorm :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tendsto_norm_sub_left
      b a δ hδ hδpos F U F∞ hF hF∞ hU
  have hdiff : Tendsto (fun t : ℝ => U t - S) atTop (nhds 0) := by
    exact tendsto_zero_of_tendsto_norm_zero (by simpa [S] using hnorm)
  have hconst : Tendsto (fun _ : ℝ => S) atTop (nhds S) := tendsto_const_nhds
  simpa [S] using hdiff.add hconst

/-- Right asymptotically constant-input evolution converges in operator space to
its unique stationary response. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tendsto_rightSteadyState_right
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i)
    (hδpos : 0 < δ)
    (F U : ℝ → (E →L[ℝ] E))
    (F∞ : E →L[ℝ] E)
    (hF : Continuous F)
    (hF∞ : Tendsto F atTop (nhds F∞))
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r) :
    Tendsto U atTop
      (nhds (orthonormalDiagonalHamiltonian_rightSteadyState b a F∞)) := by
  let S := orthonormalDiagonalHamiltonian_rightSteadyState b a F∞
  have hnorm :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tendsto_norm_sub_right
      b a δ hδ hδpos F U F∞ hF hF∞ hU
  have hdiff : Tendsto (fun t : ℝ => U t - S) atTop (nhds 0) := by
    exact tendsto_zero_of_tendsto_norm_zero (by simpa [S] using hnorm)
  have hconst : Tendsto (fun _ : ℝ => S) atTop (nhds S) := tendsto_const_nhds
  simpa [S] using hdiff.add hconst

/-- Left tracking holds strongly on every fixed state. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tendsto_apply_left
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i)
    (hδpos : 0 < δ)
    (F U : ℝ → (E →L[ℝ] E))
    (F∞ : E →L[ℝ] E)
    (hF : Continuous F)
    (hF∞ : Tendsto F atTop (nhds F∞))
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
    (x : E) :
    Tendsto (fun t : ℝ => U t x) atTop
      (nhds (orthonormalDiagonalHamiltonian_leftSteadyState b a F∞ x)) := by
  let S := orthonormalDiagonalHamiltonian_leftSteadyState b a F∞
  have hnorm :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tendsto_norm_sub_left
      b a δ hδ hδpos F U F∞ hF hF∞ hU
  have hdiff : Tendsto (fun t : ℝ => U t - S) atTop (nhds 0) :=
    tendsto_zero_of_tendsto_norm_zero (by simpa [S] using hnorm)
  have happ := continuousLinearMap_tendsto_apply_zero_of_tendsto_zero hdiff x
  have hconst : Tendsto (fun _ : ℝ => S x) atTop (nhds (S x)) := tendsto_const_nhds
  simpa [S] using happ.add hconst

/-- Right tracking holds strongly on every fixed state. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tendsto_apply_right
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i)
    (hδpos : 0 < δ)
    (F U : ℝ → (E →L[ℝ] E))
    (F∞ : E →L[ℝ] E)
    (hF : Continuous F)
    (hF∞ : Tendsto F atTop (nhds F∞))
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
    (x : E) :
    Tendsto (fun t : ℝ => U t x) atTop
      (nhds (orthonormalDiagonalHamiltonian_rightSteadyState b a F∞ x)) := by
  let S := orthonormalDiagonalHamiltonian_rightSteadyState b a F∞
  have hnorm :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tendsto_norm_sub_right
      b a δ hδ hδpos F U F∞ hF hF∞ hU
  have hdiff : Tendsto (fun t : ℝ => U t - S) atTop (nhds 0) :=
    tendsto_zero_of_tendsto_norm_zero (by simpa [S] using hnorm)
  have happ := continuousLinearMap_tendsto_apply_zero_of_tendsto_zero hdiff x
  have hconst : Tendsto (fun _ : ℝ => S x) atTop (nhds (S x)) := tendsto_const_nhds
  simpa [S] using happ.add hconst

/-- Left tracking is uniform on the closed unit ball. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_eventually_uniform_unitBall_left
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i)
    (hδpos : 0 < δ)
    (F U : ℝ → (E →L[ℝ] E))
    (F∞ : E →L[ℝ] E)
    (hF : Continuous F)
    (hF∞ : Tendsto F atTop (nhds F∞))
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ in atTop,
      ∀ x : E, ‖x‖ ≤ 1 →
        ‖U t x - orthonormalDiagonalHamiltonian_leftSteadyState b a F∞ x‖ < ε := by
  let S := orthonormalDiagonalHamiltonian_leftSteadyState b a F∞
  have hnorm :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tendsto_norm_sub_left
      b a δ hδ hδpos F U F∞ hF hF∞ hU
  have hdiff : Tendsto (fun t : ℝ => U t - S) atTop (nhds 0) :=
    tendsto_zero_of_tendsto_norm_zero (by simpa [S] using hnorm)
  simpa [S] using
    continuousLinearMap_eventually_uniform_unitBall_zero_of_tendsto_zero hdiff

/-- Right tracking is uniform on the closed unit ball. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_eventually_uniform_unitBall_right
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i)
    (hδpos : 0 < δ)
    (F U : ℝ → (E →L[ℝ] E))
    (F∞ : E →L[ℝ] E)
    (hF : Continuous F)
    (hF∞ : Tendsto F atTop (nhds F∞))
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ in atTop,
      ∀ x : E, ‖x‖ ≤ 1 →
        ‖U t x - orthonormalDiagonalHamiltonian_rightSteadyState b a F∞ x‖ < ε := by
  let S := orthonormalDiagonalHamiltonian_rightSteadyState b a F∞
  have hnorm :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tendsto_norm_sub_right
      b a δ hδ hδpos F U F∞ hF hF∞ hU
  have hdiff : Tendsto (fun t : ℝ => U t - S) atTop (nhds 0) :=
    tendsto_zero_of_tendsto_norm_zero (by simpa [S] using hnorm)
  simpa [S] using
    continuousLinearMap_eventually_uniform_unitBall_zero_of_tendsto_zero hdiff

end

end MathlibAnalytic
end MGAP4D
