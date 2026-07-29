import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamelVanishingInputAsymptoticStability
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open Filter

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

noncomputable def orthonormalDiagonalHamiltonian_leftSteadyState
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (F_lim : E →L[ℝ] E) : E →L[ℝ] E :=
  orthonormalDiagonalInverseOperator b a * F_lim

noncomputable def orthonormalDiagonalHamiltonian_rightSteadyState
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (F_lim : E →L[ℝ] E) : E →L[ℝ] E :=
  F_lim * orthonormalDiagonalInverseOperator b a

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
    (F_lim : E →L[ℝ] E) :
    orthonormalDiagonalOperator b a *
        orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim = F_lim := by
  rw [orthonormalDiagonalHamiltonian_leftSteadyState, ← mul_assoc,
    orthonormalDiagonalOperator_mul_inverseOperator b a δ hδ hδpos,
    one_mul]

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
    (F_lim : E →L[ℝ] E) :
    orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim *
        orthonormalDiagonalOperator b a = F_lim := by
  rw [orthonormalDiagonalHamiltonian_rightSteadyState, mul_assoc,
    orthonormalDiagonalInverseOperator_mul_operator b a δ hδ hδpos,
    mul_one]

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
    (F_lim S : E →L[ℝ] E)
    (hS : orthonormalDiagonalOperator b a * S = F_lim) :
    S = orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim := by
  rw [orthonormalDiagonalHamiltonian_leftSteadyState]
  calc
    S = orthonormalDiagonalInverseOperator b a *
        (orthonormalDiagonalOperator b a * S) := by
      rw [← mul_assoc,
        orthonormalDiagonalInverseOperator_mul_operator b a δ hδ hδpos,
        one_mul]
    _ = orthonormalDiagonalInverseOperator b a * F_lim := by rw [hS]

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
    (F_lim S : E →L[ℝ] E)
    (hS : S * orthonormalDiagonalOperator b a = F_lim) :
    S = orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim := by
  rw [orthonormalDiagonalHamiltonian_rightSteadyState]
  calc
    S = (S * orthonormalDiagonalOperator b a) *
        orthonormalDiagonalInverseOperator b a := by
      rw [mul_assoc,
        orthonormalDiagonalOperator_mul_inverseOperator b a δ hδ hδpos,
        mul_one]
    _ = F_lim * orthonormalDiagonalInverseOperator b a := by rw [hS]

theorem tendsto_of_tendsto_norm_sub_zero
    {α X : Type*}
    [SeminormedAddCommGroup X]
    {l : Filter α}
    {f : α → X}
    {y : X}
    (h : Tendsto (fun a => ‖f a - y‖) l (nhds 0)) :
    Tendsto f l (nhds y) := by
  have hdiff : Tendsto (fun a => f a - y) l (nhds 0) :=
    tendsto_zero_of_tendsto_norm_zero h
  have hconst : Tendsto (fun _ : α => y) l (nhds y) := tendsto_const_nhds
  simpa using hdiff.add hconst

theorem continuousLinearMap_tendsto_apply_of_tendsto_norm_sub_zero
    {α E F : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [NormedAddCommGroup F]
    [NormedSpace ℝ F]
    {l : Filter α}
    {U : α → (E →L[ℝ] F)}
    {S : E →L[ℝ] F}
    (h : Tendsto (fun a => ‖U a - S‖) l (nhds 0))
    (x : E) :
    Tendsto (fun a => U a x) l (nhds (S x)) := by
  have hdiff : Tendsto (fun a => U a - S) l (nhds 0) :=
    tendsto_zero_of_tendsto_norm_zero h
  have happ := continuousLinearMap_tendsto_apply_zero_of_tendsto_zero hdiff x
  have hconst : Tendsto (fun _ : α => S x) l (nhds (S x)) := tendsto_const_nhds
  simpa using happ.add hconst

theorem continuousLinearMap_eventually_uniform_unitBall_of_tendsto_norm_sub_zero
    {α E F : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [NormedAddCommGroup F]
    [NormedSpace ℝ F]
    {l : Filter α}
    {U : α → (E →L[ℝ] F)}
    {S : E →L[ℝ] F}
    (h : Tendsto (fun a => ‖U a - S‖) l (nhds 0)) :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ a in l, ∀ x : E, ‖x‖ ≤ 1 → ‖U a x - S x‖ < ε := by
  have hdiff : Tendsto (fun a => U a - S) l (nhds 0) :=
    tendsto_zero_of_tendsto_norm_zero h
  simpa using
    continuousLinearMap_eventually_uniform_unitBall_zero_of_tendsto_zero hdiff

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
    (F_lim : E →L[ℝ] E)
    (hF : Continuous F)
    (hF_lim : Tendsto F atTop (nhds F_lim))
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r) :
    Tendsto
      (fun t : ℝ =>
        ‖U t - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim‖)
      atTop (nhds 0) := by
  let S := orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim
  let G : ℝ → (E →L[ℝ] E) := fun t => F t - F_lim
  let V : ℝ → (E →L[ℝ] E) := fun t => U t - S
  have hS : orthonormalDiagonalOperator b a * S = F_lim := by
    dsimp [S]
    exact orthonormalDiagonalHamiltonian_leftSteadyState_stationary
      b a δ hδ hδpos F_lim
  have hG : Continuous G := by
    dsimp [G]
    exact hF.sub continuous_const
  have hconstF : Tendsto (fun _ : ℝ => F_lim) atTop (nhds F_lim) :=
    tendsto_const_nhds
  have hGop : Tendsto G atTop (nhds 0) := by
    dsimp [G]
    simpa using hF_lim.sub hconstF
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
            (F r - F_lim) := by
      rw [← hS]
      noncomm_ring
    convert hsub using 1 <;> simp [V, G]
    simpa only [neg_mul] using hderiv.symm
  have htrack :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_vanishingInput_tendsto_norm_zero_left
      b a δ hδ hδpos G V hG hG0 hV
  simpa [V, S] using htrack

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
    (F_lim : E →L[ℝ] E)
    (hF : Continuous F)
    (hF_lim : Tendsto F atTop (nhds F_lim))
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r) :
    Tendsto
      (fun t : ℝ =>
        ‖U t - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim‖)
      atTop (nhds 0) := by
  let S := orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim
  let G : ℝ → (E →L[ℝ] E) := fun t => F t - F_lim
  let V : ℝ → (E →L[ℝ] E) := fun t => U t - S
  have hS : S * orthonormalDiagonalOperator b a = F_lim := by
    dsimp [S]
    exact orthonormalDiagonalHamiltonian_rightSteadyState_stationary
      b a δ hδ hδpos F_lim
  have hG : Continuous G := by
    dsimp [G]
    exact hF.sub continuous_const
  have hconstF : Tendsto (fun _ : ℝ => F_lim) atTop (nhds F_lim) :=
    tendsto_const_nhds
  have hGop : Tendsto G atTop (nhds 0) := by
    dsimp [G]
    simpa using hF_lim.sub hconstF
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
            (F r - F_lim) := by
      rw [← hS]
      noncomm_ring
    convert hsub using 1 <;> simp [V, G]
    simpa only [mul_neg] using hderiv.symm
  have htrack :=
    orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_vanishingInput_tendsto_norm_zero_right
      b a δ hδ hδpos G V hG hG0 hV
  simpa [V, S] using htrack

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
    (F_lim : E →L[ℝ] E)
    (hF : Continuous F)
    (hF_lim : Tendsto F atTop (nhds F_lim))
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r) :
    Tendsto U atTop
      (nhds (orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim)) :=
  tendsto_of_tendsto_norm_sub_zero
    (orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tendsto_norm_sub_left
      b a δ hδ hδpos F U F_lim hF hF_lim hU)

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
    (F_lim : E →L[ℝ] E)
    (hF : Continuous F)
    (hF_lim : Tendsto F atTop (nhds F_lim))
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r) :
    Tendsto U atTop
      (nhds (orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim)) :=
  tendsto_of_tendsto_norm_sub_zero
    (orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tendsto_norm_sub_right
      b a δ hδ hδpos F U F_lim hF hF_lim hU)

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
    (F_lim : E →L[ℝ] E)
    (hF : Continuous F)
    (hF_lim : Tendsto F atTop (nhds F_lim))
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r)
    (x : E) :
    Tendsto (fun t : ℝ => U t x) atTop
      (nhds (orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim x)) :=
  continuousLinearMap_tendsto_apply_of_tendsto_norm_sub_zero
    (orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tendsto_norm_sub_left
      b a δ hδ hδpos F U F_lim hF hF_lim hU) x

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
    (F_lim : E →L[ℝ] E)
    (hF : Continuous F)
    (hF_lim : Tendsto F atTop (nhds F_lim))
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r)
    (x : E) :
    Tendsto (fun t : ℝ => U t x) atTop
      (nhds (orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim x)) :=
  continuousLinearMap_tendsto_apply_of_tendsto_norm_sub_zero
    (orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tendsto_norm_sub_right
      b a δ hδ hδpos F U F_lim hF hF_lim hU) x

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
    (F_lim : E →L[ℝ] E)
    (hF : Continuous F)
    (hF_lim : Tendsto F atTop (nhds F_lim))
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ in atTop,
      ∀ x : E, ‖x‖ ≤ 1 →
        ‖U t x - orthonormalDiagonalHamiltonian_leftSteadyState b a F_lim x‖ < ε :=
  continuousLinearMap_eventually_uniform_unitBall_of_tendsto_norm_sub_zero
    (orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tendsto_norm_sub_left
      b a δ hδ hδpos F U F_lim hF hF_lim hU)

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
    (F_lim : E →L[ℝ] E)
    (hF : Continuous F)
    (hF_lim : Tendsto F atTop (nhds F_lim))
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ in atTop,
      ∀ x : E, ‖x‖ ≤ 1 →
        ‖U t x - orthonormalDiagonalHamiltonian_rightSteadyState b a F_lim x‖ < ε :=
  continuousLinearMap_eventually_uniform_unitBall_of_tendsto_norm_sub_zero
    (orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_asymptoticallyConstantInput_tendsto_norm_sub_right
      b a δ hδ hδpos F U F_lim hF hF_lim hU)

end

end MathlibAnalytic
end MGAP4D
