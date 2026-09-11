import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorAsymptoticIncrementalSteadyBiasBundle
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The real spectral shift `H - λI` of a finite orthonormal-diagonal Hamiltonian. -/
noncomputable def orthonormalDiagonalHamiltonianShiftedOperator
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (lambda : ℝ) :
    E →L[ℝ] E :=
  orthonormalDiagonalOperator b (fun i => a i - lambda)

/-- The finite-dimensional real resolvent `(H - λI)⁻¹`. -/
noncomputable def orthonormalDiagonalHamiltonianResolvent
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (lambda : ℝ) :
    E →L[ℝ] E :=
  orthonormalDiagonalHamiltonianInverse b (fun i => a i - lambda)

@[simp]
theorem orthonormalDiagonalHamiltonianShiftedOperator_apply_basis
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (lambda : ℝ) (i : ι) :
    orthonormalDiagonalHamiltonianShiftedOperator b a lambda (b i) =
      (a i - lambda) • b i := by
  exact orthonormalDiagonalOperator_apply_basis b (fun j => a j - lambda) i

@[simp]
theorem orthonormalDiagonalHamiltonianResolvent_apply_basis
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (lambda : ℝ) (i : ι) :
    orthonormalDiagonalHamiltonianResolvent b a lambda (b i) =
      (a i - lambda)⁻¹ • b i := by
  exact orthonormalDiagonalHamiltonianInverse_apply_basis
    b (fun j => a j - lambda) i

/-- The diagonal spectral shift is the actual operator difference `H - λI`. -/
theorem orthonormalDiagonalHamiltonianShiftedOperator_eq_sub_smul_id
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (lambda : ℝ) :
    orthonormalDiagonalHamiltonianShiftedOperator b a lambda =
      orthonormalDiagonalOperator b a - lambda • (1 : E →L[ℝ] E) := by
  apply ContinuousLinearMap.ext
  intro x
  change orthonormalDiagonalOperator b (fun i => a i - lambda) x =
    orthonormalDiagonalOperator b a x - lambda • x
  rw [orthonormalDiagonalOperator_apply b (fun i => a i - lambda) x,
    orthonormalDiagonalOperator_apply b a x]
  conv_rhs =>
    rhs
    rw [← b.sum_repr' x]
  rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  module

/-- Below the spectral lower bound, the resolvent is a left inverse of `H - λI`. -/
theorem orthonormalDiagonalHamiltonianResolvent_mul_shiftedOperator
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta lambda : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i) (hlambda : lambda < delta) :
    orthonormalDiagonalHamiltonianResolvent b a lambda *
        orthonormalDiagonalHamiltonianShiftedOperator b a lambda = 1 := by
  apply orthonormalDiagonalHamiltonianInverse_mul_operator
    b (fun i => a i - lambda) (delta - lambda)
  · intro i
    linarith [hdelta i]
  · linarith

/-- Below the spectral lower bound, the resolvent is also a right inverse. -/
theorem orthonormalDiagonalHamiltonianShiftedOperator_mul_resolvent
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta lambda : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i) (hlambda : lambda < delta) :
    orthonormalDiagonalHamiltonianShiftedOperator b a lambda *
        orthonormalDiagonalHamiltonianResolvent b a lambda = 1 := by
  apply orthonormalDiagonalHamiltonianOperator_mul_inverse
    b (fun i => a i - lambda) (delta - lambda)
  · intro i
    linarith [hdelta i]
  · linarith

/-- Exact gap-to-resolvent operator-norm estimate. -/
theorem orthonormalDiagonalHamiltonianResolvent_norm_le_inv_sub
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta lambda : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i) (hlambda : lambda < delta) :
    ‖orthonormalDiagonalHamiltonianResolvent b a lambda‖ ≤
      (delta - lambda)⁻¹ := by
  have hgap : 0 < delta - lambda := sub_pos.mpr hlambda
  have hcoeff (i : ι) : (a i - lambda)⁻¹ ≤ (delta - lambda)⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le hgap (sub_le_sub_right (hdelta i) lambda)
  have hcoeffNonneg (i : ι) : 0 ≤ (a i - lambda)⁻¹ := by
    apply inv_nonneg.mpr
    exact sub_nonneg.mpr (le_trans hlambda.le (hdelta i))
  have hsymm : ∀ x y : E,
      inner ℝ (orthonormalDiagonalHamiltonianResolvent b a lambda x) y =
        inner ℝ (orthonormalDiagonalHamiltonianResolvent b a lambda y) x := by
    intro x y
    change inner ℝ
        (orthonormalDiagonalOperator b (fun i => (a i - lambda)⁻¹) x) y =
      inner ℝ
        (orthonormalDiagonalOperator b (fun i => (a i - lambda)⁻¹) y) x
    exact orthonormalDiagonalOperator_pairing_symmetric
      b (fun i => (a i - lambda)⁻¹) x y
  have hquad : ∀ z : E,
      |inner ℝ (orthonormalDiagonalHamiltonianResolvent b a lambda z) z| ≤
        (delta - lambda)⁻¹ * ‖z‖ ^ 2 := by
    intro z
    change
      |inner ℝ
        (orthonormalDiagonalOperator b (fun i => (a i - lambda)⁻¹) z) z| ≤
          (delta - lambda)⁻¹ * ‖z‖ ^ 2
    rw [orthonormalDiagonalOperator_rayleigh]
    have hnonneg :
        0 ≤ ∑ i : ι, (inner ℝ (b i) z) ^ 2 * (a i - lambda)⁻¹ := by
      exact Finset.sum_nonneg (fun i _ =>
        mul_nonneg (sq_nonneg _) (hcoeffNonneg i))
    rw [abs_of_nonneg hnonneg]
    calc
      ∑ i : ι, (inner ℝ (b i) z) ^ 2 * (a i - lambda)⁻¹ ≤
          ∑ i : ι, (inner ℝ (b i) z) ^ 2 * (delta - lambda)⁻¹ := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hcoeff i) (sq_nonneg _)
      _ = (delta - lambda)⁻¹ *
          ∑ i : ι, (inner ℝ (b i) z) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (delta - lambda)⁻¹ * ‖z‖ ^ 2 := by
        rw [b.sum_sq_inner_right z]
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le
    (𝕜 := ℝ) (E := E) (F := E)
    (T := orthonormalDiagonalHamiltonianResolvent b a lambda)
    (inv_nonneg.mpr hgap.le)
  intro x y hx hy
  simpa using
    (real_symmetric_matrix_coefficient_le_of_abs_quadratic_bound
      (orthonormalDiagonalHamiltonianResolvent b a lambda)
      (delta - lambda)⁻¹ hsymm hquad hx hy)

/-- Pointwise resolvent control on every state. -/
theorem orthonormalDiagonalHamiltonianResolvent_apply_norm_le
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta lambda : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i) (hlambda : lambda < delta)
    (x : E) :
    ‖orthonormalDiagonalHamiltonianResolvent b a lambda x‖ ≤
      (delta - lambda)⁻¹ * ‖x‖ := by
  calc
    ‖orthonormalDiagonalHamiltonianResolvent b a lambda x‖ ≤
        ‖orthonormalDiagonalHamiltonianResolvent b a lambda‖ * ‖x‖ :=
      (orthonormalDiagonalHamiltonianResolvent b a lambda).le_opNorm x
    _ ≤ (delta - lambda)⁻¹ * ‖x‖ :=
      mul_le_mul_of_nonneg_right
        (orthonormalDiagonalHamiltonianResolvent_norm_le_inv_sub
          b a delta lambda hdelta hlambda) (norm_nonneg x)

/-- Left multiplication by the resolvent has the exact gap gain. -/
theorem orthonormalDiagonalHamiltonianResolvent_mul_norm_le
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta lambda : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i) (hlambda : lambda < delta)
    (Q : E →L[ℝ] E) :
    ‖orthonormalDiagonalHamiltonianResolvent b a lambda * Q‖ ≤
      (delta - lambda)⁻¹ * ‖Q‖ := by
  exact (norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_right
      (orthonormalDiagonalHamiltonianResolvent_norm_le_inv_sub
        b a delta lambda hdelta hlambda) (norm_nonneg Q))

/-- Right multiplication has the same gain, with no commutation assumption. -/
theorem orthonormalDiagonalHamiltonian_mul_resolvent_norm_le
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta lambda : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i) (hlambda : lambda < delta)
    (Q : E →L[ℝ] E) :
    ‖Q * orthonormalDiagonalHamiltonianResolvent b a lambda‖ ≤
      (delta - lambda)⁻¹ * ‖Q‖ := by
  calc
    ‖Q * orthonormalDiagonalHamiltonianResolvent b a lambda‖ ≤
        ‖Q‖ * ‖orthonormalDiagonalHamiltonianResolvent b a lambda‖ :=
      norm_mul_le _ _
    _ ≤ ‖Q‖ * (delta - lambda)⁻¹ :=
      mul_le_mul_of_nonneg_left
        (orthonormalDiagonalHamiltonianResolvent_norm_le_inv_sub
          b a delta lambda hdelta hlambda) (norm_nonneg Q)
    _ = (delta - lambda)⁻¹ * ‖Q‖ := by ring

@[simp]
theorem orthonormalDiagonalHamiltonianResolvent_zero
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) :
    orthonormalDiagonalHamiltonianResolvent b a 0 =
      orthonormalDiagonalHamiltonianInverse b a := by
  simp [orthonormalDiagonalHamiltonianResolvent]

/-- The inverse Hamiltonian has norm at most the reciprocal spectral gap. -/
theorem orthonormalDiagonalHamiltonianInverse_norm_le_inv
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i) (hdeltaPos : 0 < delta) :
    ‖orthonormalDiagonalHamiltonianInverse b a‖ ≤ delta⁻¹ := by
  simpa using
    (orthonormalDiagonalHamiltonianResolvent_norm_le_inv_sub
      b a delta 0 hdelta hdeltaPos)

/-- The left steady response is bounded by `δ⁻¹ ‖Qinf‖`. -/
theorem orthonormalDiagonalHamiltonianSteadyResponseLeft_norm_le
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i) (hdeltaPos : 0 < delta)
    (Qinf : E →L[ℝ] E) :
    ‖orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf‖ ≤
      delta⁻¹ * ‖Qinf‖ := by
  exact (norm_mul_le _ _).trans
    (mul_le_mul_of_nonneg_right
      (orthonormalDiagonalHamiltonianInverse_norm_le_inv
        b a delta hdelta hdeltaPos) (norm_nonneg Qinf))

/-- The right steady response has the same norm bound without commutation. -/
theorem orthonormalDiagonalHamiltonianSteadyResponseRight_norm_le
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i) (hdeltaPos : 0 < delta)
    (Qinf : E →L[ℝ] E) :
    ‖orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf‖ ≤
      delta⁻¹ * ‖Qinf‖ := by
  calc
    ‖orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf‖ ≤
        ‖Qinf‖ * ‖orthonormalDiagonalHamiltonianInverse b a‖ :=
      norm_mul_le _ _
    _ ≤ ‖Qinf‖ * delta⁻¹ :=
      mul_le_mul_of_nonneg_left
        (orthonormalDiagonalHamiltonianInverse_norm_le_inv
          b a delta hdelta hdeltaPos) (norm_nonneg Qinf)
    _ = delta⁻¹ * ‖Qinf‖ := by ring

/-- Any left equilibrium is uniquely the inverse-Hamiltonian steady response. -/
theorem eq_orthonormalDiagonalHamiltonianSteadyResponseLeft_of_equilibrium
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i) (hdeltaPos : 0 < delta)
    (Qinf W : E →L[ℝ] E)
    (hW : orthonormalDiagonalOperator b a * W = Qinf) :
    W = orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf := by
  have hinv := orthonormalDiagonalHamiltonianInverse_mul_operator
    b a delta hdelta hdeltaPos
  calc
    W = 1 * W := (one_mul W).symm
    _ = (orthonormalDiagonalHamiltonianInverse b a *
          orthonormalDiagonalOperator b a) * W := by rw [hinv]
    _ = orthonormalDiagonalHamiltonianInverse b a *
          (orthonormalDiagonalOperator b a * W) := mul_assoc _ _ _
    _ = orthonormalDiagonalHamiltonianInverse b a * Qinf := by rw [hW]
    _ = orthonormalDiagonalHamiltonianSteadyResponseLeft b a Qinf := rfl

/-- Any right equilibrium is uniquely `Qinf H⁻¹`, without commutation. -/
theorem eq_orthonormalDiagonalHamiltonianSteadyResponseRight_of_equilibrium
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i) (hdeltaPos : 0 < delta)
    (Qinf W : E →L[ℝ] E)
    (hW : W * orthonormalDiagonalOperator b a = Qinf) :
    W = orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf := by
  have hinv := orthonormalDiagonalHamiltonianOperator_mul_inverse
    b a delta hdelta hdeltaPos
  calc
    W = W * 1 := (mul_one W).symm
    _ = W * (orthonormalDiagonalOperator b a *
          orthonormalDiagonalHamiltonianInverse b a) := by rw [hinv]
    _ = (W * orthonormalDiagonalOperator b a) *
          orthonormalDiagonalHamiltonianInverse b a := (mul_assoc _ _ _).symm
    _ = Qinf * orthonormalDiagonalHamiltonianInverse b a := by rw [hW]
    _ = orthonormalDiagonalHamiltonianSteadyResponseRight b a Qinf := rfl

end

end MathlibAnalytic
end MGAP4D
