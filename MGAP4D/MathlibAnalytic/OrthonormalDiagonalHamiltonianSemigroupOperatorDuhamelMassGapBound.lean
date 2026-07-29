import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianSemigroupOperatorDuhamel
import MGAP4D.MathlibAnalytic.FiniteWilsonOSAutomaticExactGapSymmetricRayleighContraction
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

open MeasureTheory

/-- A uniform lower bound on the diagonal Hamiltonian energies gives the exact
operator-norm decay of the real spectral semigroup at nonnegative time. -/
theorem orthonormalDiagonalHamiltonianSemigroup_norm_le_exp_neg_lowerBound
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i)
    (t : ℝ)
    (ht : 0 ≤ t) :
    ‖orthonormalDiagonalHamiltonianSemigroup b a t‖ ≤
      Real.exp (-(t * δ)) := by
  let S := orthonormalDiagonalHamiltonianSemigroup b a t
  let C := Real.exp (-(t * δ))
  have hcoeff (i : ι) : Real.exp (-(t * a i)) ≤ C := by
    exact Real.exp_le_exp.mpr
      (neg_le_neg (mul_le_mul_of_nonneg_left (hδ i) ht))
  have hsymm : ∀ x y : E, inner ℝ (S x) y = inner ℝ (S y) x := by
    intro x y
    change inner ℝ
        (orthonormalDiagonalOperator b (fun i => Real.exp (-(t * a i))) x) y =
      inner ℝ
        (orthonormalDiagonalOperator b (fun i => Real.exp (-(t * a i))) y) x
    exact orthonormalDiagonalOperator_pairing_symmetric
      b (fun i => Real.exp (-(t * a i))) x y
  have hquad : ∀ z : E, |inner ℝ (S z) z| ≤ C * ‖z‖ ^ 2 := by
    intro z
    change
      |inner ℝ
        (orthonormalDiagonalOperator b (fun i => Real.exp (-(t * a i))) z) z| ≤
          C * ‖z‖ ^ 2
    rw [orthonormalDiagonalOperator_rayleigh]
    have hnonneg :
        0 ≤ ∑ i : ι, (inner ℝ (b i) z) ^ 2 * Real.exp (-(t * a i)) := by
      exact Finset.sum_nonneg (fun i _ =>
        mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
    rw [abs_of_nonneg hnonneg]
    calc
      ∑ i : ι, (inner ℝ (b i) z) ^ 2 * Real.exp (-(t * a i)) ≤
          ∑ i : ι, (inner ℝ (b i) z) ^ 2 * C := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hcoeff i) (sq_nonneg _)
      _ = C * ∑ i : ι, (inner ℝ (b i) z) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = C * ‖z‖ ^ 2 := by
        rw [b.sum_sq_inner_right z]
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le
    (𝕜 := ℝ) (E := E) (F := E) (T := S) (Real.exp_pos _).le
  intro x y hx hy
  simpa [C] using
    (real_symmetric_matrix_coefficient_le_of_abs_quadratic_bound
      S C hsymm hquad hx hy)

/-- Quantitative variation-of-constants estimate for the left operator equation.
A spectral lower bound `δ` damps both the initial operator and every forcing
contribution by the exact kernel `exp (-(t-s)δ)`. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_massGap_bound_left
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i)
    (t₀ t : ℝ)
    (ht : t₀ ≤ t)
    (A : E →L[ℝ] E)
    (F U : ℝ → (E →L[ℝ] E))
    (hF : Continuous F)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U ((-orthonormalDiagonalOperator b a) * U r + F r) r) :
    ‖U t‖ ≤
      Real.exp (-((t - t₀) * δ)) * ‖A‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * δ)) * ‖F s‖ := by
  let S := orthonormalDiagonalHamiltonianSemigroup b a
  have htime : 0 ≤ t - t₀ := sub_nonneg.mpr ht
  have hinitial :
      ‖S (t - t₀) * A‖ ≤ Real.exp (-((t - t₀) * δ)) * ‖A‖ := by
    calc
      ‖S (t - t₀) * A‖ ≤ ‖S (t - t₀)‖ * ‖A‖ := norm_mul_le _ _
      _ ≤ Real.exp (-((t - t₀) * δ)) * ‖A‖ :=
        mul_le_mul_of_nonneg_right
          (orthonormalDiagonalHamiltonianSemigroup_norm_le_exp_neg_lowerBound
            b a δ hδ (t - t₀) htime)
          (norm_nonneg A)
  have hweightContinuous :
      Continuous (fun s : ℝ => Real.exp (-((t - s) * δ)) * ‖F s‖) := by
    fun_prop
  have hintegral :
      ‖∫ s in t₀..t, S (t - s) * F s‖ ≤
        ∫ s in t₀..t, Real.exp (-((t - s) * δ)) * ‖F s‖ := by
    apply intervalIntegral.norm_integral_le_of_norm_le ht
    · filter_upwards with s
      intro hs
      have hst : 0 ≤ t - s := sub_nonneg.mpr hs.2
      calc
        ‖S (t - s) * F s‖ ≤ ‖S (t - s)‖ * ‖F s‖ := norm_mul_le _ _
        _ ≤ Real.exp (-((t - s) * δ)) * ‖F s‖ :=
          mul_le_mul_of_nonneg_right
            (orthonormalDiagonalHamiltonianSemigroup_norm_le_exp_neg_lowerBound
              b a δ hδ (t - s) hst)
            (norm_nonneg (F s))
    · exact hweightContinuous.intervalIntegrable t₀ t
  have hduhamel := congrFun
    (orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_left
      b a t₀ A F U hF hU0 hU) t
  calc
    ‖U t‖ = ‖S (t - t₀) * A + ∫ s in t₀..t, S (t - s) * F s‖ := by
      exact congrArg norm hduhamel
    _ ≤ ‖S (t - t₀) * A‖ + ‖∫ s in t₀..t, S (t - s) * F s‖ :=
      norm_add_le _ _
    _ ≤ Real.exp (-((t - t₀) * δ)) * ‖A‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * δ)) * ‖F s‖ :=
      add_le_add hinitial hintegral

/-- Quantitative variation-of-constants estimate for the right operator equation.
The same spectral kernel controls right Hamiltonian evolution without requiring
that the initial operator or forcing commute with the Hamiltonian. -/
theorem orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_massGap_bound_right
    {ι E : Type*}
    [Fintype ι]
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E)
    (a : ι → ℝ)
    (δ : ℝ)
    (hδ : ∀ i : ι, δ ≤ a i)
    (t₀ t : ℝ)
    (ht : t₀ ≤ t)
    (A : E →L[ℝ] E)
    (F U : ℝ → (E →L[ℝ] E))
    (hF : Continuous F)
    (hU0 : U t₀ = A)
    (hU : ∀ r : ℝ,
      HasDerivAt U (U r * (-orthonormalDiagonalOperator b a) + F r) r) :
    ‖U t‖ ≤
      Real.exp (-((t - t₀) * δ)) * ‖A‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * δ)) * ‖F s‖ := by
  let S := orthonormalDiagonalHamiltonianSemigroup b a
  have htime : 0 ≤ t - t₀ := sub_nonneg.mpr ht
  have hinitial :
      ‖A * S (t - t₀)‖ ≤ Real.exp (-((t - t₀) * δ)) * ‖A‖ := by
    calc
      ‖A * S (t - t₀)‖ ≤ ‖A‖ * ‖S (t - t₀)‖ := norm_mul_le _ _
      _ ≤ ‖A‖ * Real.exp (-((t - t₀) * δ)) :=
        mul_le_mul_of_nonneg_left
          (orthonormalDiagonalHamiltonianSemigroup_norm_le_exp_neg_lowerBound
            b a δ hδ (t - t₀) htime)
          (norm_nonneg A)
      _ = Real.exp (-((t - t₀) * δ)) * ‖A‖ := by ring
  have hweightContinuous :
      Continuous (fun s : ℝ => Real.exp (-((t - s) * δ)) * ‖F s‖) := by
    fun_prop
  have hintegral :
      ‖∫ s in t₀..t, F s * S (t - s)‖ ≤
        ∫ s in t₀..t, Real.exp (-((t - s) * δ)) * ‖F s‖ := by
    apply intervalIntegral.norm_integral_le_of_norm_le ht
    · filter_upwards with s
      intro hs
      have hst : 0 ≤ t - s := sub_nonneg.mpr hs.2
      calc
        ‖F s * S (t - s)‖ ≤ ‖F s‖ * ‖S (t - s)‖ := norm_mul_le _ _
        _ ≤ ‖F s‖ * Real.exp (-((t - s) * δ)) :=
          mul_le_mul_of_nonneg_left
            (orthonormalDiagonalHamiltonianSemigroup_norm_le_exp_neg_lowerBound
              b a δ hδ (t - s) hst)
            (norm_nonneg (F s))
        _ = Real.exp (-((t - s) * δ)) * ‖F s‖ := by ring
    · exact hweightContinuous.intervalIntegrable t₀ t
  have hduhamel := congrFun
    (orthonormalDiagonalHamiltonianSemigroup_operator_duhamel_right
      b a t₀ A F U hF hU0 hU) t
  calc
    ‖U t‖ = ‖A * S (t - t₀) + ∫ s in t₀..t, F s * S (t - s)‖ := by
      exact congrArg norm hduhamel
    _ ≤ ‖A * S (t - t₀)‖ + ‖∫ s in t₀..t, F s * S (t - s)‖ :=
      norm_add_le _ _
    _ ≤ Real.exp (-((t - t₀) * δ)) * ‖A‖ +
        ∫ s in t₀..t, Real.exp (-((t - s) * δ)) * ‖F s‖ :=
      add_le_add hinitial hintegral

end

end MathlibAnalytic
end MGAP4D
