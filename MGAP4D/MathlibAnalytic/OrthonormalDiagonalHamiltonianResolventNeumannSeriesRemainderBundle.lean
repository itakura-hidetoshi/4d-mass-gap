import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianResolventAnalyticNeumannBundle
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace LinearPMap ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 1200000

/-- The ordered Neumann terms based at `lambda` sum in operator norm to the
resolvent at `mu` throughout the full distance-to-gap ball. -/
theorem orthonormalDiagonalHamiltonianResolvent_neumann_hasSum_of_norm_sub_lt
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    {lambda mu : ℝ} (hlambda : lambda < delta)
    (hdist : ‖mu - lambda‖ < delta - lambda) :
    HasSum
      (fun k : ℕ =>
        (((mu - lambda) •
          orthonormalDiagonalHamiltonianResolvent b a lambda) ^ k) *
            orthonormalDiagonalHamiltonianResolvent b a lambda)
      (orthonormalDiagonalHamiltonianResolvent b a mu) := by
  let Rlambda := orthonormalDiagonalHamiltonianResolvent b a lambda
  let Rmu := orthonormalDiagonalHamiltonianResolvent b a mu
  let perturb : E →L[ℝ] E := (mu - lambda) • Rlambda
  change HasSum (fun k : ℕ => perturb ^ k * Rlambda) Rmu
  have hsmall : ‖perturb‖ < 1 := by
    simpa [perturb, Rlambda] using
      (orthonormalDiagonalHamiltonianResolvent_perturb_norm_lt_one_of_norm_sub_lt
        b a delta hdelta hlambda hdist)
  have hseries :
      HasSum (fun k : ℕ => perturb ^ k * Rlambda)
        (Ring.inverse (1 - perturb) * Rlambda) :=
    (hasSum_geom_series_inverse perturb hsmall).mul_right Rlambda
  have hlocal : Rmu = Ring.inverse (1 - perturb) * Rlambda := by
    simpa [perturb, Rlambda, Rmu] using
      (orthonormalDiagonalHamiltonianResolvent_eq_inverse_one_sub_mul_of_norm_sub_lt
        b a delta hdelta hlambda hdist)
  rw [← hlocal] at hseries
  exact hseries

/-- The ordered local Neumann series is summable in operator norm throughout
the full distance-to-gap ball. -/
theorem orthonormalDiagonalHamiltonianResolvent_neumann_summable_of_norm_sub_lt
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    {lambda mu : ℝ} (hlambda : lambda < delta)
    (hdist : ‖mu - lambda‖ < delta - lambda) :
    Summable
      (fun k : ℕ =>
        (((mu - lambda) •
          orthonormalDiagonalHamiltonianResolvent b a lambda) ^ k) *
            orthonormalDiagonalHamiltonianResolvent b a lambda) :=
  (orthonormalDiagonalHamiltonianResolvent_neumann_hasSum_of_norm_sub_lt
    b a delta hdelta hlambda hdist).summable

/-- The operator-norm sum of the ordered local Neumann series is exactly the
resolvent at the target parameter. -/
theorem orthonormalDiagonalHamiltonianResolvent_neumann_tsum_eq_of_norm_sub_lt
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    {lambda mu : ℝ} (hlambda : lambda < delta)
    (hdist : ‖mu - lambda‖ < delta - lambda) :
    (∑' k : ℕ,
      (((mu - lambda) •
        orthonormalDiagonalHamiltonianResolvent b a lambda) ^ k) *
          orthonormalDiagonalHamiltonianResolvent b a lambda) =
      orthonormalDiagonalHamiltonianResolvent b a mu :=
  (orthonormalDiagonalHamiltonianResolvent_neumann_hasSum_of_norm_sub_lt
    b a delta hdelta hlambda hdist).tsum_eq

/-- The finite ordered Neumann partial sums converge in operator norm to the
resolvent at the target parameter. -/
theorem orthonormalDiagonalHamiltonianResolvent_neumann_partialSum_tendsto_of_norm_sub_lt
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    {lambda mu : ℝ} (hlambda : lambda < delta)
    (hdist : ‖mu - lambda‖ < delta - lambda) :
    Tendsto
      (fun N : ℕ =>
        (∑ k ∈ Finset.range N,
          ((mu - lambda) •
            orthonormalDiagonalHamiltonianResolvent b a lambda) ^ k) *
          orthonormalDiagonalHamiltonianResolvent b a lambda)
      atTop
      (𝓝 (orthonormalDiagonalHamiltonianResolvent b a mu)) := by
  simpa only [Finset.sum_mul] using
    (orthonormalDiagonalHamiltonianResolvent_neumann_hasSum_of_norm_sub_lt
      b a delta hdelta hlambda hdist).tendsto_sum_nat

/-- Exact ordered remainder identity for every finite Neumann truncation. -/
theorem orthonormalDiagonalHamiltonianResolvent_sub_neumann_partialSum_eq
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    (N : ℕ) {lambda mu : ℝ} (hlambda : lambda < delta)
    (hdist : ‖mu - lambda‖ < delta - lambda) :
    orthonormalDiagonalHamiltonianResolvent b a mu -
        (∑ k ∈ Finset.range N,
          ((mu - lambda) •
            orthonormalDiagonalHamiltonianResolvent b a lambda) ^ k) *
          orthonormalDiagonalHamiltonianResolvent b a lambda =
      ((mu - lambda) •
        orthonormalDiagonalHamiltonianResolvent b a lambda) ^ N *
        orthonormalDiagonalHamiltonianResolvent b a mu := by
  have h :=
    orthonormalDiagonalHamiltonianResolvent_neumann_nth_order_of_norm_sub_lt
      b a delta hdelta N hlambda hdist
  rw [h]
  abel

/-- The truncation error is bounded by the norm of the exact ordered remainder
and the target resolvent gap bound. -/
theorem orthonormalDiagonalHamiltonianResolvent_sub_neumann_partialSum_norm_le
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    (N : ℕ) {lambda mu : ℝ} (hlambda : lambda < delta)
    (hdist : ‖mu - lambda‖ < delta - lambda) :
    ‖orthonormalDiagonalHamiltonianResolvent b a mu -
        (∑ k ∈ Finset.range N,
          ((mu - lambda) •
            orthonormalDiagonalHamiltonianResolvent b a lambda) ^ k) *
          orthonormalDiagonalHamiltonianResolvent b a lambda‖ ≤
      ‖(mu - lambda) •
          orthonormalDiagonalHamiltonianResolvent b a lambda‖ ^ N *
        (delta - mu)⁻¹ := by
  have hdistAbs : |mu - lambda| < delta - lambda := by
    simpa only [Real.norm_eq_abs] using hdist
  have hmu : mu < delta := by
    have hle : mu - lambda ≤ |mu - lambda| := le_abs_self (mu - lambda)
    linarith
  rw [orthonormalDiagonalHamiltonianResolvent_sub_neumann_partialSum_eq
    b a delta hdelta N hlambda hdist]
  have hRmu :=
    orthonormalDiagonalHamiltonianResolvent_norm_le_inv_sub
      b a delta mu hdelta hmu
  calc
    ‖((mu - lambda) •
        orthonormalDiagonalHamiltonianResolvent b a lambda) ^ N *
        orthonormalDiagonalHamiltonianResolvent b a mu‖ ≤
      ‖((mu - lambda) •
        orthonormalDiagonalHamiltonianResolvent b a lambda) ^ N‖ *
        ‖orthonormalDiagonalHamiltonianResolvent b a mu‖ :=
      norm_mul_le _ _
    _ = ‖(mu - lambda) •
          orthonormalDiagonalHamiltonianResolvent b a lambda‖ ^ N *
        ‖orthonormalDiagonalHamiltonianResolvent b a mu‖ := by
      rw [norm_pow]
    _ ≤ ‖(mu - lambda) •
          orthonormalDiagonalHamiltonianResolvent b a lambda‖ ^ N *
        (delta - mu)⁻¹ :=
      mul_le_mul_of_nonneg_left hRmu (pow_nonneg (norm_nonneg _) N)

/-- Explicit geometric truncation bound in terms of the parameter displacement
and both distances to the spectral gap. -/
theorem orthonormalDiagonalHamiltonianResolvent_sub_neumann_partialSum_norm_le_explicit
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    (N : ℕ) {lambda mu : ℝ} (hlambda : lambda < delta)
    (hdist : ‖mu - lambda‖ < delta - lambda) :
    ‖orthonormalDiagonalHamiltonianResolvent b a mu -
        (∑ k ∈ Finset.range N,
          ((mu - lambda) •
            orthonormalDiagonalHamiltonianResolvent b a lambda) ^ k) *
          orthonormalDiagonalHamiltonianResolvent b a lambda‖ ≤
      (‖mu - lambda‖ * (delta - lambda)⁻¹) ^ N *
        (delta - mu)⁻¹ := by
  have hdistAbs : |mu - lambda| < delta - lambda := by
    simpa only [Real.norm_eq_abs] using hdist
  have hmu : mu < delta := by
    have hle : mu - lambda ≤ |mu - lambda| := le_abs_self (mu - lambda)
    linarith
  have hRlambda :=
    orthonormalDiagonalHamiltonianResolvent_norm_le_inv_sub
      b a delta lambda hdelta hlambda
  have hperturb :
      ‖(mu - lambda) •
          orthonormalDiagonalHamiltonianResolvent b a lambda‖ ≤
        ‖mu - lambda‖ * (delta - lambda)⁻¹ := by
    calc
      ‖(mu - lambda) •
          orthonormalDiagonalHamiltonianResolvent b a lambda‖ ≤
        ‖mu - lambda‖ *
          ‖orthonormalDiagonalHamiltonianResolvent b a lambda‖ :=
        ContinuousLinearMap.opNorm_smul_le
          (mu - lambda)
          (orthonormalDiagonalHamiltonianResolvent b a lambda)
      _ ≤ ‖mu - lambda‖ * (delta - lambda)⁻¹ :=
        mul_le_mul_of_nonneg_left hRlambda (norm_nonneg (mu - lambda))
  have hpow :
      ‖(mu - lambda) •
          orthonormalDiagonalHamiltonianResolvent b a lambda‖ ^ N ≤
        (‖mu - lambda‖ * (delta - lambda)⁻¹) ^ N :=
    pow_le_pow_left₀ (norm_nonneg _) hperturb N
  calc
    ‖orthonormalDiagonalHamiltonianResolvent b a mu -
        (∑ k ∈ Finset.range N,
          ((mu - lambda) •
            orthonormalDiagonalHamiltonianResolvent b a lambda) ^ k) *
          orthonormalDiagonalHamiltonianResolvent b a lambda‖ ≤
      ‖(mu - lambda) •
          orthonormalDiagonalHamiltonianResolvent b a lambda‖ ^ N *
        (delta - mu)⁻¹ :=
      orthonormalDiagonalHamiltonianResolvent_sub_neumann_partialSum_norm_le
        b a delta hdelta N hlambda hdist
    _ ≤ (‖mu - lambda‖ * (delta - lambda)⁻¹) ^ N *
        (delta - mu)⁻¹ :=
      mul_le_mul_of_nonneg_right hpow
        (inv_nonneg.mpr (sub_nonneg.mpr hmu.le))

/-- Operator-norm Neumann summation, convergence of partial sums, exact ordered
remainders, and the explicit geometric truncation estimate as one package. -/
theorem orthonormalDiagonalHamiltonianResolventNeumannSeriesRemainder_package
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i) :
    ∀ {lambda mu : ℝ} (hlambda : lambda < delta)
        (hdist : ‖mu - lambda‖ < delta - lambda),
      HasSum
          (fun k : ℕ =>
            (((mu - lambda) •
              orthonormalDiagonalHamiltonianResolvent b a lambda) ^ k) *
                orthonormalDiagonalHamiltonianResolvent b a lambda)
          (orthonormalDiagonalHamiltonianResolvent b a mu) ∧
        Tendsto
          (fun N : ℕ =>
            (∑ k ∈ Finset.range N,
              ((mu - lambda) •
                orthonormalDiagonalHamiltonianResolvent b a lambda) ^ k) *
              orthonormalDiagonalHamiltonianResolvent b a lambda)
          atTop
          (𝓝 (orthonormalDiagonalHamiltonianResolvent b a mu)) ∧
        ∀ N : ℕ,
          orthonormalDiagonalHamiltonianResolvent b a mu -
              (∑ k ∈ Finset.range N,
                ((mu - lambda) •
                  orthonormalDiagonalHamiltonianResolvent b a lambda) ^ k) *
                orthonormalDiagonalHamiltonianResolvent b a lambda =
            ((mu - lambda) •
              orthonormalDiagonalHamiltonianResolvent b a lambda) ^ N *
              orthonormalDiagonalHamiltonianResolvent b a mu ∧
          ‖orthonormalDiagonalHamiltonianResolvent b a mu -
              (∑ k ∈ Finset.range N,
                ((mu - lambda) •
                  orthonormalDiagonalHamiltonianResolvent b a lambda) ^ k) *
                orthonormalDiagonalHamiltonianResolvent b a lambda‖ ≤
            (‖mu - lambda‖ * (delta - lambda)⁻¹) ^ N *
              (delta - mu)⁻¹ := by
  intro lambda mu hlambda hdist
  refine ⟨orthonormalDiagonalHamiltonianResolvent_neumann_hasSum_of_norm_sub_lt
      b a delta hdelta hlambda hdist,
    orthonormalDiagonalHamiltonianResolvent_neumann_partialSum_tendsto_of_norm_sub_lt
      b a delta hdelta hlambda hdist, ?_⟩
  intro N
  exact ⟨orthonormalDiagonalHamiltonianResolvent_sub_neumann_partialSum_eq
      b a delta hdelta N hlambda hdist,
    orthonormalDiagonalHamiltonianResolvent_sub_neumann_partialSum_norm_le_explicit
      b a delta hdelta N hlambda hdist⟩

end MathlibAnalytic
end MGAP4D

end