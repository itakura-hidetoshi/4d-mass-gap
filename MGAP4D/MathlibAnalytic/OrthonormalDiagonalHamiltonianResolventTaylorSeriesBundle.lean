import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianResolventFactorialDerivativeBundle
import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianResolventNeumannSeriesRemainderBundle
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace LinearPMap ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 1600000

/-- The normalized `k`-th derivative is exactly the `(k+1)`-st resolvent power. -/
theorem orthonormalDiagonalHamiltonianResolvent_invFactorial_smul_iteratedDeriv_eq_pow
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    (k : ℕ) {lambda : ℝ} (hlambda : lambda < delta) :
    ((k.factorial : ℝ)⁻¹) •
        iteratedDeriv k (orthonormalDiagonalHamiltonianResolvent b a) lambda =
      (orthonormalDiagonalHamiltonianResolvent b a lambda) ^ (k + 1) := by
  rw [orthonormalDiagonalHamiltonianResolvent_iteratedDeriv
    b a delta hdelta k hlambda]
  have hk : (k.factorial : ℝ) ≠ 0 := by positivity
  simp [smul_smul, hk]

/-- Each ordered Neumann term is the corresponding scalar-power resolvent term,
without introducing operator commutativity. -/
theorem orthonormalDiagonalHamiltonianResolvent_neumann_term_eq_power_term
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ)
    (k : ℕ) (lambda mu : ℝ) :
    (((mu - lambda) •
        orthonormalDiagonalHamiltonianResolvent b a lambda) ^ k) *
        orthonormalDiagonalHamiltonianResolvent b a lambda =
      (mu - lambda) ^ k •
        (orthonormalDiagonalHamiltonianResolvent b a lambda) ^ (k + 1) := by
  let Rlambda := orthonormalDiagonalHamiltonianResolvent b a lambda
  change (((mu - lambda) • Rlambda) ^ k) * Rlambda =
    (mu - lambda) ^ k • Rlambda ^ (k + 1)
  calc
    (((mu - lambda) • Rlambda) ^ k) * Rlambda =
        ((mu - lambda) ^ k • Rlambda ^ k) * Rlambda := by
      rw [smul_pow]
    _ = (mu - lambda) ^ k • (Rlambda ^ k * Rlambda) :=
      Algebra.smul_mul_assoc _ _ _
    _ = (mu - lambda) ^ k • Rlambda ^ (k + 1) := by
      rw [pow_succ]

/-- The `k`-th Taylor term written with the exact iterated derivative equals the
ordered `k`-th Neumann term. -/
theorem orthonormalDiagonalHamiltonianResolvent_taylor_term_eq_neumann_term
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    (k : ℕ) {lambda mu : ℝ} (hlambda : lambda < delta) :
    (((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
        iteratedDeriv k (orthonormalDiagonalHamiltonianResolvent b a) lambda) =
      (((mu - lambda) •
          orthonormalDiagonalHamiltonianResolvent b a lambda) ^ k) *
        orthonormalDiagonalHamiltonianResolvent b a lambda := by
  calc
    (((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
        iteratedDeriv k (orthonormalDiagonalHamiltonianResolvent b a) lambda) =
      (mu - lambda) ^ k •
        (((k.factorial : ℝ)⁻¹) •
          iteratedDeriv k (orthonormalDiagonalHamiltonianResolvent b a) lambda) := by
      rw [smul_smul]
    _ = (mu - lambda) ^ k •
        (orthonormalDiagonalHamiltonianResolvent b a lambda) ^ (k + 1) := by
      rw [orthonormalDiagonalHamiltonianResolvent_invFactorial_smul_iteratedDeriv_eq_pow
        b a delta hdelta k hlambda]
    _ = (((mu - lambda) •
          orthonormalDiagonalHamiltonianResolvent b a lambda) ^ k) *
        orthonormalDiagonalHamiltonianResolvent b a lambda :=
      (orthonormalDiagonalHamiltonianResolvent_neumann_term_eq_power_term
        b a k lambda mu).symm

/-- Every finite Taylor partial sum equals the corresponding ordered Neumann
partial sum. -/
theorem orthonormalDiagonalHamiltonianResolvent_taylor_partialSum_eq_neumann_partialSum
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    (N : ℕ) {lambda mu : ℝ} (hlambda : lambda < delta) :
    (∑ k ∈ Finset.range N,
        ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
          iteratedDeriv k (orthonormalDiagonalHamiltonianResolvent b a) lambda) =
      (∑ k ∈ Finset.range N,
        ((mu - lambda) •
          orthonormalDiagonalHamiltonianResolvent b a lambda) ^ k) *
        orthonormalDiagonalHamiltonianResolvent b a lambda := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  exact orthonormalDiagonalHamiltonianResolvent_taylor_term_eq_neumann_term
    b a delta hdelta k hlambda

/-- The exact derivative Taylor series sums in operator norm to the target
resolvent throughout the full distance-to-gap ball. -/
theorem orthonormalDiagonalHamiltonianResolvent_taylor_hasSum_of_norm_sub_lt
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    {lambda mu : ℝ} (hlambda : lambda < delta)
    (hdist : ‖mu - lambda‖ < delta - lambda) :
    HasSum
      (fun k : ℕ =>
        ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
          iteratedDeriv k (orthonormalDiagonalHamiltonianResolvent b a) lambda)
      (orthonormalDiagonalHamiltonianResolvent b a mu) := by
  have hneumann :=
    orthonormalDiagonalHamiltonianResolvent_neumann_hasSum_of_norm_sub_lt
      b a delta hdelta hlambda hdist
  have hterms :
      (fun k : ℕ =>
        ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
          iteratedDeriv k (orthonormalDiagonalHamiltonianResolvent b a) lambda) =
      (fun k : ℕ =>
        (((mu - lambda) •
          orthonormalDiagonalHamiltonianResolvent b a lambda) ^ k) *
            orthonormalDiagonalHamiltonianResolvent b a lambda) := by
    funext k
    exact orthonormalDiagonalHamiltonianResolvent_taylor_term_eq_neumann_term
      b a delta hdelta k hlambda
  rw [hterms]
  exact hneumann

/-- The exact derivative Taylor series is summable in operator norm. -/
theorem orthonormalDiagonalHamiltonianResolvent_taylor_summable_of_norm_sub_lt
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    {lambda mu : ℝ} (hlambda : lambda < delta)
    (hdist : ‖mu - lambda‖ < delta - lambda) :
    Summable
      (fun k : ℕ =>
        ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
          iteratedDeriv k (orthonormalDiagonalHamiltonianResolvent b a) lambda) :=
  (orthonormalDiagonalHamiltonianResolvent_taylor_hasSum_of_norm_sub_lt
    b a delta hdelta hlambda hdist).summable

/-- The operator-norm Taylor sum is exactly the resolvent at the target
parameter. -/
theorem orthonormalDiagonalHamiltonianResolvent_taylor_tsum_eq_of_norm_sub_lt
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    {lambda mu : ℝ} (hlambda : lambda < delta)
    (hdist : ‖mu - lambda‖ < delta - lambda) :
    (∑' k : ℕ,
      ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
        iteratedDeriv k (orthonormalDiagonalHamiltonianResolvent b a) lambda) =
      orthonormalDiagonalHamiltonianResolvent b a mu :=
  (orthonormalDiagonalHamiltonianResolvent_taylor_hasSum_of_norm_sub_lt
    b a delta hdelta hlambda hdist).tsum_eq

/-- Finite exact-derivative Taylor partial sums converge in operator norm to the
target resolvent. -/
theorem orthonormalDiagonalHamiltonianResolvent_taylor_partialSum_tendsto_of_norm_sub_lt
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    {lambda mu : ℝ} (hlambda : lambda < delta)
    (hdist : ‖mu - lambda‖ < delta - lambda) :
    Tendsto
      (fun N : ℕ =>
        ∑ k ∈ Finset.range N,
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
            iteratedDeriv k (orthonormalDiagonalHamiltonianResolvent b a) lambda)
      atTop
      (𝓝 (orthonormalDiagonalHamiltonianResolvent b a mu)) :=
  (orthonormalDiagonalHamiltonianResolvent_taylor_hasSum_of_norm_sub_lt
    b a delta hdelta hlambda hdist).tendsto_sum_nat

/-- Exact ordered remainder identity for every derivative Taylor truncation. -/
theorem orthonormalDiagonalHamiltonianResolvent_sub_taylor_partialSum_eq
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    (N : ℕ) {lambda mu : ℝ} (hlambda : lambda < delta)
    (hdist : ‖mu - lambda‖ < delta - lambda) :
    orthonormalDiagonalHamiltonianResolvent b a mu -
        (∑ k ∈ Finset.range N,
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
            iteratedDeriv k (orthonormalDiagonalHamiltonianResolvent b a) lambda) =
      ((mu - lambda) •
        orthonormalDiagonalHamiltonianResolvent b a lambda) ^ N *
        orthonormalDiagonalHamiltonianResolvent b a mu := by
  rw [orthonormalDiagonalHamiltonianResolvent_taylor_partialSum_eq_neumann_partialSum
    b a delta hdelta N hlambda]
  exact orthonormalDiagonalHamiltonianResolvent_sub_neumann_partialSum_eq
    b a delta hdelta N hlambda hdist

/-- Explicit geometric operator-norm error for every derivative Taylor
truncation. -/
theorem orthonormalDiagonalHamiltonianResolvent_sub_taylor_partialSum_norm_le
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    (N : ℕ) {lambda mu : ℝ} (hlambda : lambda < delta)
    (hdist : ‖mu - lambda‖ < delta - lambda) :
    ‖orthonormalDiagonalHamiltonianResolvent b a mu -
        (∑ k ∈ Finset.range N,
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
            iteratedDeriv k (orthonormalDiagonalHamiltonianResolvent b a) lambda)‖ ≤
      (‖mu - lambda‖ * (delta - lambda)⁻¹) ^ N *
        (delta - mu)⁻¹ := by
  rw [orthonormalDiagonalHamiltonianResolvent_taylor_partialSum_eq_neumann_partialSum
    b a delta hdelta N hlambda]
  exact orthonormalDiagonalHamiltonianResolvent_sub_neumann_partialSum_norm_le_explicit
    b a delta hdelta N hlambda hdist

end MathlibAnalytic
end MGAP4D

end
