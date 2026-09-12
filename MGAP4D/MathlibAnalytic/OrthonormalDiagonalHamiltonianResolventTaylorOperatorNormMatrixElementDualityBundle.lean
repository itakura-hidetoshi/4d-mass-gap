import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianResolventTaylorFamilyUniformProductSetBundle
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace LinearPMap ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 1600000

/-- On a real Hilbert space, an operator-norm upper bound is exactly the same as
an upper bound for every real matrix element on the two closed unit balls. -/
theorem continuousLinearMap_norm_le_iff_real_matrixElement_le_unitBalls
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E) {C : ℝ} (hC : 0 ≤ C) :
    ‖T‖ ≤ C ↔
      ∀ x y : E, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
        |inner ℝ x (T y)| ≤ C := by
  constructor
  · intro hT x y hx hy
    calc
      |inner ℝ x (T y)| ≤ ‖x‖ * ‖T y‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ ‖x‖ * (‖T‖ * ‖y‖) :=
        mul_le_mul_of_nonneg_left (T.le_opNorm y) (norm_nonneg x)
      _ ≤ 1 * (‖T‖ * ‖y‖) :=
        mul_le_mul_of_nonneg_right hx
          (mul_nonneg (norm_nonneg T) (norm_nonneg y))
      _ ≤ 1 * (C * ‖y‖) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hT (norm_nonneg y)) zero_le_one
      _ ≤ 1 * (C * 1) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hy hC) zero_le_one
      _ = C := by ring
  · intro h
    apply ContinuousLinearMap.opNorm_le_of_re_inner_le hC
    intro y x hy hx
    have hbound := h x y (le_of_eq hx) (le_of_eq hy)
    have hle : inner ℝ x (T y) ≤ C :=
      le_trans (le_abs_self (inner ℝ x (T y))) hbound
    simpa [real_inner_comm] using hle

/-- The operator norm is the least nonnegative constant controlling every real
matrix element on the two closed unit balls. -/
theorem continuousLinearMap_norm_is_least_real_matrixElement_unitBall_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E) :
    (∀ x y : E, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
        |inner ℝ x (T y)| ≤ ‖T‖) ∧
      ∀ C : ℝ, 0 ≤ C →
        (∀ x y : E, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
          |inner ℝ x (T y)| ≤ C) →
        ‖T‖ ≤ C := by
  constructor
  · exact
      (continuousLinearMap_norm_le_iff_real_matrixElement_le_unitBalls
        T (norm_nonneg T)).1 le_rfl
  · intro C hC h
    exact
      (continuousLinearMap_norm_le_iff_real_matrixElement_le_unitBalls
        T hC).2 h

/-- For every orthonormal-diagonal resolvent Taylor remainder, an operator-norm
bound and the corresponding two-unit-ball matrix-element bound are equivalent. -/
theorem orthonormalDiagonalHamiltonianResolvent_sub_taylor_partialSum_norm_le_iff_matrixElement_le_unitBalls
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ)
    {lambda mu C : ℝ} (N : ℕ) (hC : 0 ≤ C) :
    ‖orthonormalDiagonalHamiltonianResolvent b a mu -
        (∑ k ∈ Finset.range N,
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
            iteratedDeriv k
              (orthonormalDiagonalHamiltonianResolvent b a) lambda)‖ ≤ C ↔
      ∀ x y : E, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
        |inner ℝ x
          ((orthonormalDiagonalHamiltonianResolvent b a mu -
            ∑ k ∈ Finset.range N,
              ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
                iteratedDeriv k
                  (orthonormalDiagonalHamiltonianResolvent b a) lambda) y)| ≤ C := by
  exact continuousLinearMap_norm_le_iff_real_matrixElement_le_unitBalls _ hC

/-- A common spectral lower bound gives one operator-norm Taylor error envelope
for every member of an orthonormal-diagonal Hamiltonian family. -/
theorem orthonormalDiagonalHamiltonianResolvent_sub_taylor_partialSum_norm_le_closedBall_family
    {J ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : J → OrthonormalBasis ι ℝ E) (a : J → ι → ℝ) (delta : ℝ)
    (hdelta : ∀ j : J, ∀ i : ι, delta ≤ a j i)
    {lambda r mu : ℝ} (hlambda : lambda < delta)
    (hr0 : 0 ≤ r) (hrlt : r < delta - lambda)
    (hmu : ‖mu - lambda‖ ≤ r) (N : ℕ) (j : J) :
    ‖orthonormalDiagonalHamiltonianResolvent (b j) (a j) mu -
        (∑ k ∈ Finset.range N,
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
            iteratedDeriv k
              (orthonormalDiagonalHamiltonianResolvent (b j) (a j)) lambda)‖ ≤
      (r * (delta - lambda)⁻¹) ^ N *
        (delta - lambda - r)⁻¹ := by
  exact
    orthonormalDiagonalHamiltonianResolvent_sub_taylor_partialSum_norm_le_closedBall
      (b j) (a j) delta (hdelta j) hlambda hr0 hrlt hmu N

/-- One eventual Taylor degree controls the operator-norm remainder for every
member of a common-gap orthonormal-diagonal family and every parameter in the
closed subgap ball. -/
theorem orthonormalDiagonalHamiltonianResolvent_taylor_eventually_operatorNorm_error_lt_closedBall_family
    {J ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : J → OrthonormalBasis ι ℝ E) (a : J → ι → ℝ) (delta : ℝ)
    (hdelta : ∀ j : J, ∀ i : ι, delta ≤ a j i)
    {lambda r epsilon : ℝ} (hlambda : lambda < delta)
    (hr0 : 0 ≤ r) (hrlt : r < delta - lambda)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop,
      ∀ j : J, ∀ mu : ℝ, ‖mu - lambda‖ ≤ r →
        ‖orthonormalDiagonalHamiltonianResolvent (b j) (a j) mu -
          (∑ k ∈ Finset.range N,
            ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
              iteratedDeriv k
                (orthonormalDiagonalHamiltonianResolvent (b j) (a j)) lambda)‖ <
          epsilon := by
  have henv :=
    resolventTaylorClosedBall_errorEnvelope_tendsto_zero
      hlambda hr0 hrlt
  have hevent :
      ∀ᶠ N : ℕ in atTop,
        (r * (delta - lambda)⁻¹) ^ N *
          (delta - lambda - r)⁻¹ < epsilon :=
    (tendsto_order.1 henv).2 epsilon hepsilon
  filter_upwards [hevent] with N hN
  intro j mu hmu
  exact lt_of_le_of_lt
    (orthonormalDiagonalHamiltonianResolvent_sub_taylor_partialSum_norm_le_closedBall_family
      b a delta hdelta hlambda hr0 hrlt hmu N j)
    hN

/-- Epsilon-threshold form of family-uniform operator-norm Taylor control. -/
theorem orthonormalDiagonalHamiltonianResolvent_taylor_exists_uniform_operatorNorm_truncationOrder_closedBall_family
    {J ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : J → OrthonormalBasis ι ℝ E) (a : J → ι → ℝ) (delta : ℝ)
    (hdelta : ∀ j : J, ∀ i : ι, delta ≤ a j i)
    {lambda r epsilon : ℝ} (hlambda : lambda < delta)
    (hr0 : 0 ≤ r) (hrlt : r < delta - lambda)
    (hepsilon : 0 < epsilon) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ j : J, ∀ mu : ℝ, ‖mu - lambda‖ ≤ r →
        ‖orthonormalDiagonalHamiltonianResolvent (b j) (a j) mu -
          (∑ k ∈ Finset.range N,
            ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
              iteratedDeriv k
                (orthonormalDiagonalHamiltonianResolvent (b j) (a j)) lambda)‖ <
          epsilon := by
  have hevent :=
    orthonormalDiagonalHamiltonianResolvent_taylor_eventually_operatorNorm_error_lt_closedBall_family
      b a delta hdelta hlambda hr0 hrlt hepsilon
  rcases (eventually_atTop.1 hevent) with ⟨N₀, hN₀⟩
  exact ⟨N₀, fun N hN => hN₀ N hN⟩

/-- Exact-derivative Taylor partial sums converge uniformly in operator norm on
the product of the full family index set and the closed spectral-parameter ball. -/
theorem orthonormalDiagonalHamiltonianResolvent_taylor_partialSum_tendstoUniformlyOn_operatorNorm_family_closedBall
    {J ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : J → OrthonormalBasis ι ℝ E) (a : J → ι → ℝ) (delta : ℝ)
    (hdelta : ∀ j : J, ∀ i : ι, delta ≤ a j i)
    {lambda r : ℝ} (hlambda : lambda < delta)
    (hr0 : 0 ≤ r) (hrlt : r < delta - lambda) :
    TendstoUniformlyOn
      (fun N : ℕ => fun p : J × ℝ =>
        ∑ k ∈ Finset.range N,
          ((p.2 - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
            iteratedDeriv k
              (orthonormalDiagonalHamiltonianResolvent (b p.1) (a p.1)) lambda)
      (fun p : J × ℝ =>
        orthonormalDiagonalHamiltonianResolvent (b p.1) (a p.1) p.2)
      atTop
      ((Set.univ : Set J) ×ˢ Metric.closedBall lambda r) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hepsilon
  have hevent :=
    orthonormalDiagonalHamiltonianResolvent_taylor_eventually_operatorNorm_error_lt_closedBall_family
      b a delta hdelta hlambda hr0 hrlt hepsilon
  filter_upwards [hevent] with N hN
  intro p hp
  have hmu : ‖p.2 - lambda‖ ≤ r := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hp.2
  have herr := hN p.1 p.2 hmu
  simpa only [dist_eq_norm] using herr

end MathlibAnalytic
end MGAP4D

end
