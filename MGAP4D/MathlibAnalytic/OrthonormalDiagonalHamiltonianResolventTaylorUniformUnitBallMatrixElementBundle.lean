import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianResolventTaylorStateMatrixElementBundle
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace LinearPMap ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 1600000

/-- On the two closed unit balls, every real matrix-element Taylor truncation
inherits the bare closed-subball geometric envelope, with no state-dependent
factor remaining. -/
theorem orthonormalDiagonalHamiltonianResolvent_taylor_matrixElement_error_abs_le_closedBall_unitBalls
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    {lambda r mu : ℝ} (hlambda : lambda < delta)
    (hr0 : 0 ≤ r) (hrlt : r < delta - lambda)
    (hmu : ‖mu - lambda‖ ≤ r) (N : ℕ) (x y : E)
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    |inner ℝ x
      ((orthonormalDiagonalHamiltonianResolvent b a mu -
        ∑ k ∈ Finset.range N,
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
            iteratedDeriv k
              (orthonormalDiagonalHamiltonianResolvent b a) lambda) y)| ≤
      (r * (delta - lambda)⁻¹) ^ N *
        (delta - lambda - r)⁻¹ := by
  have hbound :=
    orthonormalDiagonalHamiltonianResolvent_taylor_matrixElement_error_abs_le_closedBall
      b a delta hdelta hlambda hr0 hrlt hmu N x y
  have hgap0 : 0 ≤ delta - lambda :=
    le_of_lt (sub_pos.mpr hlambda)
  have hrest0 : 0 ≤ delta - lambda - r :=
    le_of_lt (sub_pos.mpr hrlt)
  have henv0 :
      0 ≤ (r * (delta - lambda)⁻¹) ^ N *
        (delta - lambda - r)⁻¹ :=
    mul_nonneg
      (pow_nonneg (mul_nonneg hr0 (inv_nonneg.mpr hgap0)) N)
      (inv_nonneg.mpr hrest0)
  calc
    |inner ℝ x
      ((orthonormalDiagonalHamiltonianResolvent b a mu -
        ∑ k ∈ Finset.range N,
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
            iteratedDeriv k
              (orthonormalDiagonalHamiltonianResolvent b a) lambda) y)| ≤
        ((r * (delta - lambda)⁻¹) ^ N *
          (delta - lambda - r)⁻¹) * ‖x‖ * ‖y‖ := hbound
    _ ≤ ((r * (delta - lambda)⁻¹) ^ N *
          (delta - lambda - r)⁻¹) * 1 * ‖y‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hx henv0) (norm_nonneg y)
    _ ≤ ((r * (delta - lambda)⁻¹) ^ N *
          (delta - lambda - r)⁻¹) * 1 * 1 :=
      mul_le_mul_of_nonneg_left hy (mul_nonneg henv0 zero_le_one)
    _ = (r * (delta - lambda)⁻¹) ^ N *
          (delta - lambda - r)⁻¹ := by ring

/-- A single eventual Taylor degree controls every spectral parameter in the
closed subgap ball and every pair of states in the two closed unit balls. -/
theorem orthonormalDiagonalHamiltonianResolvent_taylor_matrixElement_eventually_error_abs_lt_closedBall_unitBalls
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    {lambda r epsilon : ℝ} (hlambda : lambda < delta)
    (hr0 : 0 ≤ r) (hrlt : r < delta - lambda)
    (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop,
      ∀ mu : ℝ, ‖mu - lambda‖ ≤ r →
        ∀ x y : E, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
          |inner ℝ x
            ((orthonormalDiagonalHamiltonianResolvent b a mu -
              ∑ k ∈ Finset.range N,
                ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
                  iteratedDeriv k
                    (orthonormalDiagonalHamiltonianResolvent b a) lambda) y)| <
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
  intro mu hmu x y hx hy
  exact lt_of_le_of_lt
    (orthonormalDiagonalHamiltonianResolvent_taylor_matrixElement_error_abs_le_closedBall_unitBalls
      b a delta hdelta hlambda hr0 hrlt hmu N x y hx hy)
    hN

/-- Epsilon form of simultaneous unit-ball control: one truncation threshold
works for every later Taylor degree, every parameter in the closed subgap ball,
and every pair of unit-ball states. -/
theorem orthonormalDiagonalHamiltonianResolvent_taylor_matrixElement_exists_uniform_truncationOrder_closedBall_unitBalls
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    {lambda r epsilon : ℝ} (hlambda : lambda < delta)
    (hr0 : 0 ≤ r) (hrlt : r < delta - lambda)
    (hepsilon : 0 < epsilon) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ mu : ℝ, ‖mu - lambda‖ ≤ r →
        ∀ x y : E, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
          |inner ℝ x
            ((orthonormalDiagonalHamiltonianResolvent b a mu -
              ∑ k ∈ Finset.range N,
                ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
                  iteratedDeriv k
                    (orthonormalDiagonalHamiltonianResolvent b a) lambda) y)| <
            epsilon := by
  have hevent :=
    orthonormalDiagonalHamiltonianResolvent_taylor_matrixElement_eventually_error_abs_lt_closedBall_unitBalls
      b a delta hdelta hlambda hr0 hrlt hepsilon
  rcases (eventually_atTop.1 hevent) with ⟨N₀, hN₀⟩
  exact ⟨N₀, fun N hN => hN₀ N hN⟩

end MathlibAnalytic
end MGAP4D

end
