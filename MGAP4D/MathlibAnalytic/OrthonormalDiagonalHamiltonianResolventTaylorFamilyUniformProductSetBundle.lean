import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianResolventTaylorUniformUnitBallMatrixElementBundle
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace LinearPMap ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 1600000

/-- A common spectral lower bound gives the same closed-ball unit-state Taylor
error envelope for every member of an orthonormal-diagonal Hamiltonian family. -/
theorem orthonormalDiagonalHamiltonianResolvent_taylor_matrixElement_error_abs_le_closedBall_unitBalls_family
    {J ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : J → OrthonormalBasis ι ℝ E) (a : J → ι → ℝ) (delta : ℝ)
    (hdelta : ∀ j : J, ∀ i : ι, delta ≤ a j i)
    {lambda r mu : ℝ} (hlambda : lambda < delta)
    (hr0 : 0 ≤ r) (hrlt : r < delta - lambda)
    (hmu : ‖mu - lambda‖ ≤ r) (N : ℕ) (j : J) (x y : E)
    (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    |inner ℝ x
      ((orthonormalDiagonalHamiltonianResolvent (b j) (a j) mu -
        ∑ k ∈ Finset.range N,
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
            iteratedDeriv k
              (orthonormalDiagonalHamiltonianResolvent (b j) (a j)) lambda) y)| ≤
      (r * (delta - lambda)⁻¹) ^ N *
        (delta - lambda - r)⁻¹ := by
  exact
    orthonormalDiagonalHamiltonianResolvent_taylor_matrixElement_error_abs_le_closedBall_unitBalls
      (b j) (a j) delta (hdelta j) hlambda hr0 hrlt hmu N x y hx hy

/-- One eventual Taylor degree controls every Hamiltonian in a common-gap
orthonormal-diagonal family, every parameter in the closed subgap ball, and
both closed state unit balls. -/
theorem orthonormalDiagonalHamiltonianResolvent_taylor_matrixElement_eventually_error_abs_lt_closedBall_unitBalls_family
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
        ∀ x y : E, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
          |inner ℝ x
            ((orthonormalDiagonalHamiltonianResolvent (b j) (a j) mu -
              ∑ k ∈ Finset.range N,
                ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
                  iteratedDeriv k
                    (orthonormalDiagonalHamiltonianResolvent (b j) (a j)) lambda) y)| <
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
  intro j mu hmu x y hx hy
  exact lt_of_le_of_lt
    (orthonormalDiagonalHamiltonianResolvent_taylor_matrixElement_error_abs_le_closedBall_unitBalls_family
      b a delta hdelta hlambda hr0 hrlt hmu N j x y hx hy)
    hN

/-- Epsilon threshold form of family-uniform Taylor control.  The same `N₀`
works for every later degree and every member of the common-gap family. -/
theorem orthonormalDiagonalHamiltonianResolvent_taylor_matrixElement_exists_uniform_truncationOrder_closedBall_unitBalls_family
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
        ∀ x y : E, ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
          |inner ℝ x
            ((orthonormalDiagonalHamiltonianResolvent (b j) (a j) mu -
              ∑ k ∈ Finset.range N,
                ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
                  iteratedDeriv k
                    (orthonormalDiagonalHamiltonianResolvent (b j) (a j)) lambda) y)| <
            epsilon := by
  have hevent :=
    orthonormalDiagonalHamiltonianResolvent_taylor_matrixElement_eventually_error_abs_lt_closedBall_unitBalls_family
      b a delta hdelta hlambda hr0 hrlt hepsilon
  rcases (eventually_atTop.1 hevent) with ⟨N₀, hN₀⟩
  exact ⟨N₀, fun N hN => hN₀ N hN⟩

/-- Taylor matrix elements converge uniformly on the full product of the family
index set, the closed spectral-parameter ball, and the two closed state unit
balls.  Thus the family index is controlled by the same Taylor degree as the
three analytic variables. -/
theorem orthonormalDiagonalHamiltonianResolvent_taylor_matrixElement_partialSum_tendstoUniformlyOn_family_closedBall_unitBalls
    {J ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : J → OrthonormalBasis ι ℝ E) (a : J → ι → ℝ) (delta : ℝ)
    (hdelta : ∀ j : J, ∀ i : ι, delta ≤ a j i)
    {lambda r : ℝ} (hlambda : lambda < delta)
    (hr0 : 0 ≤ r) (hrlt : r < delta - lambda) :
    TendstoUniformlyOn
      (fun N : ℕ => fun p : J × (ℝ × (E × E)) =>
        inner ℝ p.2.2.1
          ((∑ k ∈ Finset.range N,
            ((p.2.1 - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
              iteratedDeriv k
                (orthonormalDiagonalHamiltonianResolvent (b p.1) (a p.1)) lambda)
            p.2.2.2))
      (fun p : J × (ℝ × (E × E)) =>
        inner ℝ p.2.2.1
          (orthonormalDiagonalHamiltonianResolvent (b p.1) (a p.1)
            p.2.1 p.2.2.2))
      atTop
      ((Set.univ : Set J) ×ˢ
        (Metric.closedBall lambda r ×ˢ
          (Metric.closedBall (0 : E) 1 ×ˢ Metric.closedBall (0 : E) 1))) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hepsilon
  have hevent :=
    orthonormalDiagonalHamiltonianResolvent_taylor_matrixElement_eventually_error_abs_lt_closedBall_unitBalls_family
      b a delta hdelta hlambda hr0 hrlt hepsilon
  filter_upwards [hevent] with N hN
  intro p hp
  have hmu : ‖p.2.1 - lambda‖ ≤ r := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hp.2.1
  have hx : ‖p.2.2.1‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hp.2.2.1
  have hy : ‖p.2.2.2‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero] using hp.2.2.2
  have herr := hN p.1 p.2.1 hmu p.2.2.1 p.2.2.2 hx hy
  rw [Real.dist_eq]
  have hrewrite :
      inner ℝ p.2.2.1
          (orthonormalDiagonalHamiltonianResolvent (b p.1) (a p.1)
            p.2.1 p.2.2.2) -
        inner ℝ p.2.2.1
          ((∑ k ∈ Finset.range N,
            ((p.2.1 - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
              iteratedDeriv k
                (orthonormalDiagonalHamiltonianResolvent (b p.1) (a p.1)) lambda)
            p.2.2.2) =
      inner ℝ p.2.2.1
        ((orthonormalDiagonalHamiltonianResolvent (b p.1) (a p.1) p.2.1 -
          ∑ k ∈ Finset.range N,
            ((p.2.1 - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
              iteratedDeriv k
                (orthonormalDiagonalHamiltonianResolvent (b p.1) (a p.1)) lambda)
          p.2.2.2) := by
    simp [inner_sub_right]
  rw [hrewrite]
  exact herr

end MathlibAnalytic
end MGAP4D

end