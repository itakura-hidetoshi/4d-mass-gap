import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianResolventTaylorUniformClosedBallBundle
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace LinearPMap ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 1600000

/-- The exact derivative Taylor series of the generic resolvent may be evaluated
termwise on every fixed state. -/
theorem orthonormalDiagonalHamiltonianResolvent_taylor_apply_hasSum_of_norm_sub_lt
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    {lambda mu : ℝ} (hlambda : lambda < delta)
    (hdist : ‖mu - lambda‖ < delta - lambda) (y : E) :
    HasSum
      (fun k : ℕ =>
        (((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
          iteratedDeriv k (orthonormalDiagonalHamiltonianResolvent b a) lambda) y)
      (orthonormalDiagonalHamiltonianResolvent b a mu y) := by
  let ev : (E →L[ℝ] E) →L[ℝ] E := (ContinuousLinearMap.apply ℝ E) y
  have hsum :=
    orthonormalDiagonalHamiltonianResolvent_taylor_hasSum_of_norm_sub_lt
      b a delta hdelta hlambda hdist
  simpa [ev] using hsum.map ev ev.continuous

/-- The pointwise Taylor `tsum` is exactly the resolvent applied to the fixed
state. -/
theorem orthonormalDiagonalHamiltonianResolvent_taylor_apply_tsum_eq_of_norm_sub_lt
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    {lambda mu : ℝ} (hlambda : lambda < delta)
    (hdist : ‖mu - lambda‖ < delta - lambda) (y : E) :
    (∑' k : ℕ,
      (((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
        iteratedDeriv k (orthonormalDiagonalHamiltonianResolvent b a) lambda) y) =
      orthonormalDiagonalHamiltonianResolvent b a mu y :=
  (orthonormalDiagonalHamiltonianResolvent_taylor_apply_hasSum_of_norm_sub_lt
    b a delta hdelta hlambda hdist y).tsum_eq

/-- Every fixed-state Taylor truncation inherits the exact closed-subball
geometric error envelope, multiplied only by the state norm. -/
theorem orthonormalDiagonalHamiltonianResolvent_taylor_apply_error_norm_le_closedBall
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    {lambda r mu : ℝ} (hlambda : lambda < delta)
    (hr0 : 0 ≤ r) (hrlt : r < delta - lambda)
    (hmu : ‖mu - lambda‖ ≤ r) (N : ℕ) (y : E) :
    ‖(orthonormalDiagonalHamiltonianResolvent b a mu -
        ∑ k ∈ Finset.range N,
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
            iteratedDeriv k
              (orthonormalDiagonalHamiltonianResolvent b a) lambda) y‖ ≤
      ((r * (delta - lambda)⁻¹) ^ N *
        (delta - lambda - r)⁻¹) * ‖y‖ := by
  have hop :=
    orthonormalDiagonalHamiltonianResolvent_sub_taylor_partialSum_norm_le_closedBall
      b a delta hdelta hlambda hr0 hrlt hmu N
  exact le_trans
    ((orthonormalDiagonalHamiltonianResolvent b a mu -
      ∑ k ∈ Finset.range N,
        ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
          iteratedDeriv k
            (orthonormalDiagonalHamiltonianResolvent b a) lambda).le_opNorm y)
    (mul_le_mul_of_nonneg_right hop (norm_nonneg y))

/-- Fixed-state Taylor partial sums converge uniformly on every strict closed
subgap ball. -/
theorem orthonormalDiagonalHamiltonianResolvent_taylor_apply_partialSum_tendstoUniformlyOn_closedBall
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    {lambda r : ℝ} (hlambda : lambda < delta)
    (hr0 : 0 ≤ r) (hrlt : r < delta - lambda) (y : E) :
    TendstoUniformlyOn
      (fun N : ℕ => fun mu : ℝ =>
        (∑ k ∈ Finset.range N,
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
            iteratedDeriv k
              (orthonormalDiagonalHamiltonianResolvent b a) lambda) y)
      (fun mu : ℝ => orthonormalDiagonalHamiltonianResolvent b a mu y)
      atTop (Metric.closedBall lambda r) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hepsilon
  have henv :=
    resolventTaylorClosedBall_errorEnvelope_tendsto_zero
      hlambda hr0 hrlt
  let C : ℝ := ‖y‖
  have hscaled :
      Tendsto
        (fun N : ℕ =>
          ((r * (delta - lambda)⁻¹) ^ N *
            (delta - lambda - r)⁻¹) * C)
        atTop (𝓝 0) := by
    have hmul := henv.mul (tendsto_const_nhds : Tendsto (fun _ : ℕ => C) atTop (𝓝 C))
    simpa [C] using hmul
  have hevent :
      ∀ᶠ N in atTop,
        ((r * (delta - lambda)⁻¹) ^ N *
          (delta - lambda - r)⁻¹) * ‖y‖ < epsilon :=
    (tendsto_order.1 hscaled).2 epsilon hepsilon
  filter_upwards [hevent] with N hN
  intro mu hmu
  have hnorm : ‖mu - lambda‖ ≤ r := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hmu
  have hbound :=
    orthonormalDiagonalHamiltonianResolvent_taylor_apply_error_norm_le_closedBall
      b a delta hdelta hlambda hr0 hrlt hnorm N y
  simpa only [dist_eq_norm, sub_apply] using lt_of_le_of_lt hbound hN

/-- Every fixed real matrix element of the exact derivative Taylor series may be
summed termwise. -/
theorem orthonormalDiagonalHamiltonianResolvent_taylor_matrixElement_hasSum_of_norm_sub_lt
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    {lambda mu : ℝ} (hlambda : lambda < delta)
    (hdist : ‖mu - lambda‖ < delta - lambda) (x y : E) :
    HasSum
      (fun k : ℕ => inner ℝ x
        ((((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
          iteratedDeriv k
            (orthonormalDiagonalHamiltonianResolvent b a) lambda) y))
      (inner ℝ x (orthonormalDiagonalHamiltonianResolvent b a mu y)) := by
  let ix : E →L[ℝ] ℝ := innerSL ℝ x
  have hsum :=
    orthonormalDiagonalHamiltonianResolvent_taylor_apply_hasSum_of_norm_sub_lt
      b a delta hdelta hlambda hdist y
  simpa [ix] using hsum.map ix ix.continuous

/-- The scalar matrix-element Taylor `tsum` is exactly the corresponding
resolvent matrix element. -/
theorem orthonormalDiagonalHamiltonianResolvent_taylor_matrixElement_tsum_eq_of_norm_sub_lt
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    {lambda mu : ℝ} (hlambda : lambda < delta)
    (hdist : ‖mu - lambda‖ < delta - lambda) (x y : E) :
    (∑' k : ℕ, inner ℝ x
      ((((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
        iteratedDeriv k
          (orthonormalDiagonalHamiltonianResolvent b a) lambda) y)) =
      inner ℝ x (orthonormalDiagonalHamiltonianResolvent b a mu y) :=
  (orthonormalDiagonalHamiltonianResolvent_taylor_matrixElement_hasSum_of_norm_sub_lt
    b a delta hdelta hlambda hdist x y).tsum_eq

/-- Every scalar matrix-element Taylor truncation inherits the same closed-ball
geometric envelope, multiplied by the two state norms. -/
theorem orthonormalDiagonalHamiltonianResolvent_taylor_matrixElement_error_abs_le_closedBall
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    {lambda r mu : ℝ} (hlambda : lambda < delta)
    (hr0 : 0 ≤ r) (hrlt : r < delta - lambda)
    (hmu : ‖mu - lambda‖ ≤ r) (N : ℕ) (x y : E) :
    |inner ℝ x
      ((orthonormalDiagonalHamiltonianResolvent b a mu -
        ∑ k ∈ Finset.range N,
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
            iteratedDeriv k
              (orthonormalDiagonalHamiltonianResolvent b a) lambda) y)| ≤
      ((r * (delta - lambda)⁻¹) ^ N *
        (delta - lambda - r)⁻¹) * ‖x‖ * ‖y‖ := by
  have happ :=
    orthonormalDiagonalHamiltonianResolvent_taylor_apply_error_norm_le_closedBall
      b a delta hdelta hlambda hr0 hrlt hmu N y
  calc
    |inner ℝ x
      ((orthonormalDiagonalHamiltonianResolvent b a mu -
        ∑ k ∈ Finset.range N,
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
            iteratedDeriv k
              (orthonormalDiagonalHamiltonianResolvent b a) lambda) y)| ≤
        ‖x‖ *
          ‖(orthonormalDiagonalHamiltonianResolvent b a mu -
            ∑ k ∈ Finset.range N,
              ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
                iteratedDeriv k
                  (orthonormalDiagonalHamiltonianResolvent b a) lambda) y‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ ‖x‖ *
        (((r * (delta - lambda)⁻¹) ^ N *
          (delta - lambda - r)⁻¹) * ‖y‖) :=
      mul_le_mul_of_nonneg_left happ (norm_nonneg x)
    _ = ((r * (delta - lambda)⁻¹) ^ N *
        (delta - lambda - r)⁻¹) * ‖x‖ * ‖y‖ := by ring

/-- Every fixed scalar matrix-element Taylor series converges uniformly on each
strict closed subgap ball. -/
theorem orthonormalDiagonalHamiltonianResolvent_taylor_matrixElement_partialSum_tendstoUniformlyOn_closedBall
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    {lambda r : ℝ} (hlambda : lambda < delta)
    (hr0 : 0 ≤ r) (hrlt : r < delta - lambda) (x y : E) :
    TendstoUniformlyOn
      (fun N : ℕ => fun mu : ℝ => inner ℝ x
        ((∑ k ∈ Finset.range N,
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
            iteratedDeriv k
              (orthonormalDiagonalHamiltonianResolvent b a) lambda) y))
      (fun mu : ℝ => inner ℝ x
        (orthonormalDiagonalHamiltonianResolvent b a mu y))
      atTop (Metric.closedBall lambda r) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hepsilon
  have henv :=
    resolventTaylorClosedBall_errorEnvelope_tendsto_zero
      hlambda hr0 hrlt
  let C : ℝ := ‖x‖ * ‖y‖
  have hscaled :
      Tendsto
        (fun N : ℕ =>
          ((r * (delta - lambda)⁻¹) ^ N *
            (delta - lambda - r)⁻¹) * C)
        atTop (𝓝 0) := by
    have hmul := henv.mul (tendsto_const_nhds : Tendsto (fun _ : ℕ => C) atTop (𝓝 C))
    simpa [C, mul_assoc] using hmul
  have hevent :
      ∀ᶠ N in atTop,
        ((r * (delta - lambda)⁻¹) ^ N *
          (delta - lambda - r)⁻¹) * ‖x‖ * ‖y‖ < epsilon := by
    simpa [C, mul_assoc] using (tendsto_order.1 hscaled).2 epsilon hepsilon
  filter_upwards [hevent] with N hN
  intro mu hmu
  have hnorm : ‖mu - lambda‖ ≤ r := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hmu
  have hbound :=
    orthonormalDiagonalHamiltonianResolvent_taylor_matrixElement_error_abs_le_closedBall
      b a delta hdelta hlambda hr0 hrlt hnorm N x y
  rw [Real.dist_eq]
  have hrewrite :
      inner ℝ x (orthonormalDiagonalHamiltonianResolvent b a mu y) -
          inner ℝ x
            ((∑ k ∈ Finset.range N,
              ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
                iteratedDeriv k
                  (orthonormalDiagonalHamiltonianResolvent b a) lambda) y) =
        inner ℝ x
          ((orthonormalDiagonalHamiltonianResolvent b a mu -
            ∑ k ∈ Finset.range N,
              ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
                iteratedDeriv k
                  (orthonormalDiagonalHamiltonianResolvent b a) lambda) y) := by
    simp [inner_sub_right]
  rw [hrewrite]
  exact lt_of_le_of_lt hbound hN

end MathlibAnalytic
end MGAP4D

end
