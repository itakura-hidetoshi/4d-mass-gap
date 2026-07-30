import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianResolventTaylorSeriesBundle
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace LinearPMap ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 1600000

/-- Every point of a closed parameter ball whose radius is strictly smaller than
its center-to-gap distance remains below the spectral gap. -/
theorem resolventTaylorClosedBall_mem_Iio
    {delta lambda r mu : ℝ}
    (hrlt : r < delta - lambda) (hmu : ‖mu - lambda‖ ≤ r) :
    mu < delta := by
  have hstep : mu - lambda ≤ ‖mu - lambda‖ := by
    simpa only [Real.norm_eq_abs] using le_abs_self (mu - lambda)
  linarith

/-- The geometric Taylor-error envelope on a strict closed subball tends to
zero. -/
theorem resolventTaylorClosedBall_errorEnvelope_tendsto_zero
    {delta lambda r : ℝ} (hlambda : lambda < delta)
    (hr0 : 0 ≤ r) (hrlt : r < delta - lambda) :
    Tendsto
      (fun N : ℕ =>
        (r * (delta - lambda)⁻¹) ^ N * (delta - lambda - r)⁻¹)
      atTop (𝓝 0) := by
  have hbase : 0 < delta - lambda := sub_pos.mpr hlambda
  have hq0 : 0 ≤ r * (delta - lambda)⁻¹ :=
    mul_nonneg hr0 (inv_nonneg.mpr hbase.le)
  have hq1 : r * (delta - lambda)⁻¹ < 1 := by
    calc
      r * (delta - lambda)⁻¹ <
          (delta - lambda) * (delta - lambda)⁻¹ :=
        mul_lt_mul_of_pos_right hrlt (inv_pos.mpr hbase)
      _ = 1 := by simp [ne_of_gt hbase]
  have hpow :
      Tendsto (fun N : ℕ => (r * (delta - lambda)⁻¹) ^ N)
        atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  let C : ℝ := (delta - lambda - r)⁻¹
  have hmul :
      Tendsto
        (fun N : ℕ => C * (r * (delta - lambda)⁻¹) ^ N)
        atTop (𝓝 (C * 0)) :=
    tendsto_const_nhds.mul hpow
  simpa [C, mul_comm] using hmul

/-- On every strict closed subball, all exact-derivative Taylor truncation errors
obey one center-radius geometric envelope. -/
theorem orthonormalDiagonalHamiltonianResolvent_sub_taylor_partialSum_norm_le_closedBall
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    {lambda r mu : ℝ} (hlambda : lambda < delta)
    (hr0 : 0 ≤ r) (hrlt : r < delta - lambda)
    (hmu : ‖mu - lambda‖ ≤ r) (N : ℕ) :
    ‖orthonormalDiagonalHamiltonianResolvent b a mu -
        (∑ k ∈ Finset.range N,
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
            iteratedDeriv k
              (orthonormalDiagonalHamiltonianResolvent b a) lambda)‖ ≤
      (r * (delta - lambda)⁻¹) ^ N *
        (delta - lambda - r)⁻¹ := by
  have hdist : ‖mu - lambda‖ < delta - lambda :=
    lt_of_le_of_lt hmu hrlt
  have hpoint :=
    orthonormalDiagonalHamiltonianResolvent_sub_taylor_partialSum_norm_le
      b a delta hdelta N hlambda hdist
  have hbase : 0 < delta - lambda := sub_pos.mpr hlambda
  have hmargin : 0 < delta - lambda - r := by linarith
  have hmuLt : mu < delta :=
    resolventTaylorClosedBall_mem_Iio hrlt hmu
  have hstep : mu - lambda ≤ ‖mu - lambda‖ := by
    simpa only [Real.norm_eq_abs] using le_abs_self (mu - lambda)
  have hgap : delta - lambda - r ≤ delta - mu := by
    linarith
  have hinv : (delta - mu)⁻¹ ≤ (delta - lambda - r)⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le hmargin hgap
  have hratio :
      ‖mu - lambda‖ * (delta - lambda)⁻¹ ≤
        r * (delta - lambda)⁻¹ :=
    mul_le_mul_of_nonneg_right hmu (inv_nonneg.mpr hbase.le)
  have hratio0 :
      0 ≤ ‖mu - lambda‖ * (delta - lambda)⁻¹ :=
    mul_nonneg (norm_nonneg _) (inv_nonneg.mpr hbase.le)
  have hpow :
      (‖mu - lambda‖ * (delta - lambda)⁻¹) ^ N ≤
        (r * (delta - lambda)⁻¹) ^ N :=
    pow_le_pow_left₀ hratio0 hratio N
  calc
    ‖orthonormalDiagonalHamiltonianResolvent b a mu -
        (∑ k ∈ Finset.range N,
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
            iteratedDeriv k
              (orthonormalDiagonalHamiltonianResolvent b a) lambda)‖ ≤
        (‖mu - lambda‖ * (delta - lambda)⁻¹) ^ N *
          (delta - mu)⁻¹ := hpoint
    _ ≤ (r * (delta - lambda)⁻¹) ^ N * (delta - mu)⁻¹ :=
      mul_le_mul_of_nonneg_right hpow
        (inv_nonneg.mpr (sub_nonneg.mpr hmuLt.le))
    _ ≤ (r * (delta - lambda)⁻¹) ^ N *
          (delta - lambda - r)⁻¹ :=
      mul_le_mul_of_nonneg_left hinv
        (pow_nonneg
          (mul_nonneg hr0 (inv_nonneg.mpr hbase.le)) N)

/-- Exact-derivative Taylor partial sums converge uniformly in operator norm on
every closed ball strictly contained in the distance-to-gap ball. -/
theorem orthonormalDiagonalHamiltonianResolvent_taylor_partialSum_tendstoUniformlyOn_closedBall
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : OrthonormalBasis ι ℝ E) (a : ι → ℝ) (delta : ℝ)
    (hdelta : ∀ i : ι, delta ≤ a i)
    {lambda r : ℝ} (hlambda : lambda < delta)
    (hr0 : 0 ≤ r) (hrlt : r < delta - lambda) :
    TendstoUniformlyOn
      (fun N : ℕ => fun mu : ℝ =>
        ∑ k ∈ Finset.range N,
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
            iteratedDeriv k
              (orthonormalDiagonalHamiltonianResolvent b a) lambda)
      (orthonormalDiagonalHamiltonianResolvent b a)
      atTop (Metric.closedBall lambda r) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hepsilon
  have henv :=
    resolventTaylorClosedBall_errorEnvelope_tendsto_zero
      hlambda hr0 hrlt
  have hevent :
      ∀ᶠ N in atTop,
        (r * (delta - lambda)⁻¹) ^ N *
          (delta - lambda - r)⁻¹ < epsilon :=
    (tendsto_order.1 henv).2 epsilon hepsilon
  filter_upwards [hevent] with N hN
  intro mu hmu
  have hnorm : ‖mu - lambda‖ ≤ r := by
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hmu
  have hbound :=
    orthonormalDiagonalHamiltonianResolvent_sub_taylor_partialSum_norm_le_closedBall
      b a delta hdelta hlambda hr0 hrlt hnorm N
  simpa only [dist_eq_norm] using lt_of_le_of_lt hbound hN

end MathlibAnalytic
end MGAP4D

end