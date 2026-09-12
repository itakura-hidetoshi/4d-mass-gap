import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Powers of a continuous real-linear operator preserve an eigenvector and
raise its eigenvalue to the matching natural power. -/
theorem realContinuousLinearMap_pow_apply_of_apply_eq_smul
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (T : E →L[ℝ] E)
    (v : E)
    (r : ℝ)
    (hTv : T v = r • v)
    (m : ℕ) :
    (T ^ m) v = (r ^ m) • v := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ]
      change (T ^ m) (T v) = _
      rw [hTv, map_smul, ih]
      simp [pow_succ, smul_smul, mul_comm]

set_option maxHeartbeats 1000000 in
/-- The Banach-algebra exponential of a continuous real-linear operator acts
on a real eigenvector by the scalar real exponential of the eigenvalue. -/
theorem normedSpace_exp_apply_of_real_eigenvector
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    [CompleteSpace E]
    (T : E →L[ℝ] E)
    (v : E)
    (r : ℝ)
    (hTv : T v = r • v) :
    NormedSpace.exp T v = Real.exp r • v := by
  have hTmem :
      T ∈ Metric.eball (0 : E →L[ℝ] E)
        (NormedSpace.expSeries ℝ (E →L[ℝ] E)).radius := by
    rw [NormedSpace.expSeries_radius_eq_top]
    exact edist_lt_top _ _
  have hTsum :
      HasSum
        (fun m : ℕ => ((Nat.factorial m : ℝ)⁻¹) • T ^ m)
        (NormedSpace.exp T) :=
    NormedSpace.expSeries_hasSum_exp_of_mem_ball' T hTmem
  have hTsum_apply :
      HasSum
        (fun m : ℕ => (((Nat.factorial m : ℝ)⁻¹) • T ^ m) v)
        (NormedSpace.exp T v) :=
    (ContinuousLinearMap.apply ℝ E v).hasSum hTsum
  have hrmem :
      r ∈ Metric.eball (0 : ℝ)
        (NormedSpace.expSeries ℝ ℝ).radius := by
    rw [NormedSpace.expSeries_radius_eq_top]
    exact edist_lt_top _ _
  have hrsum :
      HasSum
        (fun m : ℕ => ((Nat.factorial m : ℝ)⁻¹) * r ^ m)
        (NormedSpace.exp r) := by
    simpa [smul_eq_mul] using
      (NormedSpace.expSeries_hasSum_exp_of_mem_ball' r hrmem)
  have hrsum_smul :
      HasSum
        (fun m : ℕ => (((Nat.factorial m : ℝ)⁻¹) * r ^ m) • v)
        ((NormedSpace.exp r) • v) :=
    hrsum.smul_const v
  have hterms :
      (fun m : ℕ => (((Nat.factorial m : ℝ)⁻¹) * r ^ m) • v) =
        (fun m : ℕ => (((Nat.factorial m : ℝ)⁻¹) • T ^ m) v) := by
    funext m
    rw [ContinuousLinearMap.smul_apply,
      realContinuousLinearMap_pow_apply_of_apply_eq_smul T v r hTv]
    simp [smul_smul]
  have hseries :
      NormedSpace.exp T v = (NormedSpace.exp r) • v := by
    apply HasSum.unique hTsum_apply
    rw [← hterms]
    exact hrsum_smul
  rw [Real.exp_eq_exp_ℝ]
  exact hseries

end

end MathlibAnalytic
end MGAP4D
