import MGAP4D.MathlibAnalytic.ComplexContinuousPositiveContractionRpowInverse
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Powers of a continuous complex-linear operator preserve an eigenvector and
raise its eigenvalue to the matching natural power. -/
theorem complexContinuousLinearMap_pow_apply_of_apply_eq_smul
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℂ E]
    (T : E →L[ℂ] E)
    (v : E)
    (z : ℂ)
    (hTv : T v = z • v)
    (m : ℕ) :
    (T ^ m) v = (z ^ m) • v := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ]
      change (T ^ m) (T v) = _
      rw [hTv, map_smul, ih]
      simp [pow_succ, smul_smul, mul_comm]

/-- The Banach-algebra exponential of a continuous complex-linear operator acts
on an eigenvector by the scalar complex exponential of the eigenvalue. -/
theorem normedSpace_exp_apply_of_complex_eigenvector
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℂ E]
    [CompleteSpace E]
    (T : E →L[ℂ] E)
    (v : E)
    (z : ℂ)
    (hTv : T v = z • v) :
    NormedSpace.exp T v = Complex.exp z • v := by
  have hTmem :
      T ∈ Metric.eball (0 : E →L[ℂ] E)
        (NormedSpace.expSeries ℂ (E →L[ℂ] E)).radius := by
    rw [NormedSpace.expSeries_radius_eq_top]
    exact edist_lt_top _ _
  have hTsum :
      HasSum
        (fun m : ℕ => ((Nat.factorial m : ℂ)⁻¹) • T ^ m)
        (NormedSpace.exp T) :=
    NormedSpace.expSeries_hasSum_exp_of_mem_ball' T hTmem
  have hTsum_apply :
      HasSum
        (fun m : ℕ => (((Nat.factorial m : ℂ)⁻¹) • T ^ m) v)
        (NormedSpace.exp T v) :=
    hTsum.map (fun S : E →L[ℂ] E => S v) (by fun_prop)
  have hzmem :
      z ∈ Metric.eball (0 : ℂ)
        (NormedSpace.expSeries ℂ ℂ).radius := by
    rw [NormedSpace.expSeries_radius_eq_top]
    exact edist_lt_top _ _
  have hzsum :
      HasSum
        (fun m : ℕ => ((Nat.factorial m : ℂ)⁻¹) * z ^ m)
        (NormedSpace.exp z) := by
    simpa [smul_eq_mul] using
      (NormedSpace.expSeries_hasSum_exp_of_mem_ball' z hzmem)
  have hzsum_smul :
      HasSum
        (fun m : ℕ => (((Nat.factorial m : ℂ)⁻¹) * z ^ m) • v)
        ((NormedSpace.exp z) • v) :=
    hzsum.smul_const v
  have hseries :
      NormedSpace.exp T v = (NormedSpace.exp z) • v := by
    apply HasSum.unique hTsum_apply
    simpa [complexContinuousLinearMap_pow_apply_of_apply_eq_smul T v z hTv,
      smul_smul] using hzsum_smul
  rw [Complex.exp_eq_exp_ℂ]
  exact hseries

end

end MathlibAnalytic
end MGAP4D
