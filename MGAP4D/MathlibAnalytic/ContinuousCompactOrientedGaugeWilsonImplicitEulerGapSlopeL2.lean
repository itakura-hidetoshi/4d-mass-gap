import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonUniformDobrushinResolventNormL2
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Instances.NNReal.Lemmas

namespace MGAP4D
namespace MathlibAnalytic

open Filter Set Topology

noncomputable section

/-- The implicit-Euler decay factor associated with a positive mass. -/
def implicitEulerGapDecayFactor (mass : ℝ) (t : NNReal) : ℝ :=
  (1 + mass * (t : ℝ))⁻¹

/-- The positive right-time difference quotient of the implicit-Euler decay
factor has slope `mass` at the origin. -/
theorem tendsto_nnreal_inv_mul_one_sub_implicitEulerGapDecayFactor
    (mass : ℝ) :
    Tendsto
      (fun t : NNReal =>
        (t : ℝ)⁻¹ * (1 - implicitEulerGapDecayFactor mass t))
      (nhdsWithin 0 (Ioi 0))
      (nhds mass) := by
  have hden :
      HasDerivAt (fun x : ℝ => 1 + mass * x) mass 0 := by
    convert
      ((hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).add
        (hasDerivAt_const_mul (x := (0 : ℝ)) mass)) using 1 <;>
      norm_num
  have hinv :
      HasDerivAt (fun x : ℝ => (1 + mass * x)⁻¹) (-mass) 0 := by
    simpa using hden.inv (by norm_num)
  have hderiv :
      HasDerivAt (fun x : ℝ => 1 - (1 + mass * x)⁻¹) mass 0 := by
    simpa using
      ((hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).sub hinv)
  have hreal :
      Tendsto
        (fun t : ℝ => t⁻¹ * (1 - (1 + mass * t)⁻¹))
        (nhdsWithin 0 (Ioi 0))
        (nhds mass) := by
    simpa [smul_eq_mul] using hderiv.tendsto_slope_zero_right
  have hcoe :
      Tendsto
        (fun t : NNReal => (t : ℝ))
        (nhdsWithin 0 (Ioi 0))
        (nhdsWithin 0 (Ioi 0)) := by
    exact (NNReal.map_coe_nhdsGT (0 : NNReal)).le
  simpa [implicitEulerGapDecayFactor] using hreal.comp hcoe

/-- The implicit-Euler decay factor is nonnegative for nonnegative mass and
nonnegative time. -/
theorem implicitEulerGapDecayFactor_nonneg
    {mass : ℝ} (hmass : 0 ≤ mass) (t : NNReal) :
    0 ≤ implicitEulerGapDecayFactor mass t := by
  unfold implicitEulerGapDecayFactor
  apply inv_nonneg.mpr
  exact add_nonneg zero_le_one (mul_nonneg hmass t.property)

/-- The implicit-Euler decay factor is at most one for nonnegative mass. -/
theorem implicitEulerGapDecayFactor_le_one
    {mass : ℝ} (hmass : 0 ≤ mass) (t : NNReal) :
    implicitEulerGapDecayFactor mass t ≤ 1 := by
  unfold implicitEulerGapDecayFactor
  have hden : 1 ≤ 1 + mass * (t : ℝ) :=
    le_add_of_nonneg_right (mul_nonneg hmass t.property)
  have hdenPos : 0 < 1 + mass * (t : ℝ) :=
    zero_lt_one.trans_le hden
  exact (inv_le_one₀ hdenPos).2 hden

/-- The uniform compact Wilson Dobrushin gap has the canonical implicit-Euler
small-time slope. -/
theorem continuous_compact_oriented_uniformDobrushin_implicitEuler_slope
    {ι : Type*}
    (U : ContinuousCompactOrientedGaugeWilsonUniformDobrushinFamilyData ι) :
    Tendsto
      (fun t : NNReal =>
        (t : ℝ)⁻¹ *
          (1 - implicitEulerGapDecayFactor
            (continuousCompactOrientedUniformDobrushinGap U) t))
      (nhdsWithin 0 (Ioi 0))
      (nhds (continuousCompactOrientedUniformDobrushinGap U)) :=
  tendsto_nnreal_inv_mul_one_sub_implicitEulerGapDecayFactor
    (continuousCompactOrientedUniformDobrushinGap U)

end

end MathlibAnalytic
end MGAP4D
