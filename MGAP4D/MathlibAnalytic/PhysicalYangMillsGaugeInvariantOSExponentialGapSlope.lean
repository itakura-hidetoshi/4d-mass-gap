import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Tactic

noncomputable section

open Filter Set Topology

namespace MGAP4D
namespace MathlibAnalytic

/-- The positive right-time difference quotient of exponential decay has slope
`mass` at the origin.

This removes an abstract small-time limit from finite-volume OS gap packages
whenever the decay factor is the concrete exponential `exp (-mass * t)`. -/
theorem tendsto_nnreal_inv_mul_one_sub_exp_neg_mul
    (mass : ℝ) :
    Tendsto
      (fun t : NNReal =>
        (t : ℝ)⁻¹ * (1 - Real.exp (-mass * (t : ℝ))))
      (nhdsWithin 0 (Ioi 0))
      (nhds mass) := by
  have hexp :
      HasDerivAt (fun x : ℝ => Real.exp (-mass * x)) (-mass) 0 := by
    simpa using
      ((hasDerivAt_const_mul (x := (0 : ℝ)) (-mass)).exp)
  have hderiv :
      HasDerivAt (fun x : ℝ => 1 - Real.exp (-mass * x)) mass 0 := by
    simpa using
      ((hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).sub hexp)
  have hreal :
      Tendsto
        (fun t : ℝ =>
          t⁻¹ * (1 - Real.exp (-mass * t)))
        (nhdsWithin 0 (Ioi 0))
        (nhds mass) := by
    simpa [smul_eq_mul] using hderiv.tendsto_slope_zero_right
  have hcoe :
      Tendsto
        (fun t : NNReal => (t : ℝ))
        (nhdsWithin 0 (Ioi 0))
        (nhdsWithin 0 (Ioi 0)) := by
    exact (NNReal.map_coe_nhdsGT (0 : NNReal)).le
  exact hreal.comp hcoe

/-- The square root of the double-time exponential decay is the one-time
exponential decay. -/
theorem sqrt_exp_neg_mul_double_nnreal
    (mass : ℝ) (t : NNReal) :
    Real.sqrt
        (Real.exp (-mass * (((t + t : NNReal) : ℝ)))) =
      Real.exp (-mass * (t : ℝ)) := by
  have harg :
      -mass * (((t + t : NNReal) : ℝ)) =
        (-mass * (t : ℝ)) + (-mass * (t : ℝ)) := by
    push_cast
    ring
  rw [harg, Real.exp_add, ← pow_two, Real.sqrt_sq_eq_abs,
    abs_of_pos (Real.exp_pos _)]

/-- For the concrete quadratic decay factor `q(t) = exp (-mass * t)`, the exact
square-root double-time slope required by the Wilson OS continuum transfer is
`mass`. -/
theorem exponential_quadraticDecayFactor_slope_tendsto
    (mass : ℝ) :
    Tendsto
      (fun t : NNReal =>
        (t : ℝ)⁻¹ *
          (1 - Real.sqrt
            (Real.exp (-mass * (((t + t : NNReal) : ℝ))))))
      (nhdsWithin 0 (Ioi 0))
      (nhds mass) := by
  convert tendsto_nnreal_inv_mul_one_sub_exp_neg_mul mass using 1
  funext t
  rw [sqrt_exp_neg_mul_double_nnreal]

/-- Exponential decay is nonnegative at every nonnegative Euclidean time. -/
theorem exponential_quadraticDecayFactor_nonneg
    (mass : ℝ) (t : NNReal) :
    0 ≤ Real.exp (-mass * (t : ℝ)) :=
  (Real.exp_pos _).le

/-- The Poincaré defect associated with exponential decay lies in `[0,1]` for a
nonnegative mass. -/
theorem exponential_defect_nonneg
    {mass : ℝ} (hmass : 0 ≤ mass) (t : NNReal) :
    0 ≤ 1 - Real.exp (-mass * (t : ℝ)) := by
  rw [sub_nonneg]
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr hmass) t.property)

/-- The exponential Poincaré defect is at most one. -/
theorem exponential_defect_le_one
    (mass : ℝ) (t : NNReal) :
    1 - Real.exp (-mass * (t : ℝ)) ≤ 1 := by
  linarith [Real.exp_pos (-mass * (t : ℝ))]

end MathlibAnalytic
end MGAP4D

end
