import MGAP4D.MathlibAnalytic.CompactPositiveMomentTail

/-!
# P4-Q2-PZ37ACO — genuine mean-adjusted signal/residual ratio

On a compact probability space, let U = integral u > 0 and V = integral v >= 0,
with v >= 0 pointwise, continuous u,v, and a proved finite upper cap u <= R.
For every epsilon > 0, the ACTUAL mean-adjusted margin
  Q_epsilon(x) = (V+epsilon)*u(x) - U*v(x)
has exact mean epsilon*U > 0 and obeys Q_epsilon <= (V+epsilon)*R.
Consequently its strict upper tail has an explicit positive original-mass floor.

No assumption v/u <= some target ratio, independence, atom-freeness,
quantitative variance, or uniformity is inserted.
-/

namespace MGAP4D.MathlibAnalytic.CompactPositiveMeanRelativeResidual

open MeasureTheory
open scoped Topology
noncomputable section
set_option autoImplicit false

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
  [CompactSpace α] [BorelSpace α]
  (μ : Measure α) [IsProbabilityMeasure μ]

/-- Actual, epsilon-relaxed comparison between a signal and nonnegative residual. -/
def adjustedMargin (u v : α → ℝ) (epsilon : ℝ) (x : α) : ℝ :=
  ((∫ y : α, v y ∂μ) + epsilon) * u x - (∫ y : α, u y ∂μ) * v x

omit [CompactSpace α] [BorelSpace α] [IsProbabilityMeasure μ] in
/-- The margin is continuous in the unchanged compact probability space. -/
theorem adjustedMargin_continuous (u v : α → ℝ)
    (hu : Continuous u) (hv : Continuous v) (epsilon : ℝ) :
    Continuous (adjustedMargin μ u v epsilon) := by
  unfold adjustedMargin
  exact (continuous_const.mul hu).sub (continuous_const.mul hv)

/-- No ratio or variance assumption: the exact integral cancels the same
actual signal and residual means, leaving epsilon times the signal mean. -/
theorem adjustedMargin_integral (u v : α → ℝ)
    (hu : Continuous u) (hv : Continuous v) (epsilon : ℝ) :
    (∫ x : α, adjustedMargin μ u v epsilon x ∂μ) =
      epsilon * (∫ x : α, u x ∂μ) := by
  have huI : Integrable u μ :=
    hu.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hvI : Integrable v μ :=
    hv.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold adjustedMargin
  rw [integral_sub (huI.const_mul _) (hvI.const_mul _),
    integral_const_mul, integral_const_mul]
  ring

/-- At each finite original volume, every positive epsilon gives an
explicit positive-probability high relative-margin region. The denominator
is proved positive rather than assumed. -/
theorem adjustedMargin_half_mean_tail (u v : α → ℝ)
    (hu : Continuous u) (hv : Continuous v)
    (R : ℝ) (hBound : ∀ x, u x ≤ R)
    (hvNonneg : ∀ x, 0 ≤ v x)
    (hU : 0 < ∫ x : α, u x ∂μ)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    0 < 2 * ((∫ x : α, v x ∂μ) + epsilon) * R -
        epsilon * (∫ x : α, u x ∂μ) ∧
      (epsilon * (∫ x : α, u x ∂μ)) /
        (2 * ((∫ x : α, v x ∂μ) + epsilon) * R -
          epsilon * (∫ x : α, u x ∂μ)) ≤
        Measure.real μ {x : α |
          epsilon * (∫ y : α, u y ∂μ) / 2 <
            adjustedMargin μ u v epsilon x} := by
  have hV : 0 ≤ ∫ x : α, v x ∂μ := integral_nonneg hvNonneg
  have hCoeff : 0 ≤ (∫ x : α, v x ∂μ) + epsilon :=
    add_nonneg hV hepsilon.le
  have hUpper (x : α) :
      adjustedMargin μ u v epsilon x ≤
        ((∫ y : α, v y ∂μ) + epsilon) * R := by
    have hSub : 0 ≤ (∫ y : α, u y ∂μ) * v x :=
      mul_nonneg hU.le (hvNonneg x)
    calc
      adjustedMargin μ u v epsilon x =
          ((∫ y : α, v y ∂μ) + epsilon) * u x -
            (∫ y : α, u y ∂μ) * v x := rfl
      _ ≤ ((∫ y : α, v y ∂μ) + epsilon) * u x :=
        sub_le_self _ hSub
      _ ≤ ((∫ y : α, v y ∂μ) + epsilon) * R :=
        mul_le_mul_of_nonneg_left (hBound x) hCoeff
  have hMean : 0 < ∫ x : α, adjustedMargin μ u v epsilon x ∂μ := by
    rw [adjustedMargin_integral μ u v hu hv epsilon]
    exact mul_pos hepsilon hU
  have ht := CompactPositiveMomentTail.half_mean_upper_tail μ
    (adjustedMargin μ u v epsilon)
    (adjustedMargin_continuous μ u v hu hv epsilon)
    (((∫ x : α, v x ∂μ) + epsilon) * R) hUpper hMean
  rw [adjustedMargin_integral μ u v hu hv epsilon] at ht
  simpa only [mul_assoc] using ht

end

end MGAP4D.MathlibAnalytic.CompactPositiveMeanRelativeResidual

#print axioms MGAP4D.MathlibAnalytic.CompactPositiveMeanRelativeResidual.adjustedMargin_continuous
#print axioms MGAP4D.MathlibAnalytic.CompactPositiveMeanRelativeResidual.adjustedMargin_integral
#print axioms MGAP4D.MathlibAnalytic.CompactPositiveMeanRelativeResidual.adjustedMargin_half_mean_tail
