import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonUniformSpectralGapCertificateL2
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Topology.Order.OrderClosed

namespace MGAP4D
namespace MathlibAnalytic

open Filter Topology

noncomputable section

/-- A family of bounded operators on one identified real Hilbert space,
converging strongly to a limit operator while sharing one positive quadratic
lower bound. -/
structure RealHilbertUniformCoerciveStrongLimitData
    (ι E : Type*)
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (l : Filter ι) where
  approximant : ι → E →L[ℝ] E
  limitOperator : E →L[ℝ] E
  gap : ℝ
  gap_pos : 0 < gap
  approximant_gap : ∀ (i : ι) (f : E),
    gap * ‖f‖ ^ 2 ≤ inner ℝ (approximant i f) f
  strong_tendsto : ∀ f : E,
    Tendsto (fun i => approximant i f) l (𝓝 (limitOperator f))

/-- A strong operator limit preserves a family-uniform quadratic coercivity
bound on the identified Hilbert space. -/
theorem realHilbert_uniformCoerciveStrongLimit_limit_gap
    {ι E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    {l : Filter ι}
    [Filter.NeBot l]
    (D : RealHilbertUniformCoerciveStrongLimitData ι E l)
    (f : E) :
    D.gap * ‖f‖ ^ 2 ≤ inner ℝ (D.limitOperator f) f := by
  have hInner :
      Tendsto
        (fun i => inner ℝ (D.approximant i f) f)
        l
        (𝓝 (inner ℝ (D.limitOperator f) f)) :=
    (D.strong_tendsto f).inner tendsto_const_nhds
  exact ge_of_tendsto' hInner (fun i => D.approximant_gap i f)

/-- The same strong-limit coercivity gives a norm lower bound for the limit
operator. -/
theorem realHilbert_uniformCoerciveStrongLimit_norm_lower
    {ι E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    {l : Filter ι}
    [Filter.NeBot l]
    (D : RealHilbertUniformCoerciveStrongLimitData ι E l)
    (f : E) :
    D.gap * ‖f‖ ≤ ‖D.limitOperator f‖ := by
  by_cases hf : 0 < ‖f‖
  · refine (mul_le_mul_iff_left₀ hf).mp ?_
    calc
      D.gap * ‖f‖ * ‖f‖ = D.gap * ‖f‖ ^ 2 := by ring
      _ ≤ inner ℝ (D.limitOperator f) f :=
        realHilbert_uniformCoerciveStrongLimit_limit_gap D f
      _ ≤ ‖D.limitOperator f‖ * ‖f‖ :=
        real_inner_le_norm (D.limitOperator f) f
  · have hzero : f = 0 := by simpa using hf
    simp [hzero]

/-- A strongly convergent family with one positive uniform coercivity constant
has an injective limit operator. -/
theorem realHilbert_uniformCoerciveStrongLimit_limit_injective
    {ι E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    {l : Filter ι}
    [Filter.NeBot l]
    (D : RealHilbertUniformCoerciveStrongLimitData ι E l) :
    Function.Injective D.limitOperator := by
  intro f g hfg
  have hLower :=
    realHilbert_uniformCoerciveStrongLimit_norm_lower D (f - g)
  have hImage : D.limitOperator (f - g) = 0 := by
    rw [map_sub, hfg, sub_self]
  rw [hImage, norm_zero] at hLower
  have hNorm : ‖f - g‖ = 0 := by
    by_contra hne
    have hNormPos : 0 < ‖f - g‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    have hProductPos : 0 < D.gap * ‖f - g‖ :=
      mul_pos D.gap_pos hNormPos
    linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hNorm)

end

end MathlibAnalytic
end MGAP4D
