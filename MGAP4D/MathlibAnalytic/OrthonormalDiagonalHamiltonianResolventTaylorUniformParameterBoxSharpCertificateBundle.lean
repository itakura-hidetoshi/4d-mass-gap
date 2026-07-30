import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianResolventTaylorSharpMinimalTruncationTheoryBundle
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace LinearPMap ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 2400000

/-- Increasing the spectral lower gap cannot increase the sharp closed-ball
resolvent Taylor truncation order. -/
theorem resolventTaylorClosedBall_sharpTruncationOrder_antitone_gap
    {delta₁ delta₂ lambda r epsilon : ℝ}
    (hdelta₁₂ : delta₁ ≤ delta₂)
    (hlambda₁ : lambda < delta₁)
    (hr0 : 0 ≤ r) (hrlt₁ : r < delta₁ - lambda)
    (hepsilon : 0 < epsilon) :
    resolventTaylorClosedBall_sharpTruncationOrder
        delta₂ lambda r epsilon ≤
      resolventTaylorClosedBall_sharpTruncationOrder
        delta₁ lambda r epsilon := by
  have hbase₁ : 0 < delta₁ - lambda := sub_pos.mpr hlambda₁
  have hbase₂ : 0 < delta₂ - lambda := by linarith
  have hbaseOrder : delta₁ - lambda ≤ delta₂ - lambda := by linarith
  have hinvOrder :
      (delta₂ - lambda)⁻¹ ≤ (delta₁ - lambda)⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le hbase₁ hbaseOrder
  have hq₂0 : 0 ≤ r * (delta₂ - lambda)⁻¹ :=
    mul_nonneg hr0 (inv_nonneg.mpr hbase₂.le)
  have hq₁0 : 0 ≤ r * (delta₁ - lambda)⁻¹ :=
    mul_nonneg hr0 (inv_nonneg.mpr hbase₁.le)
  have hq₂₁ :
      r * (delta₂ - lambda)⁻¹ ≤ r * (delta₁ - lambda)⁻¹ :=
    mul_le_mul_of_nonneg_left hinvOrder hr0
  have hq₁lt : r * (delta₁ - lambda)⁻¹ < 1 := by
    calc
      r * (delta₁ - lambda)⁻¹ <
          (delta₁ - lambda) * (delta₁ - lambda)⁻¹ :=
        mul_lt_mul_of_pos_right hrlt₁ (inv_pos.mpr hbase₁)
      _ = 1 := by simp [ne_of_gt hbase₁]
  have hmargin₁ : 0 < delta₁ - lambda - r := sub_pos.mpr hrlt₁
  have hmargin₂ : 0 < delta₂ - lambda - r := by linarith
  have hmarginOrder :
      delta₁ - lambda - r ≤ delta₂ - lambda - r := by linarith
  have hC₂ : 0 < (delta₂ - lambda - r)⁻¹ := inv_pos.mpr hmargin₂
  have hC₁ : 0 < (delta₁ - lambda - r)⁻¹ := inv_pos.mpr hmargin₁
  have hC₂₁ :
      (delta₂ - lambda - r)⁻¹ ≤ (delta₁ - lambda - r)⁻¹ := by
    simpa only [one_div] using
      one_div_le_one_div_of_le hmargin₁ hmarginOrder
  simpa [resolventTaylorClosedBall_sharpTruncationOrder] using
    (geometricDecaySharpTruncationOrder_mono_rate_constant_antitone_tolerance
      hq₂0 hq₁0 hq₂₁ hq₁lt hC₂ hC₁ hC₂₁
      hepsilon hepsilon le_rfl)

/-- Joint comparison theorem for resolvent Taylor complexity.  A larger gap, a
smaller Taylor center, a smaller parameter-ball radius, and a larger tolerance
can only reduce the sharp truncation requirement. -/
theorem resolventTaylorClosedBall_sharpTruncationOrder_mono_gap_center_radius_antitone_tolerance
    {delta₁ delta₂ lambda₁ lambda₂ r₁ r₂ epsilon₁ epsilon₂ : ℝ}
    (hdelta₁₂ : delta₁ ≤ delta₂)
    (hlambda₁₂ : lambda₁ ≤ lambda₂)
    (hlambda₂ : lambda₂ < delta₁)
    (hr₁0 : 0 ≤ r₁) (hr₁₂ : r₁ ≤ r₂)
    (hr₂lt : r₂ < delta₁ - lambda₂)
    (hepsilon₂ : 0 < epsilon₂) (hepsilon₁ : 0 < epsilon₁)
    (hepsilon₂₁ : epsilon₂ ≤ epsilon₁) :
    resolventTaylorClosedBall_sharpTruncationOrder
        delta₂ lambda₁ r₁ epsilon₁ ≤
      resolventTaylorClosedBall_sharpTruncationOrder
        delta₁ lambda₂ r₂ epsilon₂ := by
  have hlambda₁delta₁ : lambda₁ < delta₁ := lt_of_le_of_lt hlambda₁₂ hlambda₂
  have hr₁lt : r₁ < delta₁ - lambda₁ := by linarith
  calc
    resolventTaylorClosedBall_sharpTruncationOrder
        delta₂ lambda₁ r₁ epsilon₁ ≤
      resolventTaylorClosedBall_sharpTruncationOrder
        delta₁ lambda₁ r₁ epsilon₁ :=
      resolventTaylorClosedBall_sharpTruncationOrder_antitone_gap
        hdelta₁₂ hlambda₁delta₁ hr₁0 hr₁lt hepsilon₁
    _ ≤ resolventTaylorClosedBall_sharpTruncationOrder
        delta₁ lambda₂ r₁ epsilon₁ :=
      resolventTaylorClosedBall_sharpTruncationOrder_mono_center
        hlambda₁₂ hlambda₂ hr₁0 (by linarith) hepsilon₁
    _ ≤ resolventTaylorClosedBall_sharpTruncationOrder
        delta₁ lambda₂ r₂ epsilon₁ :=
      resolventTaylorClosedBall_sharpTruncationOrder_mono_radius
        hlambda₂ hr₁0 hr₁₂ hr₂lt hepsilon₁
    _ ≤ resolventTaylorClosedBall_sharpTruncationOrder
        delta₁ lambda₂ r₂ epsilon₂ :=
      resolventTaylorClosedBall_sharpTruncationOrder_antitone_epsilon
        hlambda₂ (le_trans hr₁0 hr₁₂) hr₂lt
        hepsilon₂ hepsilon₁ hepsilon₂₁

/-- The single sharp Taylor degree attached to the worst corner of a resolvent
parameter box.  The worst corner uses the smallest permitted gap, largest
Taylor center, largest closed-ball radius, and smallest tolerance. -/
noncomputable def resolventTaylorClosedBall_parameterBoxWorstCornerSharpTruncationOrder
    (deltaMin lambdaMax rMax epsilonMin : ℝ) : ℕ :=
  resolventTaylorClosedBall_sharpTruncationOrder
    deltaMin lambdaMax rMax epsilonMin

/-- Every sharp degree in a valid resolvent parameter box is bounded by the
sharp degree at its worst corner. -/
theorem resolventTaylorClosedBall_sharpTruncationOrder_le_parameterBoxWorstCorner
    {deltaMin delta lambda lambdaMax r rMax epsilonMin epsilon : ℝ}
    (hdelta : deltaMin ≤ delta)
    (hlambda : lambda ≤ lambdaMax)
    (hlambdaMax : lambdaMax < deltaMin)
    (hr0 : 0 ≤ r) (hr : r ≤ rMax)
    (hrMaxlt : rMax < deltaMin - lambdaMax)
    (hepsilonMin : 0 < epsilonMin)
    (hepsilon : epsilonMin ≤ epsilon) :
    resolventTaylorClosedBall_sharpTruncationOrder
        delta lambda r epsilon ≤
      resolventTaylorClosedBall_parameterBoxWorstCornerSharpTruncationOrder
        deltaMin lambdaMax rMax epsilonMin := by
  have hepsilonPos : 0 < epsilon := lt_of_lt_of_le hepsilonMin hepsilon
  simpa [resolventTaylorClosedBall_parameterBoxWorstCornerSharpTruncationOrder] using
    (resolventTaylorClosedBall_sharpTruncationOrder_mono_gap_center_radius_antitone_tolerance
      hdelta hlambda hlambdaMax hr0 hr hrMaxlt
      hepsilonMin hepsilonPos hepsilon)

/-- The worst-corner degree is the actual greatest sharp degree attained over
the entire valid parameter box, not merely an upper bound. -/
theorem resolventTaylorClosedBall_parameterBoxWorstCornerSharpTruncationOrder_isGreatest
    {deltaMin lambdaMax rMax epsilonMin : ℝ}
    (hlambdaMax : lambdaMax < deltaMin)
    (hrMax0 : 0 ≤ rMax)
    (hrMaxlt : rMax < deltaMin - lambdaMax)
    (hepsilonMin : 0 < epsilonMin) :
    IsGreatest
      {N : ℕ |
        ∃ delta lambda r epsilon : ℝ,
          deltaMin ≤ delta ∧
          lambda ≤ lambdaMax ∧
          0 ≤ r ∧ r ≤ rMax ∧
          epsilonMin ≤ epsilon ∧
          N = resolventTaylorClosedBall_sharpTruncationOrder
            delta lambda r epsilon}
      (resolventTaylorClosedBall_parameterBoxWorstCornerSharpTruncationOrder
        deltaMin lambdaMax rMax epsilonMin) := by
  constructor
  · refine ⟨deltaMin, lambdaMax, rMax, epsilonMin, le_rfl, le_rfl,
      hrMax0, le_rfl, le_rfl, ?_⟩
    rfl
  · intro N hN
    rcases hN with
      ⟨delta, lambda, r, epsilon, hdelta, hlambda, hr0, hr,
        hepsilon, rfl⟩
    exact
      resolventTaylorClosedBall_sharpTruncationOrder_le_parameterBoxWorstCorner
        hdelta hlambda hlambdaMax hr0 hr hrMaxlt hepsilonMin hepsilon

/-- The worst-corner certificate simultaneously controls operator-norm Taylor
remainders for every member of a common-gap orthonormal-diagonal family, every
admissible gap, center, radius, tolerance, and spectral parameter in the box. -/
theorem orthonormalDiagonalHamiltonianResolvent_taylor_operatorNorm_error_lt_parameterBox_family_of_worstCornerSharpTruncationOrder
    {J ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : J → OrthonormalBasis ι ℝ E) (a : J → ι → ℝ) (delta : ℝ)
    (hdeltaSpectrum : ∀ j : J, ∀ i : ι, delta ≤ a j i)
    {deltaMin lambdaMax rMax epsilonMin : ℝ}
    (hdelta : deltaMin ≤ delta)
    (hlambdaMax : lambdaMax < deltaMin)
    (hrMax0 : 0 ≤ rMax)
    (hrMaxlt : rMax < deltaMin - lambdaMax)
    (hepsilonMin : 0 < epsilonMin)
    {lambda r epsilon : ℝ}
    (hlambda : lambda ≤ lambdaMax)
    (hr0 : 0 ≤ r) (hr : r ≤ rMax)
    (hepsilon : epsilonMin ≤ epsilon)
    {N : ℕ}
    (hN : resolventTaylorClosedBall_parameterBoxWorstCornerSharpTruncationOrder
      deltaMin lambdaMax rMax epsilonMin ≤ N)
    (j : J) (mu : ℝ) (hmu : ‖mu - lambda‖ ≤ r) :
    ‖orthonormalDiagonalHamiltonianResolvent (b j) (a j) mu -
        (∑ k ∈ Finset.range N,
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
            iteratedDeriv k
              (orthonormalDiagonalHamiltonianResolvent (b j) (a j)) lambda)‖ <
      epsilon := by
  have hlambdaDelta : lambda < delta := by linarith
  have hrlt : r < delta - lambda := by linarith
  have hepsilonPos : 0 < epsilon := lt_of_lt_of_le hepsilonMin hepsilon
  have hsharp :
      resolventTaylorClosedBall_sharpTruncationOrder
          delta lambda r epsilon ≤ N :=
    le_trans
      (resolventTaylorClosedBall_sharpTruncationOrder_le_parameterBoxWorstCorner
        hdelta hlambda hlambdaMax hr0 hr hrMaxlt hepsilonMin hepsilon)
      hN
  exact
    orthonormalDiagonalHamiltonianResolvent_taylor_operatorNorm_error_lt_closedBall_family_of_sharpTruncationOrder
      b a delta hdeltaSpectrum hlambdaDelta hr0 hrlt hepsilonPos
      hsharp j mu hmu

/-- The same worst-corner degree simultaneously controls every real matrix
element on the two unit balls throughout the full parameter box. -/
theorem orthonormalDiagonalHamiltonianResolvent_taylor_matrixElement_error_abs_lt_parameterBox_unitBalls_family_of_worstCornerSharpTruncationOrder
    {J ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : J → OrthonormalBasis ι ℝ E) (a : J → ι → ℝ) (delta : ℝ)
    (hdeltaSpectrum : ∀ j : J, ∀ i : ι, delta ≤ a j i)
    {deltaMin lambdaMax rMax epsilonMin : ℝ}
    (hdelta : deltaMin ≤ delta)
    (hlambdaMax : lambdaMax < deltaMin)
    (hrMax0 : 0 ≤ rMax)
    (hrMaxlt : rMax < deltaMin - lambdaMax)
    (hepsilonMin : 0 < epsilonMin)
    {lambda r epsilon : ℝ}
    (hlambda : lambda ≤ lambdaMax)
    (hr0 : 0 ≤ r) (hr : r ≤ rMax)
    (hepsilon : epsilonMin ≤ epsilon)
    {N : ℕ}
    (hN : resolventTaylorClosedBall_parameterBoxWorstCornerSharpTruncationOrder
      deltaMin lambdaMax rMax epsilonMin ≤ N)
    (j : J) (mu : ℝ) (hmu : ‖mu - lambda‖ ≤ r)
    (x y : E) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    |inner ℝ x
      ((orthonormalDiagonalHamiltonianResolvent (b j) (a j) mu -
        ∑ k ∈ Finset.range N,
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
            iteratedDeriv k
              (orthonormalDiagonalHamiltonianResolvent (b j) (a j)) lambda) y)| <
      epsilon := by
  have hlambdaDelta : lambda < delta := by linarith
  have hrlt : r < delta - lambda := by linarith
  have hepsilonPos : 0 < epsilon := lt_of_lt_of_le hepsilonMin hepsilon
  have hsharp :
      resolventTaylorClosedBall_sharpTruncationOrder
          delta lambda r epsilon ≤ N :=
    le_trans
      (resolventTaylorClosedBall_sharpTruncationOrder_le_parameterBoxWorstCorner
        hdelta hlambda hlambdaMax hr0 hr hrMaxlt hepsilonMin hepsilon)
      hN
  exact
    orthonormalDiagonalHamiltonianResolvent_taylor_matrixElement_error_abs_lt_closedBall_unitBalls_family_of_sharpTruncationOrder
      b a delta hdeltaSpectrum hlambdaDelta hr0 hrlt hepsilonPos
      hsharp j mu hmu x y hx hy

/-- At the worst-corner sharp degree itself, the common-gap family satisfies the
operator-norm tolerance simultaneously throughout the entire parameter box. -/
theorem orthonormalDiagonalHamiltonianResolvent_taylor_operatorNorm_error_lt_parameterBox_family_at_worstCornerSharpTruncationOrder
    {J ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : J → OrthonormalBasis ι ℝ E) (a : J → ι → ℝ) (delta : ℝ)
    (hdeltaSpectrum : ∀ j : J, ∀ i : ι, delta ≤ a j i)
    {deltaMin lambdaMax rMax epsilonMin : ℝ}
    (hdelta : deltaMin ≤ delta)
    (hlambdaMax : lambdaMax < deltaMin)
    (hrMax0 : 0 ≤ rMax)
    (hrMaxlt : rMax < deltaMin - lambdaMax)
    (hepsilonMin : 0 < epsilonMin)
    {lambda r epsilon : ℝ}
    (hlambda : lambda ≤ lambdaMax)
    (hr0 : 0 ≤ r) (hr : r ≤ rMax)
    (hepsilon : epsilonMin ≤ epsilon)
    (j : J) (mu : ℝ) (hmu : ‖mu - lambda‖ ≤ r) :
    ‖orthonormalDiagonalHamiltonianResolvent (b j) (a j) mu -
        (∑ k ∈ Finset.range
          (resolventTaylorClosedBall_parameterBoxWorstCornerSharpTruncationOrder
            deltaMin lambdaMax rMax epsilonMin),
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
            iteratedDeriv k
              (orthonormalDiagonalHamiltonianResolvent (b j) (a j)) lambda)‖ <
      epsilon := by
  exact
    orthonormalDiagonalHamiltonianResolvent_taylor_operatorNorm_error_lt_parameterBox_family_of_worstCornerSharpTruncationOrder
      b a delta hdeltaSpectrum hdelta hlambdaMax hrMax0 hrMaxlt hepsilonMin
      hlambda hr0 hr hepsilon le_rfl j mu hmu

/-- At the worst-corner sharp degree itself, all two-unit-ball matrix elements
satisfy the tolerance simultaneously throughout the parameter box. -/
theorem orthonormalDiagonalHamiltonianResolvent_taylor_matrixElement_error_abs_lt_parameterBox_unitBalls_family_at_worstCornerSharpTruncationOrder
    {J ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : J → OrthonormalBasis ι ℝ E) (a : J → ι → ℝ) (delta : ℝ)
    (hdeltaSpectrum : ∀ j : J, ∀ i : ι, delta ≤ a j i)
    {deltaMin lambdaMax rMax epsilonMin : ℝ}
    (hdelta : deltaMin ≤ delta)
    (hlambdaMax : lambdaMax < deltaMin)
    (hrMax0 : 0 ≤ rMax)
    (hrMaxlt : rMax < deltaMin - lambdaMax)
    (hepsilonMin : 0 < epsilonMin)
    {lambda r epsilon : ℝ}
    (hlambda : lambda ≤ lambdaMax)
    (hr0 : 0 ≤ r) (hr : r ≤ rMax)
    (hepsilon : epsilonMin ≤ epsilon)
    (j : J) (mu : ℝ) (hmu : ‖mu - lambda‖ ≤ r)
    (x y : E) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    |inner ℝ x
      ((orthonormalDiagonalHamiltonianResolvent (b j) (a j) mu -
        ∑ k ∈ Finset.range
          (resolventTaylorClosedBall_parameterBoxWorstCornerSharpTruncationOrder
            deltaMin lambdaMax rMax epsilonMin),
          ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
            iteratedDeriv k
              (orthonormalDiagonalHamiltonianResolvent (b j) (a j)) lambda) y)| <
      epsilon := by
  exact
    orthonormalDiagonalHamiltonianResolvent_taylor_matrixElement_error_abs_lt_parameterBox_unitBalls_family_of_worstCornerSharpTruncationOrder
      b a delta hdeltaSpectrum hdelta hlambdaMax hrMax0 hrMaxlt hepsilonMin
      hlambda hr0 hr hepsilon le_rfl j mu hmu x y hx hy

end MathlibAnalytic
end MGAP4D

end
