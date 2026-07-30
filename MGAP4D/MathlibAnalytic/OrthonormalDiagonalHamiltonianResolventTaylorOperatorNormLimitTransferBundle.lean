import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianResolventTaylorUniformParameterBoxSharpCertificateBundle
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace LinearPMap ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 2400000

/-- The finite Taylor partial sum of an operator-valued function. -/
noncomputable def continuousLinearMapTaylorPartialSum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → E →L[ℝ] E) (lambda mu : ℝ) (N : ℕ) : E →L[ℝ] E :=
  ∑ k ∈ Finset.range N,
    ((mu - lambda) ^ k * (k.factorial : ℝ)⁻¹) •
      iteratedDeriv k F lambda

/-- Operator-norm convergence data sufficient to pass a finite Taylor expansion
from a sequence of operator-valued functions to its limit.  Both values and all
iterated derivatives converge in the continuous-linear-map norm topology. -/
structure ContinuousLinearMapTaylorOperatorNormLimitData
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℕ → ℝ → E →L[ℝ] E) where
  limitResolvent : ℝ → E →L[ℝ] E
  value_tendsto : ∀ mu : ℝ,
    Tendsto (fun n : ℕ => F n mu) atTop (𝓝 (limitResolvent mu))
  iteratedDeriv_tendsto : ∀ k : ℕ, ∀ lambda : ℝ,
    Tendsto (fun n : ℕ => iteratedDeriv k (F n) lambda) atTop
      (𝓝 (iteratedDeriv k limitResolvent lambda))

/-- An operator-norm Taylor limit is unique pointwise, hence unique as a
resolvent-valued function. -/
theorem ContinuousLinearMapTaylorOperatorNormLimitData.limitResolvent_unique
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℕ → ℝ → E →L[ℝ] E}
    (L₁ L₂ : ContinuousLinearMapTaylorOperatorNormLimitData F) :
    L₁.limitResolvent = L₂.limitResolvent := by
  funext mu
  exact tendsto_nhds_unique (L₁.value_tendsto mu) (L₂.value_tendsto mu)

/-- Convergence of every derivative coefficient implies convergence of each
fixed finite Taylor partial sum in operator norm. -/
theorem continuousLinearMapTaylorPartialSum_tendsto_atTop
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℕ → ℝ → E →L[ℝ] E}
    (L : ContinuousLinearMapTaylorOperatorNormLimitData F)
    (lambda mu : ℝ) (N : ℕ) :
    Tendsto
      (fun n : ℕ => continuousLinearMapTaylorPartialSum (F n) lambda mu N)
      atTop
      (𝓝 (continuousLinearMapTaylorPartialSum L.limitResolvent lambda mu N)) := by
  unfold continuousLinearMapTaylorPartialSum
  apply tendsto_finsetSum (Finset.range N)
  intro k hk
  exact tendsto_const_nhds.smul (L.iteratedDeriv_tendsto k lambda)

/-- The Taylor remainder converges in operator norm when the resolvent value and
the finitely many Taylor coefficients converge in operator norm. -/
theorem continuousLinearMapTaylorRemainder_tendsto_atTop
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℕ → ℝ → E →L[ℝ] E}
    (L : ContinuousLinearMapTaylorOperatorNormLimitData F)
    (lambda mu : ℝ) (N : ℕ) :
    Tendsto
      (fun n : ℕ =>
        F n mu - continuousLinearMapTaylorPartialSum (F n) lambda mu N)
      atTop
      (𝓝 (L.limitResolvent mu -
        continuousLinearMapTaylorPartialSum L.limitResolvent lambda mu N)) := by
  exact (L.value_tendsto mu).sub
    (continuousLinearMapTaylorPartialSum_tendsto_atTop L lambda mu N)

/-- The operator norms of the Taylor remainders converge to the norm of the
limit Taylor remainder. -/
theorem continuousLinearMapTaylorRemainder_norm_tendsto_atTop
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℕ → ℝ → E →L[ℝ] E}
    (L : ContinuousLinearMapTaylorOperatorNormLimitData F)
    (lambda mu : ℝ) (N : ℕ) :
    Tendsto
      (fun n : ℕ =>
        ‖F n mu - continuousLinearMapTaylorPartialSum (F n) lambda mu N‖)
      atTop
      (𝓝 ‖L.limitResolvent mu -
        continuousLinearMapTaylorPartialSum L.limitResolvent lambda mu N‖) := by
  exact (continuousLinearMapTaylorRemainder_tendsto_atTop L lambda mu N).norm

/-- A common closed operator-norm upper bound for all approximating Taylor
remainders passes to the operator-norm limit. -/
theorem continuousLinearMapTaylorRemainder_norm_le_of_operatorNormLimit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℕ → ℝ → E →L[ℝ] E}
    (L : ContinuousLinearMapTaylorOperatorNormLimitData F)
    (lambda mu : ℝ) (N : ℕ) {C : ℝ}
    (hC : ∀ n : ℕ,
      ‖F n mu - continuousLinearMapTaylorPartialSum (F n) lambda mu N‖ ≤ C) :
    ‖L.limitResolvent mu -
      continuousLinearMapTaylorPartialSum L.limitResolvent lambda mu N‖ ≤ C := by
  exact le_of_tendsto'
    (continuousLinearMapTaylorRemainder_norm_tendsto_atTop L lambda mu N) hC

/-- A common-gap orthonormal-diagonal approximation sequence transfers its
closed-ball geometric Taylor envelope to any operator-norm limit resolvent. -/
theorem orthonormalDiagonalHamiltonianResolvent_limit_sub_taylor_partialSum_norm_le_closedBall
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : ℕ → OrthonormalBasis ι ℝ E) (a : ℕ → ι → ℝ) (delta : ℝ)
    (hdelta : ∀ n : ℕ, ∀ i : ι, delta ≤ a n i)
    (L : ContinuousLinearMapTaylorOperatorNormLimitData
      (fun n : ℕ => orthonormalDiagonalHamiltonianResolvent (b n) (a n)))
    {lambda r mu : ℝ} (hlambda : lambda < delta)
    (hr0 : 0 ≤ r) (hrlt : r < delta - lambda)
    (hmu : ‖mu - lambda‖ ≤ r) (N : ℕ) :
    ‖L.limitResolvent mu -
        continuousLinearMapTaylorPartialSum L.limitResolvent lambda mu N‖ ≤
      (r * (delta - lambda)⁻¹) ^ N *
        (delta - lambda - r)⁻¹ := by
  apply continuousLinearMapTaylorRemainder_norm_le_of_operatorNormLimit
    L lambda mu N
  intro n
  simpa only [continuousLinearMapTaylorPartialSum] using
    (orthonormalDiagonalHamiltonianResolvent_sub_taylor_partialSum_norm_le_closedBall_family
      b a delta hdelta hlambda hr0 hrlt hmu N n)

/-- The worst-corner sharp degree controls the operator-norm Taylor remainder
of the limit resolvent throughout the entire parameter box. -/
theorem orthonormalDiagonalHamiltonianResolvent_limit_taylor_operatorNorm_error_lt_parameterBox_of_worstCornerSharpTruncationOrder
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : ℕ → OrthonormalBasis ι ℝ E) (a : ℕ → ι → ℝ) (delta : ℝ)
    (hdeltaSpectrum : ∀ n : ℕ, ∀ i : ι, delta ≤ a n i)
    (L : ContinuousLinearMapTaylorOperatorNormLimitData
      (fun n : ℕ => orthonormalDiagonalHamiltonianResolvent (b n) (a n)))
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
    (mu : ℝ) (hmu : ‖mu - lambda‖ ≤ r) :
    ‖L.limitResolvent mu -
        continuousLinearMapTaylorPartialSum L.limitResolvent lambda mu N‖ <
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
  have hlimit :
      ‖L.limitResolvent mu -
          continuousLinearMapTaylorPartialSum L.limitResolvent lambda mu N‖ ≤
        (r * (delta - lambda)⁻¹) ^ N *
          (delta - lambda - r)⁻¹ :=
    orthonormalDiagonalHamiltonianResolvent_limit_sub_taylor_partialSum_norm_le_closedBall
      b a delta hdeltaSpectrum L hlambdaDelta hr0 hrlt hmu N
  have henvelope :
      (r * (delta - lambda)⁻¹) ^ N *
        (delta - lambda - r)⁻¹ < epsilon :=
    (resolventTaylorClosedBall_sharpTruncationOrder_le_iff
      hlambdaDelta hr0 hrlt hepsilonPos N).1 hsharp
  exact lt_of_le_of_lt hlimit henvelope

/-- The same limit certificate controls every real matrix element on the two
closed unit balls throughout the full parameter box. -/
theorem orthonormalDiagonalHamiltonianResolvent_limit_taylor_matrixElement_error_abs_lt_parameterBox_unitBalls_of_worstCornerSharpTruncationOrder
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : ℕ → OrthonormalBasis ι ℝ E) (a : ℕ → ι → ℝ) (delta : ℝ)
    (hdeltaSpectrum : ∀ n : ℕ, ∀ i : ι, delta ≤ a n i)
    (L : ContinuousLinearMapTaylorOperatorNormLimitData
      (fun n : ℕ => orthonormalDiagonalHamiltonianResolvent (b n) (a n)))
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
    (mu : ℝ) (hmu : ‖mu - lambda‖ ≤ r)
    (x y : E) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    |inner ℝ x
      ((L.limitResolvent mu -
        continuousLinearMapTaylorPartialSum L.limitResolvent lambda mu N) y)| <
      epsilon := by
  have hnorm :=
    orthonormalDiagonalHamiltonianResolvent_limit_taylor_operatorNorm_error_lt_parameterBox_of_worstCornerSharpTruncationOrder
      b a delta hdeltaSpectrum L hdelta hlambdaMax hrMax0 hrMaxlt
      hepsilonMin hlambda hr0 hr hepsilon hN mu hmu
  have hmatrix :
      |inner ℝ x
        ((L.limitResolvent mu -
          continuousLinearMapTaylorPartialSum L.limitResolvent lambda mu N) y)| ≤
        ‖L.limitResolvent mu -
          continuousLinearMapTaylorPartialSum L.limitResolvent lambda mu N‖ :=
    (continuousLinearMap_norm_le_iff_real_matrixElement_le_unitBalls
      (L.limitResolvent mu -
        continuousLinearMapTaylorPartialSum L.limitResolvent lambda mu N)
      (norm_nonneg _)).1 le_rfl x y hx hy
  exact lt_of_le_of_lt hmatrix hnorm

/-- At the worst-corner sharp degree itself, the operator-norm limit resolvent
satisfies every requested tolerance throughout the parameter box. -/
theorem orthonormalDiagonalHamiltonianResolvent_limit_taylor_operatorNorm_error_lt_parameterBox_at_worstCornerSharpTruncationOrder
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : ℕ → OrthonormalBasis ι ℝ E) (a : ℕ → ι → ℝ) (delta : ℝ)
    (hdeltaSpectrum : ∀ n : ℕ, ∀ i : ι, delta ≤ a n i)
    (L : ContinuousLinearMapTaylorOperatorNormLimitData
      (fun n : ℕ => orthonormalDiagonalHamiltonianResolvent (b n) (a n)))
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
    (mu : ℝ) (hmu : ‖mu - lambda‖ ≤ r) :
    ‖L.limitResolvent mu -
        continuousLinearMapTaylorPartialSum L.limitResolvent lambda mu
          (resolventTaylorClosedBall_parameterBoxWorstCornerSharpTruncationOrder
            deltaMin lambdaMax rMax epsilonMin)‖ < epsilon := by
  exact
    orthonormalDiagonalHamiltonianResolvent_limit_taylor_operatorNorm_error_lt_parameterBox_of_worstCornerSharpTruncationOrder
      b a delta hdeltaSpectrum L hdelta hlambdaMax hrMax0 hrMaxlt
      hepsilonMin hlambda hr0 hr hepsilon le_rfl mu hmu

/-- At the worst-corner sharp degree itself, every two-unit-ball matrix element
of the limit Taylor remainder satisfies the requested tolerance. -/
theorem orthonormalDiagonalHamiltonianResolvent_limit_taylor_matrixElement_error_abs_lt_parameterBox_unitBalls_at_worstCornerSharpTruncationOrder
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : ℕ → OrthonormalBasis ι ℝ E) (a : ℕ → ι → ℝ) (delta : ℝ)
    (hdeltaSpectrum : ∀ n : ℕ, ∀ i : ι, delta ≤ a n i)
    (L : ContinuousLinearMapTaylorOperatorNormLimitData
      (fun n : ℕ => orthonormalDiagonalHamiltonianResolvent (b n) (a n)))
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
    (mu : ℝ) (hmu : ‖mu - lambda‖ ≤ r)
    (x y : E) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    |inner ℝ x
      ((L.limitResolvent mu -
        continuousLinearMapTaylorPartialSum L.limitResolvent lambda mu
          (resolventTaylorClosedBall_parameterBoxWorstCornerSharpTruncationOrder
            deltaMin lambdaMax rMax epsilonMin)) y)| < epsilon := by
  exact
    orthonormalDiagonalHamiltonianResolvent_limit_taylor_matrixElement_error_abs_lt_parameterBox_unitBalls_of_worstCornerSharpTruncationOrder
      b a delta hdeltaSpectrum L hdelta hlambdaMax hrMax0 hrMaxlt
      hepsilonMin hlambda hr0 hr hepsilon le_rfl mu hmu x y hx hy

end MathlibAnalytic
end MGAP4D

end