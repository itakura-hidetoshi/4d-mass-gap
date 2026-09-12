import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianResolventTaylorOperatorNormLimitTransferBundle
import MGAP4D.MathlibAnalytic.OrthonormalDiagonalHamiltonianResolventFactorialDerivativeBundle
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic

noncomputable section

open Set Filter Topology ContinuousLinearMap Module
open scoped InnerProductSpace LinearPMap ContDiff Ring

namespace MGAP4D
namespace MathlibAnalytic

set_option maxHeartbeats 2400000

/-- Reconstruct a continuous linear map from its values on a finite basis.  The
map from the finite product of basis values to operator space is itself
continuous because the product is finite dimensional. -/
noncomputable def basisValuesToContinuousLinearMap
    {ι E F : Type*}
    [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    (v : Basis ι ℝ E) :
    (ι → F) →L[ℝ] (E →L[ℝ] F) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun f => v.constrL f
      map_add' := by
        intro f g
        ext x
        simp [Basis.constrL_apply, Finset.sum_add_distrib]
      map_smul' := by
        intro c f
        ext x
        simp [Basis.constrL_apply, Finset.smul_sum, smul_eq_mul,
          smul_smul, mul_comm] }

@[simp]
theorem basisValuesToContinuousLinearMap_apply_basis
    {ι E F : Type*}
    [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    (v : Basis ι ℝ E) (f : ι → F) (i : ι) :
    basisValuesToContinuousLinearMap v f (v i) = f i := by
  simp [basisValuesToContinuousLinearMap]

@[simp]
theorem basisValuesToContinuousLinearMap_reconstruct
    {ι E F : Type*}
    [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    (v : Basis ι ℝ E) (T : E →L[ℝ] F) :
    basisValuesToContinuousLinearMap v (fun i => T (v i)) = T := by
  ext x
  rw [basisValuesToContinuousLinearMap]
  change v.constrL (fun i => T (v i)) x = T x
  rw [Basis.constrL_apply]
  calc
    (∑ i, v.equivFun x i • T (v i)) =
        T (∑ i, v.equivFun x i • v i) := by
      rw [map_sum]
      simp only [map_smul]
    _ = T x := by rw [Basis.sum_equivFun]

/-- On a finite-dimensional domain and codomain, convergence on the vectors of
one finite basis upgrades to convergence in continuous-linear-map norm. -/
theorem continuousLinearMap_tendsto_of_tendsto_apply_basis
    {α ι E F : Type*}
    [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    {l : Filter α}
    {T : α → E →L[ℝ] F} {S : E →L[ℝ] F}
    (v : Basis ι ℝ E)
    (h : ∀ i : ι, Tendsto (fun a => T a (v i)) l (𝓝 (S (v i)))) :
    Tendsto T l (𝓝 S) := by
  have hPi :
      Tendsto (fun a : α => fun i : ι => T a (v i)) l
        (𝓝 (fun i : ι => S (v i))) :=
    tendsto_pi_nhds.2 h
  have hmap :=
    (basisValuesToContinuousLinearMap v).continuous.tendsto
      (fun i : ι => S (v i))
  have hcomp := hmap.comp hPi
  have htarget :
      basisValuesToContinuousLinearMap v (fun i : ι => S (v i)) = S :=
    basisValuesToContinuousLinearMap_reconstruct v S
  have hsource :
      (⇑(basisValuesToContinuousLinearMap v) ∘
        fun a : α => fun i : ι => T a (v i)) = T := by
    funext a
    exact basisValuesToContinuousLinearMap_reconstruct v (T a)
  rw [htarget, hsource] at hcomp
  exact hcomp

/-- Statewise strong convergence of continuous linear maps upgrades to
operator-norm convergence in finite dimension. -/
theorem continuousLinearMap_tendsto_of_tendsto_apply_finiteDimensional
    {α E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F]
    {l : Filter α}
    {T : α → E →L[ℝ] F} {S : E →L[ℝ] F}
    (h : ∀ x : E, Tendsto (fun a => T a x) l (𝓝 (S x))) :
    Tendsto T l (𝓝 S) := by
  let v := Module.finBasis ℝ E
  exact continuousLinearMap_tendsto_of_tendsto_apply_basis v
    (fun i => h (v i))

/-- Strong value-and-derivative convergence data for an operator-valued Taylor
family.  Unlike operator-norm data, convergence is required only after applying
each operator to a fixed state. -/
structure ContinuousLinearMapTaylorStrongLimitData
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℕ → ℝ → E →L[ℝ] E) where
  limitResolvent : ℝ → E →L[ℝ] E
  value_tendsto_apply : ∀ mu : ℝ, ∀ x : E,
    Tendsto (fun n : ℕ => F n mu x) atTop (𝓝 (limitResolvent mu x))
  iteratedDeriv_tendsto_apply : ∀ k : ℕ, ∀ lambda : ℝ, ∀ x : E,
    Tendsto (fun n : ℕ => (iteratedDeriv k (F n) lambda) x) atTop
      (𝓝 ((iteratedDeriv k limitResolvent lambda) x))

/-- In finite dimension, Taylor strong-limit data canonically upgrades to the
operator-norm limit data used by the quantitative Taylor-transfer theory. -/
noncomputable def ContinuousLinearMapTaylorStrongLimitData.toOperatorNormLimitData
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {F : ℕ → ℝ → E →L[ℝ] E}
    (S : ContinuousLinearMapTaylorStrongLimitData F) :
    ContinuousLinearMapTaylorOperatorNormLimitData F where
  limitResolvent := S.limitResolvent
  value_tendsto mu :=
    continuousLinearMap_tendsto_of_tendsto_apply_finiteDimensional
      (S.value_tendsto_apply mu)
  iteratedDeriv_tendsto k lambda :=
    continuousLinearMap_tendsto_of_tendsto_apply_finiteDimensional
      (S.iteratedDeriv_tendsto_apply k lambda)

/-- A strong Taylor limit is unique in finite dimension. -/
theorem ContinuousLinearMapTaylorStrongLimitData.limitResolvent_unique
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {F : ℕ → ℝ → E →L[ℝ] E}
    (S₁ S₂ : ContinuousLinearMapTaylorStrongLimitData F) :
    S₁.limitResolvent = S₂.limitResolvent := by
  exact ContinuousLinearMapTaylorOperatorNormLimitData.limitResolvent_unique
    S₁.toOperatorNormLimitData S₂.toOperatorNormLimitData

/-- A common operator-norm upper bound passes from a strongly convergent
finite-dimensional sequence to its limit. -/
theorem continuousLinearMap_norm_le_of_strongLimit_finiteDimensional
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (T : ℕ → E →L[ℝ] F) (S : E →L[ℝ] F)
    (hstrong : ∀ x : E,
      Tendsto (fun n : ℕ => T n x) atTop (𝓝 (S x)))
    {C : ℝ} (hC : ∀ n : ℕ, ‖T n‖ ≤ C) :
    ‖S‖ ≤ C := by
  have hop :=
    continuousLinearMap_tendsto_of_tendsto_apply_finiteDimensional hstrong
  exact le_of_tendsto' hop.norm hC

/-- The common spectral-gap resolvent norm bound is inherited by a
finite-dimensional strong resolvent limit. -/
theorem orthonormalDiagonalHamiltonianResolvent_strongLimit_norm_le_inv_sub
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : ℕ → OrthonormalBasis ι ℝ E) (a : ℕ → ι → ℝ) (delta : ℝ)
    (hdelta : ∀ n : ℕ, ∀ i : ι, delta ≤ a n i)
    (S : ContinuousLinearMapTaylorStrongLimitData
      (fun n : ℕ => orthonormalDiagonalHamiltonianResolvent (b n) (a n)))
    {lambda : ℝ} (hlambda : lambda < delta) :
    ‖S.limitResolvent lambda‖ ≤ (delta - lambda)⁻¹ := by
  exact continuousLinearMap_norm_le_of_strongLimit_finiteDimensional
    (fun n : ℕ => orthonormalDiagonalHamiltonianResolvent (b n) (a n) lambda)
    (S.limitResolvent lambda)
    (S.value_tendsto_apply lambda)
    (fun n => orthonormalDiagonalHamiltonianResolvent_norm_le_inv_sub
      (b n) (a n) delta lambda (hdelta n) hlambda)

/-- Every exact factorial derivative bound supplied by the common gap passes to
the finite-dimensional strong Taylor limit. -/
theorem orthonormalDiagonalHamiltonianResolvent_strongLimit_iteratedDeriv_norm_le
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : ℕ → OrthonormalBasis ι ℝ E) (a : ℕ → ι → ℝ) (delta : ℝ)
    (hdelta : ∀ n : ℕ, ∀ i : ι, delta ≤ a n i)
    (S : ContinuousLinearMapTaylorStrongLimitData
      (fun n : ℕ => orthonormalDiagonalHamiltonianResolvent (b n) (a n)))
    (k : ℕ) {lambda : ℝ} (hlambda : lambda < delta) :
    ‖iteratedDeriv k S.limitResolvent lambda‖ ≤
      (k.factorial : ℝ) * ((delta - lambda)⁻¹) ^ (k + 1) := by
  exact continuousLinearMap_norm_le_of_strongLimit_finiteDimensional
    (fun n : ℕ => iteratedDeriv k
      (orthonormalDiagonalHamiltonianResolvent (b n) (a n)) lambda)
    (iteratedDeriv k S.limitResolvent lambda)
    (S.iteratedDeriv_tendsto_apply k lambda)
    (fun n => orthonormalDiagonalHamiltonianResolvent_iteratedDeriv_norm_le
      (b n) (a n) delta (hdelta n) k hlambda)

/-- Strong Taylor convergence is sufficient to transfer the exact common-gap
closed-ball geometric remainder envelope to the limit. -/
theorem orthonormalDiagonalHamiltonianResolvent_strongLimit_sub_taylor_partialSum_norm_le_closedBall
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : ℕ → OrthonormalBasis ι ℝ E) (a : ℕ → ι → ℝ) (delta : ℝ)
    (hdelta : ∀ n : ℕ, ∀ i : ι, delta ≤ a n i)
    (S : ContinuousLinearMapTaylorStrongLimitData
      (fun n : ℕ => orthonormalDiagonalHamiltonianResolvent (b n) (a n)))
    {lambda r mu : ℝ} (hlambda : lambda < delta)
    (hr0 : 0 ≤ r) (hrlt : r < delta - lambda)
    (hmu : ‖mu - lambda‖ ≤ r) (N : ℕ) :
    ‖S.limitResolvent mu -
        continuousLinearMapTaylorPartialSum S.limitResolvent lambda mu N‖ ≤
      (r * (delta - lambda)⁻¹) ^ N *
        (delta - lambda - r)⁻¹ := by
  exact
    orthonormalDiagonalHamiltonianResolvent_limit_sub_taylor_partialSum_norm_le_closedBall
      b a delta hdelta S.toOperatorNormLimitData hlambda hr0 hrlt hmu N

/-- The worst-corner sharp degree controls the strong limit throughout the full
resolvent parameter box. -/
theorem orthonormalDiagonalHamiltonianResolvent_strongLimit_taylor_operatorNorm_error_lt_parameterBox_of_worstCornerSharpTruncationOrder
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : ℕ → OrthonormalBasis ι ℝ E) (a : ℕ → ι → ℝ) (delta : ℝ)
    (hdeltaSpectrum : ∀ n : ℕ, ∀ i : ι, delta ≤ a n i)
    (S : ContinuousLinearMapTaylorStrongLimitData
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
    ‖S.limitResolvent mu -
        continuousLinearMapTaylorPartialSum S.limitResolvent lambda mu N‖ <
      epsilon := by
  exact
    orthonormalDiagonalHamiltonianResolvent_limit_taylor_operatorNorm_error_lt_parameterBox_of_worstCornerSharpTruncationOrder
      b a delta hdeltaSpectrum S.toOperatorNormLimitData hdelta hlambdaMax
      hrMax0 hrMaxlt hepsilonMin hlambda hr0 hr hepsilon hN mu hmu

/-- The strong-limit worst-corner certificate also controls every real matrix
element on the two closed unit balls. -/
theorem orthonormalDiagonalHamiltonianResolvent_strongLimit_taylor_matrixElement_error_abs_lt_parameterBox_unitBalls_of_worstCornerSharpTruncationOrder
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : ℕ → OrthonormalBasis ι ℝ E) (a : ℕ → ι → ℝ) (delta : ℝ)
    (hdeltaSpectrum : ∀ n : ℕ, ∀ i : ι, delta ≤ a n i)
    (S : ContinuousLinearMapTaylorStrongLimitData
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
      ((S.limitResolvent mu -
        continuousLinearMapTaylorPartialSum S.limitResolvent lambda mu N) y)| <
      epsilon := by
  exact
    orthonormalDiagonalHamiltonianResolvent_limit_taylor_matrixElement_error_abs_lt_parameterBox_unitBalls_of_worstCornerSharpTruncationOrder
      b a delta hdeltaSpectrum S.toOperatorNormLimitData hdelta hlambdaMax
      hrMax0 hrMaxlt hepsilonMin hlambda hr0 hr hepsilon hN mu hmu
      x y hx hy

/-- At the worst-corner sharp degree itself, the strong limit satisfies every
operator-norm tolerance throughout the parameter box. -/
theorem orthonormalDiagonalHamiltonianResolvent_strongLimit_taylor_operatorNorm_error_lt_parameterBox_at_worstCornerSharpTruncationOrder
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : ℕ → OrthonormalBasis ι ℝ E) (a : ℕ → ι → ℝ) (delta : ℝ)
    (hdeltaSpectrum : ∀ n : ℕ, ∀ i : ι, delta ≤ a n i)
    (S : ContinuousLinearMapTaylorStrongLimitData
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
    ‖S.limitResolvent mu -
        continuousLinearMapTaylorPartialSum S.limitResolvent lambda mu
          (resolventTaylorClosedBall_parameterBoxWorstCornerSharpTruncationOrder
            deltaMin lambdaMax rMax epsilonMin)‖ < epsilon := by
  exact
    orthonormalDiagonalHamiltonianResolvent_strongLimit_taylor_operatorNorm_error_lt_parameterBox_of_worstCornerSharpTruncationOrder
      b a delta hdeltaSpectrum S hdelta hlambdaMax hrMax0 hrMaxlt
      hepsilonMin hlambda hr0 hr hepsilon le_rfl mu hmu

/-- At the worst-corner sharp degree itself, all two-unit-ball matrix elements
of the strong-limit Taylor remainder satisfy tolerance. -/
theorem orthonormalDiagonalHamiltonianResolvent_strongLimit_taylor_matrixElement_error_abs_lt_parameterBox_unitBalls_at_worstCornerSharpTruncationOrder
    {ι E : Type*}
    [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (b : ℕ → OrthonormalBasis ι ℝ E) (a : ℕ → ι → ℝ) (delta : ℝ)
    (hdeltaSpectrum : ∀ n : ℕ, ∀ i : ι, delta ≤ a n i)
    (S : ContinuousLinearMapTaylorStrongLimitData
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
      ((S.limitResolvent mu -
        continuousLinearMapTaylorPartialSum S.limitResolvent lambda mu
          (resolventTaylorClosedBall_parameterBoxWorstCornerSharpTruncationOrder
            deltaMin lambdaMax rMax epsilonMin)) y)| < epsilon := by
  exact
    orthonormalDiagonalHamiltonianResolvent_strongLimit_taylor_matrixElement_error_abs_lt_parameterBox_unitBalls_of_worstCornerSharpTruncationOrder
      b a delta hdeltaSpectrum S hdelta hlambdaMax hrMax0 hrMaxlt
      hepsilonMin hlambda hr0 hr hepsilon le_rfl mu hmu x y hx hy

end MathlibAnalytic
end MGAP4D

end