import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTopOrthogonalScaleCommonBoundaryDecay
import Mathlib.Tactic

/-!
# Strong-limit preservation of the uniform top-orthogonal contraction

PR #4984 places every finite physical top-orthogonal transfer trajectory in one
common interacting infinite-product boundary L2 carrier and proves the exact
scale-independent geometric estimate

  ||I_n (R_n^k x_n)|| <= q0^k ||I_n x_n||,

where q0 = 3071/3072.

This file closes the next abstract H1 descent step.

First, whenever a sequence of embedded finite initial vectors and the
corresponding embedded evolved vectors both converge strongly in the common
carrier, the same q0^k estimate survives in the limit.

Second, we package an optional limiting normed space E, an isometric embedding
of E into the common carrier, finite approximants for every x : E, and a
bounded limit operator.  If both the initial and evolved embedded approximants
converge to the corresponding embedded limit vectors, then the limiting
operator inherits the exact same q0^k operator-norm bound.

For one step this yields

  ||T|| <= 3071 / 3072

and therefore

  1 / 3072 <= 1 - ||T||.

No finite OS vacuum identification, no scale nesting, no projective
coarse-graining of periodic Gibbs laws, and no existence claim for the limiting
operator are introduced.  Construction of the strong-limit data is the next
model-facing H1 compatibility boundary.
-/

namespace MGAP4D
namespace MathlibAnalytic

open Filter Topology
open scoped InnerProductSpace

noncomputable section

section ScalingFamily

variable
    (halfExtent : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)

/-- Any strongly convergent family of finite top-orthogonal trajectories in
the #4984 common carrier inherits the exact same q0^k norm bound. -/
theorem
    periodicHypercubicEvenSpecialUnitary_topOrthogonalScaleCommonBoundaryTrajectory_limit_norm_le
    (s : ℝ) (hs : 8 < s)
    (hcut :
      ∀ n : ℕ,
        beta n ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
            s hs)
    (k : ℕ) (hk : 0 < k)
    (x :
      (n : ℕ) →
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
          (halfExtent n) N hN (beta n) (hbeta n))
    (xLimit yLimit :
      PeriodicHypercubicEvenSpecialUnitaryTopOrthogonalScaleCommonBoundaryL2
        halfExtent N hN beta hbeta)
    (hInitial :
      Tendsto
        (fun n =>
          periodicHypercubicEvenSpecialUnitaryTopOrthogonalToScaleCommonBoundaryLinearIsometry
            halfExtent N hN beta hbeta n (x n))
        atTop
        (𝓝 xLimit))
    (hEvolved :
      Tendsto
        (fun n =>
          periodicHypercubicEvenSpecialUnitaryTopOrthogonalScaleCommonBoundaryTrajectory
            halfExtent N hN beta hbeta n k (x n))
        atTop
        (𝓝 yLimit)) :
    ‖yLimit‖ ≤
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ k *
        ‖xLimit‖ := by
  have hLeft :
      Tendsto
        (fun n =>
          ‖periodicHypercubicEvenSpecialUnitaryTopOrthogonalScaleCommonBoundaryTrajectory
            halfExtent N hN beta hbeta n k (x n)‖)
        atTop
        (𝓝 ‖yLimit‖) :=
    hEvolved.norm
  have hRight :
      Tendsto
        (fun n =>
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ k *
            ‖periodicHypercubicEvenSpecialUnitaryTopOrthogonalToScaleCommonBoundaryLinearIsometry
              halfExtent N hN beta hbeta n (x n)‖)
        atTop
        (𝓝
          (GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ k *
            ‖xLimit‖)) :=
    tendsto_const_nhds.mul hInitial.norm
  apply le_of_tendsto_of_tendsto hLeft hRight
  exact Filter.Eventually.of_forall fun n =>
    periodicHypercubicEvenSpecialUnitary_topOrthogonalScaleCommonBoundaryTrajectory_norm_le
      halfExtent N hN beta hbeta s hs hcut n k hk (x n)

/-- Strong-limit compatibility data for one fixed positive natural transfer
power.

The approximants may live in different finite top-orthogonal spaces.  Their
images and evolved images are compared only after the exact #4984 isometric
embedding into the common interacting boundary carrier. -/
structure
    PeriodicHypercubicEvenSpecialUnitaryTopOrthogonalScaleCommonBoundaryStrongLimitData
    (E : Type*)
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (k : ℕ) where
  limitEmbedding :
    E →ₗᵢ[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryTopOrthogonalScaleCommonBoundaryL2
        halfExtent N hN beta hbeta
  approximate :
    (x : E) →
      (n : ℕ) →
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
          (halfExtent n) N hN (beta n) (hbeta n)
  limitOperator : E →L[ℝ] E
  initial_tendsto :
    ∀ x : E,
      Tendsto
        (fun n =>
          periodicHypercubicEvenSpecialUnitaryTopOrthogonalToScaleCommonBoundaryLinearIsometry
            halfExtent N hN beta hbeta n (approximate x n))
        atTop
        (𝓝 (limitEmbedding x))
  evolved_tendsto :
    ∀ x : E,
      Tendsto
        (fun n =>
          periodicHypercubicEvenSpecialUnitaryTopOrthogonalScaleCommonBoundaryTrajectory
            halfExtent N hN beta hbeta n k (approximate x n))
        atTop
        (𝓝 (limitEmbedding (limitOperator x)))

namespace PeriodicHypercubicEvenSpecialUnitaryTopOrthogonalScaleCommonBoundaryStrongLimitData

variable
    {halfExtent : ℕ → ℕ}
    {N : ℕ} {hN : 0 < N}
    [Nontrivial (Matrix.specialUnitaryGroup (Fin N) ℂ)]
    {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}

/-- The limiting operator inherits the exact q0^k pointwise norm bound. -/
theorem limitOperator_apply_norm_le
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    {k : ℕ}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryTopOrthogonalScaleCommonBoundaryStrongLimitData
        halfExtent N hN beta hbeta E k)
    (s : ℝ) (hs : 8 < s)
    (hcut :
      ∀ n : ℕ,
        beta n ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
            s hs)
    (hk : 0 < k)
    (x : E) :
    ‖D.limitOperator x‖ ≤
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ k *
        ‖x‖ := by
  have h :=
    periodicHypercubicEvenSpecialUnitary_topOrthogonalScaleCommonBoundaryTrajectory_limit_norm_le
      halfExtent N hN beta hbeta s hs hcut k hk
      (D.approximate x)
      (D.limitEmbedding x)
      (D.limitEmbedding (D.limitOperator x))
      (D.initial_tendsto x)
      (D.evolved_tendsto x)
  have hInitialNorm :
      ‖D.limitEmbedding x‖ = ‖x‖ :=
    D.limitEmbedding.norm_map x
  have hEvolvedNorm :
      ‖D.limitEmbedding (D.limitOperator x)‖ = ‖D.limitOperator x‖ :=
    D.limitEmbedding.norm_map (D.limitOperator x)
  rw [hEvolvedNorm, hInitialNorm] at h
  exact h

/-- Operator-norm version of the inherited q0^k strong-limit bound. -/
theorem limitOperator_norm_le
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    {k : ℕ}
    (D :
      PeriodicHypercubicEvenSpecialUnitaryTopOrthogonalScaleCommonBoundaryStrongLimitData
        halfExtent N hN beta hbeta E k)
    (s : ℝ) (hs : 8 < s)
    (hcut :
      ∀ n : ℕ,
        beta n ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
            s hs)
    (hk : 0 < k) :
    ‖D.limitOperator‖ ≤
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor ^ k := by
  apply ContinuousLinearMap.opNorm_le_bound
  · exact pow_nonneg
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor_nonneg
      k
  · intro x
    exact D.limitOperator_apply_norm_le s hs hcut hk x

/-- The one-step specialization of the H1 strong-limit compatibility data. -/
abbrev OneStep
    (E : Type*)
    [NormedAddCommGroup E]
    [NormedSpace ℝ E] :=
  PeriodicHypercubicEvenSpecialUnitaryTopOrthogonalScaleCommonBoundaryStrongLimitData
    halfExtent N hN beta hbeta E 1

/-- Every one-step strong limit satisfying the explicit #4984 compatibility
inherits the same strict contraction factor 3071/3072. -/
theorem OneStep.limitOperator_norm_le_uniformFactor
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (D : OneStep (halfExtent := halfExtent) (N := N) (hN := hN)
      (beta := beta) (hbeta := hbeta) E)
    (s : ℝ) (hs : 8 < s)
    (hcut :
      ∀ n : ℕ,
        beta n ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
            s hs) :
    ‖D.limitOperator‖ ≤
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor := by
  simpa using D.limitOperator_norm_le s hs hcut (by norm_num : 0 < (1 : ℕ))

/-- Explicit one-step gap preservation on any compatible strong-limit carrier. -/
theorem OneStep.one_div_3072_le_one_sub_limitOperator_norm
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (D : OneStep (halfExtent := halfExtent) (N := N) (hN := hN)
      (beta := beta) (hbeta := hbeta) E)
    (s : ℝ) (hs : 8 < s)
    (hcut :
      ∀ n : ℕ,
        beta n ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
            s hs) :
    (1 : ℝ) / 3072 ≤ 1 - ‖D.limitOperator‖ := by
  have h := D.limitOperator_norm_le_uniformFactor s hs hcut
  unfold
    GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor
    at h
  norm_num at h ⊢
  linarith

/-- In particular the compatible one-step strong limit is a strict
contraction. -/
theorem OneStep.limitOperator_norm_lt_one
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (D : OneStep (halfExtent := halfExtent) (N := N) (hN := hN)
      (beta := beta) (hbeta := hbeta) E)
    (s : ℝ) (hs : 8 < s)
    (hcut :
      ∀ n : ℕ,
        beta n ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
            s hs) :
    ‖D.limitOperator‖ < 1 := by
  have h := D.limitOperator_norm_le_uniformFactor s hs hcut
  exact lt_of_le_of_lt h
    GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformTopOrthogonalContractionFactor_lt_one

end PeriodicHypercubicEvenSpecialUnitaryTopOrthogonalScaleCommonBoundaryStrongLimitData

end ScalingFamily

end

end MathlibAnalytic
end MGAP4D
