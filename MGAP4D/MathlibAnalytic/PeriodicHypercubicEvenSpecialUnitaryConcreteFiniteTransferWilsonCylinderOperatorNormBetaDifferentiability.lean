import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryConcreteFiniteTransferWilsonCylinderOperatorNormBetaDerivative
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter
open scoped Topology

noncomputable section

/-- The physical Wilson coupling half-line, kept as an actual subtype so no
negative-coupling extension is introduced merely for differential calculus. -/
abbrev PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling :=
  { beta : ℝ // 0 ≤ beta }

/-- The complete positive-half physical transfer family on the genuine
nonnegative Wilson-coupling domain. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferFamily
    (H N : ℕ)
    (hN : 0 < N)
    (beta : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling) :
    PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N :=
  periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
    H N hN beta.1 beta.2

/-- The summed Wilson cylinder-action insertion operator, as a family on the
same nonnegative coupling domain. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionFamily
    (H N : ℕ)
    (hN : 0 < N)
    (beta : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling) :
    PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N :=
  periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator
    H N hN beta.1 beta.2

/-- The off-diagonal difference-quotient error operator

  (T_gamma - T_beta) / (gamma - beta) + O_cyl,beta.

For `gamma ≠ beta`, convergence of its operator norm to zero is exactly
operator-norm differentiability with derivative `- O_cyl,beta`. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotientError
    (H N : ℕ)
    (hN : 0 < N)
    (beta gamma : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling) :
    PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N :=
  (gamma.1 - beta.1)⁻¹ •
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferFamily
          H N hN gamma -
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferFamily
          H N hN beta) +
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionFamily
      H N hN beta

/-- Away from the base coupling, the difference-quotient error is precisely the
quadratic remainder divided by the coupling increment.  The proof is reduced
pointwise before using scalar-module identities, avoiding generic operator-space
instance search. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotientError_eq_inv_smul_remainder
    (H N : ℕ)
    (hN : 0 < N)
    (beta gamma : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling)
    (h : gamma ≠ beta) :
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotientError
        H N hN beta gamma =
      (gamma.1 - beta.1)⁻¹ •
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaRemainderOperator
          H N hN beta.1 beta.2 gamma.1 gamma.2 := by
  have hval : gamma.1 ≠ beta.1 := by
    intro hval
    apply h
    exact Subtype.ext hval
  have hsub : gamma.1 - beta.1 ≠ 0 := sub_ne_zero.mpr hval
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotientError
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferFamily
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionFamily
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaRemainderOperator
  apply ContinuousLinearMap.ext
  intro f
  change
    (gamma.1 - beta.1)⁻¹ •
          (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
              H N hN gamma.1 gamma.2 f -
            periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
              H N hN beta.1 beta.2 f) +
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator
            H N hN beta.1 beta.2 f =
      (gamma.1 - beta.1)⁻¹ •
        ((periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
              H N hN gamma.1 gamma.2 f -
            periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferOperator
              H N hN beta.1 beta.2 f) +
          (gamma.1 - beta.1) •
            periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionInsertionOperator
              H N hN beta.1 beta.2 f)
  rw [smul_add, smul_smul, inv_mul_cancel₀ hsub, one_smul]

/-- Quantitative off-diagonal difference-quotient estimate.  The proof uses
`opNorm_le_bound` and the pointwise remainder estimate, so no normed-space
structure on the operator carrier has to be inferred through the generic
`norm_smul` API. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotient_norm_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta gamma : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling)
    (h : gamma ≠ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotientError
        H N hN beta gamma‖ ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
          H N ^ 2 * ‖gamma.1 - beta.1‖ := by
  have hval : gamma.1 ≠ beta.1 := by
    intro hval
    apply h
    exact Subtype.ext hval
  have hsub : gamma.1 - beta.1 ≠ 0 := sub_ne_zero.mpr hval
  have hnorm : ‖gamma.1 - beta.1‖ ≠ 0 := norm_ne_zero_iff.mpr hsub
  apply ContinuousLinearMap.opNorm_le_bound
    (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotientError
      H N hN beta gamma)
    (by positivity)
  intro f
  rw [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotientError_eq_inv_smul_remainder
    H N hN beta gamma h]
  change
    ‖(gamma.1 - beta.1)⁻¹ •
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaRemainderOperator
          H N hN beta.1 beta.2 gamma.1 gamma.2 f‖ ≤
      (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
          H N ^ 2 * ‖gamma.1 - beta.1‖) * ‖f‖
  rw [norm_smul]
  have hR :=
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaRemainderOperator_apply_norm_le
      H N hN beta.1 beta.2 gamma.1 gamma.2 f
  calc
    ‖(gamma.1 - beta.1)⁻¹‖ *
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaRemainderOperator
          H N hN beta.1 beta.2 gamma.1 gamma.2 f‖ ≤
      ‖(gamma.1 - beta.1)⁻¹‖ *
        ((periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
            H N ^ 2 * ‖gamma.1 - beta.1‖ ^ 2) * ‖f‖) :=
      mul_le_mul_of_nonneg_left hR (norm_nonneg _)
    _ = (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
          H N ^ 2 * ‖gamma.1 - beta.1‖) * ‖f‖ := by
      rw [norm_inv]
      field_simp [hnorm]

/-- Scalar operator-norm error, totalized by assigning zero at the base point.
The diagonal value is irrelevant to the punctured difference quotient but makes
the norm-error a total real-valued function on the physical coupling half-line. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotientErrorNorm
    (H N : ℕ)
    (hN : 0 < N)
    (beta gamma : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling) : ℝ :=
  if gamma = beta then
    0
  else
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotientError
        H N hN beta gamma‖

/-- The totalized scalar error is nonnegative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotientErrorNorm_nonneg
    (H N : ℕ)
    (hN : 0 < N)
    (beta gamma : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotientErrorNorm
        H N hN beta gamma := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotientErrorNorm
  split
  · exact le_rfl
  · exact ContinuousLinearMap.opNorm_nonneg _

/-- Uniform linear control of the scalar operator-norm difference-quotient
error, including the harmless totalized diagonal value. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotientErrorNorm_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta gamma : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling) :
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotientErrorNorm
        H N hN beta gamma ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
          H N ^ 2 * ‖gamma.1 - beta.1‖ := by
  by_cases h : gamma = beta
  · subst gamma
    simp [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotientErrorNorm]
  · simpa only [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotientErrorNorm,
      if_neg h] using
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotient_norm_le
        H N hN beta gamma h

/-- The actual operator-norm difference-quotient error converges to zero on the
genuine nonnegative coupling space.  The codomain here is `ℝ`: this is precisely
convergence in operator norm, while avoiding any need to infer a metric-space
instance on the concrete operator carrier itself. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotientErrorNorm_tendsto_zero
    (H N : ℕ)
    (hN : 0 < N)
    (beta : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling) :
    Tendsto
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotientErrorNorm
        H N hN beta)
      (𝓝 beta)
      (𝓝 0) := by
  let B :=
    periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
        H N ^ 2
  have hB : 0 ≤ B := by positivity
  rw [Metric.tendsto_nhds_nhds]
  intro epsilon hepsilon
  by_cases hBzero : B = 0
  · refine ⟨1, zero_lt_one, ?_⟩
    intro gamma hdist
    have herr :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotientErrorNorm_le
        H N hN beta gamma
    change
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotientErrorNorm
          H N hN beta gamma ≤ B * ‖gamma.1 - beta.1‖ at herr
    rw [hBzero, zero_mul] at herr
    have herrnonneg :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotientErrorNorm_nonneg
        H N hN beta gamma
    have herrzero :
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotientErrorNorm
            H N hN beta gamma = 0 :=
      le_antisymm herr herrnonneg
    rw [herrzero]
    simpa using hepsilon
  · have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hBzero)
    refine ⟨epsilon / B, div_pos hepsilon hBpos, ?_⟩
    intro gamma hdist
    have hdist' : ‖gamma.1 - beta.1‖ < epsilon / B := by
      simpa [Real.dist_eq] using hdist
    have herr :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotientErrorNorm_le
        H N hN beta gamma
    change
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotientErrorNorm
          H N hN beta gamma ≤ B * ‖gamma.1 - beta.1‖ at herr
    have hmul : B * ‖gamma.1 - beta.1‖ < B * (epsilon / B) :=
      mul_lt_mul_of_pos_left hdist' hBpos
    have hcancel : B * (epsilon / B) = epsilon := by
      field_simp [ne_of_gt hBpos]
    have herrlt :
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotientErrorNorm
            H N hN beta gamma < epsilon :=
      herr.trans_lt (by simpa [hcancel] using hmul)
    have herrnonneg :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotientErrorNorm_nonneg
        H N hN beta gamma
    simpa [Real.dist_eq, abs_of_nonneg herrnonneg] using herrlt

/-- Main operator-norm differentiability theorem.  On the physical coupling
half-line,

  ‖(T_gamma - T_beta)/(gamma - beta) + O_cyl,beta‖ → 0.

Thus the derivative is exactly `- O_cyl,beta`.  At `beta = 0` this is the right
operator-norm derivative; at every `beta > 0` it is the ordinary interior
operator-norm derivative.  No negative-coupling extension is used. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransfer_hasNonnegativeOperatorNormDerivAt
    (H N : ℕ)
    (hN : 0 < N)
    (beta : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling) :
    Tendsto
      (fun gamma : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling =>
        if gamma = beta then
          0
        else
          ‖(gamma.1 - beta.1)⁻¹ •
                (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferFamily
                    H N hN gamma -
                  periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferFamily
                    H N hN beta) +
              periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionFamily
                H N hN beta‖)
      (𝓝 beta)
      (𝓝 0) := by
  simpa only [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotientErrorNorm,
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotientError] using
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotientErrorNorm_tendsto_zero
      H N hN beta

end

end MathlibAnalytic
end MGAP4D
