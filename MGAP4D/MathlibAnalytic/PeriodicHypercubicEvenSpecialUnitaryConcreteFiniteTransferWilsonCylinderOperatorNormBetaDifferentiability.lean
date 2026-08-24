import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryConcreteFiniteTransferWilsonCylinderOperatorNormBetaDerivative
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open Filter
open scoped InnerProductSpace Topology

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

/-- Difference-quotient error for the physical transfer family.  At the base
point itself it is set to zero; away from the base point it is exactly

  (T_gamma - T_beta) / (gamma - beta) + O_cyl,beta,

so convergence to zero is operator-norm differentiability with derivative
`- O_cyl,beta`. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotientError
    (H N : ℕ)
    (hN : 0 < N)
    (beta gamma : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling) :
    PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N →L[ℝ]
      PeriodicHypercubicEvenSpecialUnitaryTransferWordPhysicalHilbert H N :=
  if h : gamma = beta then
    0
  else
    (gamma.1 - beta.1)⁻¹ •
        (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferFamily
            H N hN gamma -
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferFamily
            H N hN beta) +
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionFamily
        H N hN beta

/-- Away from the base coupling, the difference-quotient error is precisely the
quadratic remainder divided by the coupling increment. -/
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
  simp [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotientError,
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferFamily,
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionFamily,
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaRemainderOperator,
    h, hsub, smul_add, smul_smul]

/-- Quantitative difference-quotient estimate.  The quadratic operator remainder
from the previous layer becomes a linear error after division by the coupling
increment. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotientError_norm_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta gamma : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotientError
        H N hN beta gamma‖ ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
          H N ^ 2 * ‖gamma.1 - beta.1‖ := by
  by_cases h : gamma = beta
  · subst gamma
    simp [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotientError]
  · rw [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotientError_eq_inv_smul_remainder
      H N hN beta gamma h]
    have hval : gamma.1 ≠ beta.1 := by
      intro hval
      apply h
      exact Subtype.ext hval
    have hsub : gamma.1 - beta.1 ≠ 0 := sub_ne_zero.mpr hval
    have hnorm : ‖gamma.1 - beta.1‖ ≠ 0 := norm_ne_zero_iff.mpr hsub
    have hR :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaRemainderOperator_norm_le
        H N hN beta.1 beta.2 gamma.1 gamma.2
    calc
      ‖(gamma.1 - beta.1)⁻¹ •
          periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaRemainderOperator
            H N hN beta.1 beta.2 gamma.1 gamma.2‖ =
          ‖(gamma.1 - beta.1)⁻¹‖ *
            ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaRemainderOperator
              H N hN beta.1 beta.2 gamma.1 gamma.2‖ := by
        rw [norm_smul]
      _ ≤ ‖(gamma.1 - beta.1)⁻¹‖ *
          (periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
              H N ^ 2 * ‖gamma.1 - beta.1‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hR (norm_nonneg _)
      _ = periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
            H N ^ 2 * ‖gamma.1 - beta.1‖ := by
        rw [norm_inv]
        field_simp [hnorm]
        ring

/-- Explicit off-diagonal quotient form of the previous estimate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotient_norm_le
    (H N : ℕ)
    (hN : 0 < N)
    (beta gamma : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling)
    (h : gamma ≠ beta) :
    ‖(gamma.1 - beta.1)⁻¹ •
          (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferFamily
              H N hN gamma -
            periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferFamily
              H N hN beta) +
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionFamily
          H N hN beta‖ ≤
      periodicHypercubicEvenSpecialUnitaryPositiveHalfCylinderTemporalGaugePathActionUniformBound
          H N ^ 2 * ‖gamma.1 - beta.1‖ := by
  simpa [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotientError,
    h] using
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotientError_norm_le
      H N hN beta gamma

/-- The difference-quotient error converges to zero in operator norm on the
actual nonnegative coupling space.  At beta = 0 this is the right derivative;
at every beta > 0 it is the ordinary interior operator-norm derivative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotientError_tendsto_zero
    (H N : ℕ)
    (hN : 0 < N)
    (beta : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling) :
    Tendsto
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotientError
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
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotientError_norm_le
        H N hN beta gamma
    change
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotientError
          H N hN beta gamma‖ ≤ B * ‖gamma.1 - beta.1‖ at herr
    rw [hBzero, zero_mul] at herr
    have hnormzero :
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotientError
            H N hN beta gamma‖ = 0 :=
      le_antisymm herr (norm_nonneg _)
    have hzero :
        periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotientError
            H N hN beta gamma = 0 :=
      norm_eq_zero.mp hnormzero
    simpa [hzero] using hepsilon
  · have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hBzero)
    refine ⟨epsilon / B, div_pos hepsilon hBpos, ?_⟩
    intro gamma hdist
    have hdist' : ‖gamma.1 - beta.1‖ < epsilon / B := by
      simpa [Real.dist_eq] using hdist
    have herr :=
      periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotientError_norm_le
        H N hN beta gamma
    change
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotientError
          H N hN beta gamma‖ ≤ B * ‖gamma.1 - beta.1‖ at herr
    have hmul : B * ‖gamma.1 - beta.1‖ < B * (epsilon / B) :=
      mul_lt_mul_of_pos_left hdist' hBpos
    have hcancel : B * (epsilon / B) = epsilon := by
      field_simp [ne_of_gt hBpos]
    have hnormlt :
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotientError
            H N hN beta gamma‖ < epsilon :=
      herr.trans_lt (by simpa [hcancel] using hmul)
    simpa [dist_zero_right] using hnormlt

/-- Operator-norm derivative on the nonnegative coupling domain.  The quotient
is evaluated only on the physical half-line; the value at the base point is
irrelevant to the limit and is set to zero. -/
def periodicHypercubicEvenSpecialUnitaryHasNonnegativeOperatorNormDerivAt
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E]
    (F : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling → E)
    (D : E)
    (beta : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling) : Prop :=
  Tendsto
    (fun gamma =>
      if h : gamma = beta then
        0
      else
        (gamma.1 - beta.1)⁻¹ • (F gamma - F beta) - D)
    (𝓝 beta)
    (𝓝 0)

/-- Main operator-norm differentiability theorem.  On the genuine physical
coupling half-line, the derivative of the complete positive-half transfer
operator is exactly minus the summed Wilson cylinder-action insertion
operator. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransfer_hasNonnegativeOperatorNormDerivAt
    (H N : ℕ)
    (hN : 0 < N)
    (beta : PeriodicHypercubicEvenSpecialUnitaryNonnegativeWilsonCoupling) :
    periodicHypercubicEvenSpecialUnitaryHasNonnegativeOperatorNormDerivAt
      (periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferFamily H N hN)
      (-periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderWilsonActionFamily H N hN beta)
      beta := by
  unfold periodicHypercubicEvenSpecialUnitaryHasNonnegativeOperatorNormDerivAt
  simpa [periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotientError,
    sub_neg_eq_add] using
    periodicHypercubicEvenSpecialUnitaryPhysicalPositiveHalfCylinderTransferBetaDifferenceQuotientError_tendsto_zero
      H N hN beta

end

end MathlibAnalytic
end MGAP4D
