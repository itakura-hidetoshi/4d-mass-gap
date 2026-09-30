import MGAP4D.MathlibAnalytic.ProbabilityMeasureMutualDominationL2MeanDifference
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCrossBoundaryInfluenceOperator
import Mathlib.Tactic

/-!
# Genuine L² mean-difference control for the cross-boundary one-link law

The existing cross-boundary comparison identifies exact diagonal support and
proves mutual Harnack domination of the two normalized target fiber laws.
The generic variance-sensitive theorem now upgrades that comparison to an L²
mean-difference estimate without applying a bounded-test/TV inequality to an
unbounded L² observable.

On the existing small-coupling region beta < log 3 / 16, the normalized
Harnack factor

  K = exp (8 beta)^2 = exp (16 beta)

satisfies K < 3. Hence the generic theorem gives exactly the square of the
already named cross-boundary contraction coefficient

  c_cross(beta) = 2 * (K - 1) / (K + 1).

Off the diagonal source/fiber support, the two conditional laws are literally
equal, so the mean difference is exactly zero.

This file stops at the conditional-law variance bound. Identifying those
variances with genuine joint one-link projection residuals is a separate step.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open ProbabilityTheory
open scoped ENNReal

noncomputable section

-- The measurable structure used by the cross-boundary fiber laws is declared
-- locally in their defining modules. Local instances do not propagate through
-- imports, so this consumer must install the same concrete structure before
-- applying generic MemLp/variance theorems.
local instance crossBoundaryL2MeanDifferenceSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

/-- The existing cross-boundary threshold implies that the normalized Harnack
factor entering the L² theorem is at most three. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundary_harnackFactor_le_three_of_beta_lt
    (beta : ℝ)
    (hBetaLt :
      beta <
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBetaThreshold) :
    (Real.exp (8 * beta)) ^ 2 ≤ 3 := by
  have hArg : beta * 16 < Real.log 3 := by
    dsimp [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBetaThreshold] at hBetaLt
    nlinarith
  have hThreePos : (0 : ℝ) < 3 := by norm_num
  have hExp16 : Real.exp (beta * 16) < 3 := by
    calc
      Real.exp (beta * 16) < Real.exp (Real.log 3) :=
        Real.exp_lt_exp.mpr hArg
      _ = 3 := Real.exp_log hThreePos
  have hEq : (Real.exp (8 * beta)) ^ 2 = Real.exp (beta * 16) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hEq]
  exact hExp16.le

/-- On the diagonal cross-boundary support, the difference of expectations of
an arbitrary real L² observable is bounded by the sum of the two conditional
variances with the square of the already named cross coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_L2MeanDifference_sq_le_varianceSum_diagonal
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hBetaLt :
      beta <
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBetaThreshold)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k₁ k₂ g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (phi : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hphi₁ : MemLp phi 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
        H N hN beta hbeta B target fiber fiber k₁ g₂ A))
    (hphi₂ : MemLp phi 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
        H N hN beta hbeta B target fiber fiber k₂ g₂ A)) :
    ((∫ g, phi g
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B target fiber fiber k₁ g₂ A) -
      (∫ g, phi g
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B target fiber fiber k₂ g₂ A)) ^ 2 ≤
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
        beta) ^ 2 *
        (variance phi
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
              H N hN beta hbeta B target fiber fiber k₁ g₂ A) +
          variance phi
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
              H N hN beta hbeta B target fiber fiber k₂ g₂ A)) := by
  let μ₁ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
      H N hN beta hbeta B target fiber fiber k₁ g₂ A
  let μ₂ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
      H N hN beta hbeta B target fiber fiber k₂ g₂ A
  let R : ℝ≥0∞ := ENNReal.ofReal (Real.exp (8 * beta))
  let K : ℝ := (Real.exp (8 * beta)) ^ 2
  letI : IsProbabilityMeasure μ₁ := by
    dsimp [μ₁]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_isProbabilityMeasure
        H N hN beta hbeta B target fiber fiber k₁ g₂ A
  letI : IsProbabilityMeasure μ₂ := by
    dsimp [μ₂]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_isProbabilityMeasure
        H N hN beta hbeta B target fiber fiber k₂ g₂ A
  have hCmp :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_pairwise_harnack_diagonal
      H N hN beta hbeta B target fiber k₁ k₂ g₂ A
  have hR2 : R * R = ENNReal.ofReal K := by
    dsimp [R, K]
    rw [pow_two, ENNReal.ofReal_mul (Real.exp_nonneg _)]
  have hμ12 : μ₁ ≤ ENNReal.ofReal K • μ₂ := by
    have h := hCmp.1
    change μ₁ ≤ (R * R) • μ₂ at h
    rwa [hR2] at h
  have hμ21 : μ₂ ≤ ENNReal.ofReal K • μ₁ := by
    have h := hCmp.2
    change μ₂ ≤ (R * R) • μ₁ at h
    rwa [hR2] at h
  have hExp : 1 ≤ Real.exp (8 * beta) := by
    apply Real.one_le_exp
    nlinarith
  have hK : 1 ≤ K := by
    dsimp [K]
    nlinarith [Real.exp_pos (8 * beta)]
  have hK3 : K ≤ 3 := by
    dsimp [K]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundary_harnackFactor_le_three_of_beta_lt
        beta hBetaLt
  have h :=
    probabilityMeasure_integral_difference_sq_le_variance_sum_of_pairwise_le_smul
      μ₁ μ₂ K hK hK3 hμ12 hμ21 phi hphi₁ hphi₂
  simpa [μ₁, μ₂, K,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient] using h

/-- Full exact support form of the L² cross-boundary mean-difference estimate.
A source distinct from the target fiber changes neither conditional law, hence
the squared mean difference is zero there. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_L2MeanDifference_sq_le_varianceSum_supported_on_diagonal
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hBetaLt :
      beta <
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBetaThreshold)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (k₁ k₂ g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (phi : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ)
    (hphi₁ : MemLp phi 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
        H N hN beta hbeta B target source fiber k₁ g₂ A))
    (hphi₂ : MemLp phi 2
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
        H N hN beta hbeta B target source fiber k₂ g₂ A)) :
    ((∫ g, phi g
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B target source fiber k₁ g₂ A) -
      (∫ g, phi g
        ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B target source fiber k₂ g₂ A)) ^ 2 ≤
      if source = fiber then
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
          beta) ^ 2 *
          (variance phi
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
                H N hN beta hbeta B target source fiber k₁ g₂ A) +
            variance phi
              (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
                H N hN beta hbeta B target source fiber k₂ g₂ A))
      else 0 := by
  by_cases hsf : source = fiber
  · subst source
    rw [if_pos rfl]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_L2MeanDifference_sq_le_varianceSum_diagonal
        H N hN beta hbeta hBetaLt B target fiber k₁ k₂ g₂ A phi hphi₁ hphi₂
  · have hEq :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_eq_of_source_ne_fiber
        H N hN beta hbeta B target source fiber k₁ k₂ g₂ A hsf
    rw [hEq]
    simp [hsf]

end

end MathlibAnalytic
end MGAP4D
