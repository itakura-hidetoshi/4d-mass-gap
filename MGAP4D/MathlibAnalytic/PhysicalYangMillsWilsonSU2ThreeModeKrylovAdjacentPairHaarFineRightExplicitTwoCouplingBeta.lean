import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarFineRightOrthogonalDepthLeakage
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaLipschitz
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferNormalizationFloor
import Mathlib.Tactic

/-!
# P4-Q2: explicit fine/frozen beta coupling for actual orthogonal right Krylov

PR #5312 controls the ACTUAL fine-right Krylov orthogonal component
by its one-step normalized physical vacuum defect:
  ||R(n,r)^\perp|| <= r ||S_fine u_H-u_H||.
Its genuine FROZEN beta(n) receiver residual already has a sharp
coefficient-one bound from #5311.

This unit bounds the FINE one-step vacuum defect using the ORIGINAL
unnormalized Wilson physical one-slab beta-Lipschitz theorem
  ||T_beta-T_0|| <= B_H beta,
exact beta-zero norm ||T_0||=1 and T_0 u=u, and the previously proved
finite-H minorization m_H(beta) <= ||T_beta||:

  ||S_beta u-u|| <= 2 m_H(beta)^(-1) B_H beta.

A general real-normed linear operator lemma controls the change caused
by norm normalization and does not assume u is fixed at beta>0.

Hence the true centered actual right Krylov vector satisfies
  ||R(n,r)^\perp|| <= r * 2 m_H(beta(n+1))^(-1) B_H beta(n+1).

Its original FROZEN beta(n) receiver has full-link squared energy at
most
  |Links(H)| *
    [C_H(beta(n)) * r * 2 m_H(beta(n+1))^(-1) B_H beta(n+1)]^2,
  C_H(beta) = m_H(beta)^(-2) B_H beta.

This gives explicit O_H,r(beta_frozen^2 beta_fine^2) for each fixed
finite H and depth r, not a volume-uniform Yang--Mills gap.
Neither the true physical receiver normalization nor the ground-state
posterior law is changed. No Dobrushin or additional assumptions.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

/-- Normalizing an operator by its genuine strictly positive norm
costs at most twice its perturbation relative to a norm-one reference
operator fixing the reference unit vector. This is an elementary
Hilbert-independent normed-linear estimate, using mathlib opNorm,
reverse triangle inequality, and exact inverse cancellation. -/
private theorem p4_normalized_clm_reference_step_le_two_opDifference
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T T₀ : E →L[ℝ] E) (u : E)
    (hT : 0 < ‖T‖) (hT₀ : ‖T₀‖ = 1)
    (hunit : ‖u‖ = 1) (hfix : T₀ u = u) :
    ‖‖T‖⁻¹ • T u - u‖ ≤
      2 * ‖T‖⁻¹ * ‖T - T₀‖ := by
  let a : ℝ := ‖T‖⁻¹
  have ha : 0 ≤ a := (inv_pos.mpr hT).le
  have hnormUnit : a • (‖T‖ • u) = u := by
    change ‖T‖⁻¹ • (‖T‖ • u) = u
    rw [smul_smul, inv_mul_cancel₀ hT.ne', one_smul]
  have hrepr : a • T u - u = a • (T u - ‖T‖ • u) := by
    rw [smul_sub, hnormUnit]
  have hvar : ‖(1 : ℝ) - ‖T‖‖ ≤ ‖T - T₀‖ := by
    have hvar' := abs_norm_sub_norm_le T₀ T
    rw [hT₀] at hvar'
    calc
      ‖(1 : ℝ) - ‖T‖‖ = |(1 : ℝ) - ‖T‖| := by rw [Real.norm_eq_abs]
      _ ≤ ‖T₀ - T‖ := hvar'
      _ = ‖T - T₀‖ := norm_sub_rev _ _
  have hdiff : T u - ‖T‖ • u =
      (T - T₀) u + ((1 : ℝ) - ‖T‖) • u := by
    rw [ContinuousLinearMap.sub_apply, hfix, sub_smul, one_smul]
    abel
  have hOp : ‖(T - T₀) u‖ ≤ ‖T - T₀‖ := by
    calc
      ‖(T - T₀) u‖ ≤ ‖T - T₀‖ * ‖u‖ :=
        (T - T₀).le_opNorm u
      _ = ‖T - T₀‖ := by rw [hunit, mul_one]
  have hcenter : ‖T u - ‖T‖ • u‖ ≤ 2 * ‖T - T₀‖ := by
    calc
      ‖T u - ‖T‖ • u‖ =
          ‖(T - T₀) u + ((1 : ℝ) - ‖T‖) • u‖ := by rw [hdiff]
      _ ≤ ‖(T - T₀) u‖ + ‖((1 : ℝ) - ‖T‖) • u‖ :=
        norm_add_le _ _
      _ = ‖(T - T₀) u‖ + ‖(1 : ℝ) - ‖T‖‖ := by
        rw [norm_smul, hunit, mul_one]
      _ ≤ ‖T - T₀‖ + ‖(1 : ℝ) - ‖T‖‖ :=
        add_le_add_left hOp _
      _ ≤ ‖T - T₀‖ + ‖T - T₀‖ :=
        add_le_add_right hvar _
      _ = 2 * ‖T - T₀‖ := by ring
  change ‖a • T u - u‖ ≤ 2 * a * ‖T - T₀‖
  calc
    ‖a • T u - u‖ = ‖a • (T u - ‖T‖ • u)‖ := by rw [hrepr]
    _ = a * ‖T u - ‖T‖ • u‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
    _ ≤ a * (2 * ‖T - T₀‖) :=
      mul_le_mul_of_nonneg_left hcenter ha
    _ = 2 * a * ‖T - T₀‖ := by ring

local instance p4FineExplicitTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4FineExplicitCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4FineExplicitSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4FineExplicitMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4FineExplicitBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4FineExplicitLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Explicit finite-volume one-step normalized physical vacuum
defect budget. Beta remains the coupling of THIS transfer, not a
separate frozen/posterior beta. -/
noncomputable def physicalOriginalNormalizedTransferConstantStepBetaBudget
    (H : ℕ) (beta : ℝ) : ℝ :=
  2 * (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor
      H beta)⁻¹ *
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H *
    beta

theorem physicalOriginalNormalizedTransferConstantStepBetaBudget_nonneg
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    0 ≤ physicalOriginalNormalizedTransferConstantStepBetaBudget H beta := by
  unfold physicalOriginalNormalizedTransferConstantStepBetaBudget
  have hm :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_pos H beta
  have hB :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget_nonneg H
  positivity

@[simp] theorem physicalOriginalNormalizedTransferConstantStepBetaBudget_zero
    (H : ℕ) :
    physicalOriginalNormalizedTransferConstantStepBetaBudget H 0 = 0 := by
  simp [physicalOriginalNormalizedTransferConstantStepBetaBudget]

/-- Quantitative ACTUAL normalized physical SU(N) Wilson one-slab
constant-vacuum step difference, using only original beta-Lipschitz,
the beta-zero rank-one theorem and genuine finite-H denominator.

This exact named theorem needs a larger typeclass-synthesis budget only
while elaborating the heavily nested continuous-linear-map norm.
The mathematical hypotheses and operator remain unchanged. -/
set_option synthInstance.maxHeartbeats 750000 in
theorem normalizedPhysicalOneSlabTransfer_constantUnit_stepDefect_le_beta
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) -
        periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N‖ ≤
      physicalOriginalNormalizedTransferConstantStepBetaBudget H beta := by
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let T₀ := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN 0 (by norm_num)
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let a : ℝ := ‖T‖⁻¹
  let m : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor H beta
  let B : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  have ht : 0 < ‖T‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H N hN beta hbeta
  have ht₀ : ‖T₀‖ = 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_zero_norm
      H N hN
  have hu : ‖u‖ = 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_norm H N
  have hfix : T₀ u = u :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_zero_constantUnit
      H N hN
  have hstep : ‖S u - u‖ ≤ (2 * a) * ‖T - T₀‖ := by
    change ‖‖T‖⁻¹ • T u - u‖ ≤ (2 * ‖T‖⁻¹) * ‖T - T₀‖
    simpa only [mul_assoc] using
      (p4_normalized_clm_reference_step_le_two_opDifference
        T T₀ u ht ht₀ hu hfix)
  have hLip : ‖T - T₀‖ ≤ B * beta := by
    simpa [T, T₀, B, Real.norm_eq_abs, abs_of_nonneg hbeta] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_sub_le_beta
        H N hN 0 beta (by norm_num) hbeta)
  have hInv : a ≤ m⁻¹ := by
    simpa only [a, T, m] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferNorm_inv_le_globalMinorizationFloor_inv
        H N hN beta hbeta)
  have hm : 0 < m :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_pos H beta
  have hScale : 2 * a ≤ 2 * m⁻¹ :=
    mul_le_mul_of_nonneg_left hInv (by norm_num)
  have hDiffNonneg : 0 ≤ ‖T - T₀‖ := norm_nonneg (T - T₀)
  change ‖S u - u‖ ≤ physicalOriginalNormalizedTransferConstantStepBetaBudget H beta
  calc
    ‖S u - u‖ ≤ (2 * a) * ‖T - T₀‖ := hstep
    _ ≤ (2 * m⁻¹) * ‖T - T₀‖ :=
      mul_le_mul_of_nonneg_right hScale hDiffNonneg
    _ ≤ (2 * m⁻¹) * (B * beta) :=
      mul_le_mul_of_nonneg_left hLip (by positivity)
    _ = physicalOriginalNormalizedTransferConstantStepBetaBudget H beta := by
      dsimp [physicalOriginalNormalizedTransferConstantStepBetaBudget, m, B]
      ring

/-- Original fine-right Krylov: explicit O_H(r beta_fine) orthogonal
leakage from the actual nonzero-beta normalized physical transfer. -/
theorem fineRightConstantOrthogonalKrylovInput_norm_le_explicitFineBeta
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) :
    ‖fineRightConstantOrthogonalKrylovInput
        (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
        n r‖ ≤
      (r : ℝ) *
        physicalOriginalNormalizedTransferConstantStepBetaBudget
          (halfExtent (n + 1)) (beta (n + 1)) := by
  have hdepth :=
    fineRightConstantOrthogonalKrylovInput_norm_le_depth_stepDefect
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r
  have hstep :=
    normalizedPhysicalOneSlabTransfer_constantUnit_stepDefect_le_beta
      (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
      (beta (n + 1)) (hbeta (n + 1))
  exact hdepth.trans
    (mul_le_mul_of_nonneg_left hstep (Nat.cast_nonneg r))

/-- Actual two-coupling P4-Q2 theorem: the fine-right input is centered
in the original physical space, its fine beta(n+1) varies independently
from the original frozen beta(n) receiver/posterior. Explicit
finite-volume O_H,r(beta_frozen² beta_fine²), with honest link count
and both finite-H Wilson minorization denominators. -/
theorem fineRightConstantOrthogonalKrylovInput_frozenEnergy_le_explicitTwoBeta
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ} {hbeta : ∀ n, 0 ≤ beta n}
    (n r : ℕ) :
    physicalPairHaarReceiverBetaZeroDriftFullLinkEnergy
        (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
        (beta n) (hbeta n)
        (fineRightConstantOrthogonalKrylovInput
          (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
          n r) ≤
      (Fintype.card
        (PeriodicHypercubicEvenSpatialSliceLink (halfExtent (n + 1))) : ℝ) *
      (physicalOriginalOrthogonalReceiverBetaLipschitzBudget
          (halfExtent (n + 1)) (beta n) *
        ((r : ℝ) *
          physicalOriginalNormalizedTransferConstantStepBetaBudget
            (halfExtent (n + 1)) (beta (n + 1)))) ^ 2 := by
  let H := halfExtent (n + 1)
  let C := physicalOriginalOrthogonalReceiverBetaLipschitzBudget H (beta n)
  let M := physicalOriginalNormalizedTransferConstantStepBetaBudget H (beta (n + 1))
  let δ : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          H 2 specialUnitaryTwoWilsonRankPositive
          (beta (n + 1)) (hbeta (n + 1))
          (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2) -
        periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2‖
  have hOld :=
    fineRightConstantOrthogonalKrylovInput_frozenReceiverEnergy_le_depth
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta) n r
  have hOne : δ ≤ M :=
    normalizedPhysicalOneSlabTransfer_constantUnit_stepDefect_le_beta
      H 2 specialUnitaryTwoWilsonRankPositive
      (beta (n + 1)) (hbeta (n + 1))
  have hC : 0 ≤ C :=
    physicalOriginalOrthogonalReceiverBetaLipschitzBudget_nonneg H (beta n) (hbeta n)
  have hr : 0 ≤ (r : ℝ) := Nat.cast_nonneg _
  have hR : (r : ℝ) * δ ≤ (r : ℝ) * M :=
    mul_le_mul_of_nonneg_left hOne hr
  have hScaled : C * ((r : ℝ) * δ) ≤ C * ((r : ℝ) * M) :=
    mul_le_mul_of_nonneg_left hR hC
  have hScaledNonneg : 0 ≤ C * ((r : ℝ) * δ) :=
    mul_nonneg hC (mul_nonneg hr (norm_nonneg _))
  have hSq : (C * ((r : ℝ) * δ)) ^ 2 ≤
      (C * ((r : ℝ) * M)) ^ 2 :=
    pow_le_pow_left₀ hScaledNonneg hScaled 2
  exact hOld.trans
    (mul_le_mul_of_nonneg_left hSq (Nat.cast_nonneg _))

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
