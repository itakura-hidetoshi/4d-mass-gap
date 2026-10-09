import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarUncenteredUnitVacuumBridge
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarFineRightExplicitTwoCouplingBeta
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferBetaLipschitz
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferNormalizationFloor
import Mathlib.Tactic

/-!
# P4-Q2: original positive-beta unit receiver variation in the true Haar carrier

PR #5316 identified an honest obstruction to the UN-CENTERED Krylov Gram
bound, namely the original physical constant-input receiver beta-zero drift
  delta_beta = V_beta u_H - V_0 u_H.
Its norm must not be confused with the transported original Wilson vacuum
conditional-expectation energy.

The original signed receiver has a single right-coordinate pullback under
the true normalized product-Haar measure. Since that pullback is an exact
linear isometry, two receiver norms can be compared without taking an
unproved supremum of any Wilson half-density:
  ||V_gamma f - V_beta f||
   = ||lambda_gamma^(-1) S_gamma f
         - lambda_beta^(-1) S_beta f||_(physical Haar L2).

At the exact beta-zero rank-one reference u_H, lambda_0=1 and S_0 u_H=u_H:
  ||V_beta u_H - V_0 u_H||
   = ||lambda_beta^(-1) S_beta u_H-u_H||.

Using the genuine finite-volume beta-Lipschitz theorem for the unnormalized
physical transfer, the exact beta-zero transfer normalization, the positive
Wilson global minorization m_H(beta), and the #5313 normalized physical
unit-step theorem, obtain a concrete finite-H O(beta) bound

  ||V_beta u_H - V_0 u_H||
    <= m_H(beta)^(-1) *
         ( M_H(beta) + B_H beta ),

where M_H(beta)=2m_H(beta)^(-1)B_H beta.

There is NO volume-uniform lower bound for m_H(beta), no new posterior,
no Dobrushin, no fictitious receiver normalization and no continuum gap.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

local instance p4UnitVariationTopologicalGroup (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N
local instance p4UnitVariationCompactSpace (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N
local instance p4UnitVariationSecondCountable (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N
local instance p4UnitVariationMeasurableSpace (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N
local instance p4UnitVariationBorelSpace (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N
local instance p4UnitVariationLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The ORIGINAL pair-Haar right-coordinate pullback is exactly isometric
for receiver differences at any two couplings. The physical input f is the
same and no posterior measure is replaced; both receiver vectors are in
the beta-INDEPENDENT original pair-Haar carrier. -/
theorem normalizedPhysicalOneSlabPairHaarReceiver_sub_norm_eq_scaledTransferDifference
    (H N : ℕ) (hN : 0 < N)
    (beta gamma : ℝ) (hbeta : 0 ≤ beta) (hgamma : 0 ≤ gamma)
    (f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
    ‖normalizedPhysicalOneSlabPairHaarReceiver H N hN gamma hgamma f -
        normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f‖ =
      ‖(‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN gamma hgamma‖⁻¹) •
          periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
            H N hN gamma hgamma f -
        (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖⁻¹) •
          periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
            H N hN beta hbeta f‖ := by
  let μ := periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N
  let μP := periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
  let hSnd := spatialSlicePairHaar_snd_measurePreserving H N
  let J : Lp ℝ 2 μ →ₗᵢ[ℝ] Lp ℝ 2 μP :=
    Lp.compMeasurePreservingₗᵢ ℝ Prod.snd hSnd
  let Sγ := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H N hN gamma hgamma
  let Sβ := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let aγ : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN gamma hgamma‖⁻¹
  let aβ : ℝ :=
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
      H N hN beta hbeta‖⁻¹
  let xγ : Lp ℝ 2 μ :=
    ((Sγ f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
      Lp ℝ 2 μ)
  let xβ : Lp ℝ 2 μ :=
    ((Sβ f : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N) :
      Lp ℝ 2 μ)
  have hγ :
      normalizedPhysicalOneSlabPairHaarReceiver H N hN gamma hgamma f =
        aγ • J xγ := rfl
  have hβ :
      normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f =
        aβ • J xβ := rfl
  calc
    ‖normalizedPhysicalOneSlabPairHaarReceiver H N hN gamma hgamma f -
        normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta f‖ =
        ‖aγ • J xγ - aβ • J xβ‖ := by rw [hγ, hβ]
    _ = ‖J (aγ • xγ - aβ • xβ)‖ := by
      rw [map_sub, map_smul, map_smul]
    _ = ‖aγ • xγ - aβ • xβ‖ := J.norm_map _
    _ = ‖aγ • Sγ f - aβ • Sβ f‖ := rfl

/-- Exactly at beta=0 the original normalized transfer fixes the
physical constant unit and its *unnormalized* norm is one. -/
theorem normalizedPhysicalOneSlabPairHaarReceiver_unit_sub_zero_norm_eq_scaledTransfer
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) -
      normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num)
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N)‖ =
      ‖(‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN beta hbeta‖⁻¹) •
        periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          H N hN beta hbeta
          (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) -
        periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N‖ := by
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N
  have hS0 :
      periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          H N hN 0 (by norm_num) u = u :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_zero_constantUnit
      H N hN
  have hT0 :
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H N hN 0 (by norm_num)‖ = 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_zero_norm H N hN
  have hNorm :=
    normalizedPhysicalOneSlabPairHaarReceiver_sub_norm_eq_scaledTransferDifference
      H N hN 0 beta (by norm_num) hbeta u
  rw [hS0, hT0, inv_one, one_smul] at hNorm
  exact hNorm

/-- Finite-H ORIGINAL Wilson unit receiver beta-variation coefficient,
retaining the true physical inverse top norm via the global floor. -/
noncomputable def physicalOriginalUnitReceiverBetaVariationBudget
    (H : ℕ) (beta : ℝ) : ℝ :=
  let m :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor H beta
  let B :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  m⁻¹ * (physicalOriginalNormalizedTransferConstantStepBetaBudget H beta + B * beta)

theorem physicalOriginalUnitReceiverBetaVariationBudget_nonneg
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    0 ≤ physicalOriginalUnitReceiverBetaVariationBudget H beta := by
  unfold physicalOriginalUnitReceiverBetaVariationBudget
  have hm :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_pos H beta
  have hM :=
    physicalOriginalNormalizedTransferConstantStepBetaBudget_nonneg H beta hbeta
  have hB :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget_nonneg H
  positivity

@[simp] theorem physicalOriginalUnitReceiverBetaVariationBudget_zero (H : ℕ) :
    physicalOriginalUnitReceiverBetaVariationBudget H 0 = 0 := by
  simp [physicalOriginalUnitReceiverBetaVariationBudget]

/-- Original positive-beta physical constant-receiver drift is O_H(beta),
using #5313 original normalized Wilson transfer step and its genuine
positive finite-volume denominator. Not a volume-uniform estimate. -/
theorem normalizedPhysicalOneSlabPairHaarReceiver_unit_sub_zero_norm_le_explicitBeta
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N) -
      normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num)
        (periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N)‖ ≤
      physicalOriginalUnitReceiverBetaVariationBudget H beta := by
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H N
  let T := periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let S := periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H N hN beta hbeta
  let lam : ℝ := ‖T‖
  let a : ℝ := lam⁻¹
  let m : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor H beta
  let B : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  let M : ℝ := physicalOriginalNormalizedTransferConstantStepBetaBudget H beta
  have hlam : 0 < lam :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H N hN beta hbeta
  have ha : 0 ≤ a := (inv_pos.mpr hlam).le
  have halam : a * lam = 1 := inv_mul_cancel₀ hlam.ne'
  have hNorm :
      ‖normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta u -
        normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) u‖ =
      ‖a • S u - u‖ := by
    simpa only [u, T, S, lam, a] using
      (normalizedPhysicalOneSlabPairHaarReceiver_unit_sub_zero_norm_eq_scaledTransfer
        H N hN beta hbeta)
  have hStep : ‖S u - u‖ ≤ M :=
    normalizedPhysicalOneSlabTransfer_constantUnit_stepDefect_le_beta
      H N hN beta hbeta
  have hNormVariation : ‖lam - 1‖ ≤ B * beta := by
    have h :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_norm_sub_le_beta
        H N hN 0 beta (by norm_num) hbeta
    simpa [lam, T, B,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_zero_norm,
      Real.norm_eq_abs, abs_of_nonneg hbeta] using h
  have hInv : a ≤ m⁻¹ := by
    simpa only [a, lam, T, m] using
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferNorm_inv_le_globalMinorizationFloor_inv
        H N hN beta hbeta)
  have hm : 0 < m :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalMinorizationFloor_pos H beta
  have hM : 0 ≤ M := physicalOriginalNormalizedTransferConstantStepBetaBudget_nonneg H beta hbeta
  have hB : 0 ≤ B :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget_nonneg H
  have hsumNonneg : 0 ≤ M + B * beta :=
    add_nonneg hM (mul_nonneg hB hbeta)
  have hu : ‖u‖ = 1 := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_norm H N
  have hSplit : S u - lam • u = (S u - u) + ((1 : ℝ) - lam) • u := by
    module
  have hSplitNorm :
      ‖S u - lam • u‖ ≤ M + B * beta := by
    calc
      ‖S u - lam • u‖ =
          ‖(S u - u) + ((1 : ℝ) - lam) • u‖ := by rw [hSplit]
      _ ≤ ‖S u - u‖ + ‖((1 : ℝ) - lam) • u‖ :=
        norm_add_le _ _
      _ = ‖S u - u‖ + ‖lam - 1‖ := by
        rw [norm_smul, hu, mul_one, norm_sub_rev]
      _ ≤ M + B * beta := add_le_add hStep hNormVariation
  have hScaled : a • S u - u = a • (S u - lam • u) := by
    rw [smul_sub, smul_smul, halam, one_smul]
  change ‖normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta u -
    normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) u‖ ≤
    m⁻¹ * (M + B * beta)
  calc
    ‖normalizedPhysicalOneSlabPairHaarReceiver H N hN beta hbeta u -
      normalizedPhysicalOneSlabPairHaarReceiver H N hN 0 (by norm_num) u‖ =
        ‖a • S u - u‖ := hNorm
    _ = ‖a • (S u - lam • u)‖ := by rw [hScaled]
    _ = a * ‖S u - lam • u‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
    _ ≤ a * (M + B * beta) :=
      mul_le_mul_of_nonneg_left hSplitNorm ha
    _ ≤ m⁻¹ * (M + B * beta) :=
      mul_le_mul_of_nonneg_right hInv hsumNonneg

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
