import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarGlobalHilbertDirectSumRayleigh
import Mathlib.Tactic

/-!
# P4-Q2-U: explicit positive-fine Wilson interval with separated H/r factors

For the ACTUAL normalized Wilson one-slab transfer, let A_H ≥ 0 be
its existing finite-volume physical action budget. On 0 ≤ t ≤ 1,

  B_H(t) = 2 exp(t A_H) A_H t ≤ C_H t,
  C_H := 2 exp(A_H) A_H.

Set L_H := the actual finite number of spatial links, gamma(b,H) the
existing signed innovation Hilbert coefficient, and E_unit(b,H)>0 the
original full-link frozen receiver energy. The explicit radius is

  delta(H,r,b) :=
    min 1 (sqrt(E_unit(b,H)) /
      (1 + r sqrt(L_H) sqrt(gamma(b,H)) C_H)).

The denominator is strictly positive. For every nonnegative actual
Wilson beta profile with frozen beta(n)>0, any 0≤beta(n+1)<delta
satisfies the P4-Q2-T physical budget and hence

  normalized_ones_Rayleigh > (r+1) E_unit(beta(n),H) / 4 > 0.

A concrete supported two-scale beta schedule using delta/2 is also
constructed. This is an explicit H- and r-dependent finite-scale
window; it is NOT a uniform-in-volume/depth or continuum mass gap.
No Dobrushin, proxy Wilson law, surrogate transfer, new axiom or sorry.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

/-- The actual Wilson physical action budget gives an explicit
local-in-fine-beta linear majorant, not an abstract continuity modulus. -/
noncomputable def physicalOriginalNormalizedTransferExpActionLinearConstant
    (H : ℕ) : ℝ :=
  2 * Real.exp
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H) *
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H

theorem physicalOriginalNormalizedTransferExpActionLinearConstant_nonneg
    (H : ℕ) :
    0 ≤ physicalOriginalNormalizedTransferExpActionLinearConstant H := by
  unfold physicalOriginalNormalizedTransferExpActionLinearConstant
  have hA :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget_nonneg H
  positivity

/-- The original physical normalized transfer defect budget satisfies
B_H(t) ≤ 2 exp(A_H) A_H t on the exact interval [0,1]. -/
theorem physicalOriginalNormalizedTransferConstantStepBetaBudget_le_expActionLinear_one
    (H : ℕ) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    GroundStatePosteriorJoint.physicalOriginalNormalizedTransferConstantStepBetaBudget H t ≤
      physicalOriginalNormalizedTransferExpActionLinearConstant H * t := by
  let A : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  have hA : 0 ≤ A :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget_nonneg H
  have hMul : t * A ≤ A := by
    calc
      t * A ≤ 1 * A := mul_le_mul_of_nonneg_right ht1 hA
      _ = A := one_mul _
  have hExp : Real.exp (t * A) ≤ Real.exp A :=
    Real.exp_le_exp.mpr hMul
  change 2 * (Real.exp (-(t * A)))⁻¹ * A * t ≤
    (2 * Real.exp A * A) * t
  rw [Real.exp_neg, inv_inv]
  calc
    2 * Real.exp (t * A) * A * t =
        (2 * A * t) * Real.exp (t * A) := by ring
    _ ≤ (2 * A * t) * Real.exp A :=
      mul_le_mul_of_nonneg_left hExp (by positivity)
    _ = (2 * Real.exp A * A) * t := by ring

/-- This radius is explicit in r, in the selected finite-H physical
action constant, and in the physical frozen receiver/innovation data. -/
noncomputable def physicalOriginalNormalizedTransferExplicitFineRadius
    (H r : ℕ) (K radius : ℝ) : ℝ :=
  min 1 (radius /
    (1 + (r : ℝ) * K *
      physicalOriginalNormalizedTransferExpActionLinearConstant H))

theorem physicalOriginalNormalizedTransferExplicitFineRadius_pos
    (H r : ℕ) (K radius : ℝ)
    (hK : 0 ≤ K) (hRadius : 0 < radius) :
    0 < physicalOriginalNormalizedTransferExplicitFineRadius H r K radius := by
  unfold physicalOriginalNormalizedTransferExplicitFineRadius
  apply lt_min (by norm_num)
  apply div_pos hRadius
  have hC := physicalOriginalNormalizedTransferExpActionLinearConstant_nonneg H
  positivity

/-- Fully explicit smallness verification using only exp monotonicity
on t≤1; in particular no epsilon-delta existence oracle is used. -/
theorem physicalOriginalNormalizedTransferExplicitFineRadius_bound
    (H r : ℕ) (K radius : ℝ)
    (hK : 0 ≤ K)
    (t : ℝ) (ht : 0 ≤ t)
    (hlt : t < physicalOriginalNormalizedTransferExplicitFineRadius H r K radius) :
    K * ((r : ℝ) *
      GroundStatePosteriorJoint.physicalOriginalNormalizedTransferConstantStepBetaBudget H t) <
      radius := by
  let C : ℝ := physicalOriginalNormalizedTransferExpActionLinearConstant H
  let Q : ℝ := (r : ℝ) * K * C
  have hC : 0 ≤ C :=
    physicalOriginalNormalizedTransferExpActionLinearConstant_nonneg H
  have hQ : 0 ≤ Q := by
    dsimp [Q]
    positivity
  have hRadiusDef :
      physicalOriginalNormalizedTransferExplicitFineRadius H r K radius =
        min 1 (radius / (1 + Q)) := rfl
  rw [hRadiusDef] at hlt
  have htOne : t ≤ 1 :=
    le_of_lt (lt_of_lt_of_le hlt (min_le_left _ _))
  have htRatio : t < radius / (1 + Q) :=
    lt_of_lt_of_le hlt (min_le_right _ _)
  have hDen : 0 < 1 + Q := by linarith
  have hAbove : (1 + Q) * t < radius := by
    calc
      (1 + Q) * t = t * (1 + Q) := mul_comm _ _
      _ < radius := (lt_div_iff₀ hDen).mp htRatio
  have hQBound : Q * t ≤ (1 + Q) * t :=
    mul_le_mul_of_nonneg_right (by linarith : Q ≤ 1 + Q) ht
  have hB :=
    physicalOriginalNormalizedTransferConstantStepBetaBudget_le_expActionLinear_one
      H t ht htOne
  calc
    K * ((r : ℝ) *
        GroundStatePosteriorJoint.physicalOriginalNormalizedTransferConstantStepBetaBudget H t) =
        (K * (r : ℝ)) *
          GroundStatePosteriorJoint.physicalOriginalNormalizedTransferConstantStepBetaBudget H t := by
      ring
    _ ≤ (K * (r : ℝ)) * (C * t) := by
      exact mul_le_mul_of_nonneg_left hB (mul_nonneg hK (Nat.cast_nonneg _))
    _ = Q * t := by dsimp [Q]; ring
    _ ≤ (1 + Q) * t := hQBound
    _ < radius := hAbove

local instance p4ExplicitRadiusGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4ExplicitRadiusCompact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4ExplicitRadiusSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4ExplicitRadiusMeasurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4ExplicitRadiusBorel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4ExplicitRadiusLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- Certified explicit physical fine-coupling radius:
 min(1, sqrt(E_unit) / (1 + r sqrt(L_H) sqrt(gamma) C_H)).
It depends only on H, r and frozen beta, not on a chosen fine schedule. -/
noncomputable def physicalOriginalGlobalQuarterEnergyExplicitFineRadius
    (H r : ℕ) (frozen : ℝ) (hFrozen : 0 ≤ frozen) : ℝ :=
  physicalOriginalNormalizedTransferExplicitFineRadius
    H r
    (Real.sqrt (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
      Real.sqrt (originalWilsonPhysicalSignedInnovationHilbertCoefficient
        H 2 specialUnitaryTwoWilsonRankPositive frozen hFrozen))
    (Real.sqrt (physicalOriginalUnitReceiverFullLinkEnergy
      H 2 specialUnitaryTwoWilsonRankPositive frozen hFrozen))

theorem physicalOriginalGlobalQuarterEnergyExplicitFineRadius_pos
    (H r : ℕ) (frozen : ℝ) (hFrozen : 0 < frozen) :
    0 < physicalOriginalGlobalQuarterEnergyExplicitFineRadius
      H r frozen (le_of_lt hFrozen) := by
  have hEnergy :=
    physicalOriginalUnitReceiverFullLinkEnergy_pos_of_beta_pos_SU2
      H frozen hFrozen
  unfold physicalOriginalGlobalQuarterEnergyExplicitFineRadius
  apply physicalOriginalNormalizedTransferExplicitFineRadius_pos
  · exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  · exact Real.sqrt_pos.mpr hEnergy

/-- The explicit radius controls the ACTUAL global posterior Hilbert
receiver error for every nonnegative beta schedule. -/
theorem fineRightKrylovPairHaarResidualGram_ones_normalizedRayleigh_gt_globalQuarterEnergy_of_explicitRadius
    {halfExtent : ℕ → ℕ} {beta : ℕ → ℝ}
    {hbeta : ∀ k, 0 ≤ beta k}
    (n r : ℕ)
    (hFine :
      beta (n + 1) <
        physicalOriginalGlobalQuarterEnergyExplicitFineRadius
          (halfExtent (n + 1)) r (beta n) (hbeta n)) :
    let H := halfExtent (n + 1)
    (((r + 1 : ℕ) : ℝ)) *
      (physicalOriginalUnitReceiverFullLinkEnergy
        H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) / 4) <
      (star (fun _ : Fin (r + 1) => (1 : ℝ)) ⬝ᵥ
        (Matrix.mulVec
          (fineRightKrylovPairHaarResidualGram
            (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
            n r)
          (fun _ : Fin (r + 1) => (1 : ℝ)))) /
        (∑ j : Fin (r + 1),
          ((fun _ : Fin (r + 1) => (1 : ℝ)) j) ^ 2) := by
  let H := halfExtent (n + 1)
  let K : ℝ :=
    Real.sqrt (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
      Real.sqrt (originalWilsonPhysicalSignedInnovationHilbertCoefficient
        H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n))
  let Eunit := physicalOriginalUnitReceiverFullLinkEnergy
    H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n)
  have hK : 0 ≤ K :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hBudget :
      K * ((r : ℝ) *
        physicalOriginalNormalizedTransferConstantStepBetaBudget H (beta (n + 1))) <
        Real.sqrt Eunit :=
    physicalOriginalNormalizedTransferExplicitFineRadius_bound
      H r K (Real.sqrt Eunit) hK
      (beta (n + 1)) (hbeta (n + 1)) hFine
  apply fineRightKrylovPairHaarResidualGram_ones_normalizedRayleigh_gt_globalQuarterEnergy
    (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
    n r
  exact hBudget

/-- The explicit radius is a concrete replacement for a mere
existence-of-delta statement; the chosen fine beta is strictly
positive and the original normalized posterior Rayleigh retains
the full physical unit-energy floor. -/
theorem fineRightKrylovPairHaarResidualGram_exists_positiveFine_explicitRadius_schedule
    (halfExtent : ℕ → ℕ) (n r : ℕ)
    (frozen : ℝ) (hFrozen : 0 < frozen) :
    ∃ (beta : ℕ → ℝ) (hbeta : ∀ k, 0 ≤ beta k),
      beta n = frozen ∧
        beta (n + 1) =
          physicalOriginalGlobalQuarterEnergyExplicitFineRadius
            (halfExtent (n + 1)) r frozen (le_of_lt hFrozen) / 2 ∧
        0 < beta (n + 1) ∧
        (∀ k, k ≠ n → k ≠ n + 1 → beta k = 0) ∧
        0 < ((r + 1 : ℕ) : ℝ) *
          (physicalOriginalUnitReceiverFullLinkEnergy
            (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
            (beta n) (hbeta n) / 4) ∧
        ((r + 1 : ℕ) : ℝ) *
          (physicalOriginalUnitReceiverFullLinkEnergy
            (halfExtent (n + 1)) 2 specialUnitaryTwoWilsonRankPositive
            (beta n) (hbeta n) / 4) <
        (star (fun _ : Fin (r + 1) => (1 : ℝ)) ⬝ᵥ
          (Matrix.mulVec
            (fineRightKrylovPairHaarResidualGram
              (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
              n r)
            (fun _ : Fin (r + 1) => (1 : ℝ)))) /
          (∑ j : Fin (r + 1),
            ((fun _ : Fin (r + 1) => (1 : ℝ)) j) ^ 2) := by
  classical
  let H := halfExtent (n + 1)
  let delta : ℝ :=
    physicalOriginalGlobalQuarterEnergyExplicitFineRadius
      H r frozen (le_of_lt hFrozen)
  have hDelta : 0 < delta :=
    physicalOriginalGlobalQuarterEnergyExplicitFineRadius_pos H r frozen hFrozen
  let fine : ℝ := delta / 2
  have hFinePos : 0 < fine := by
    dsimp [fine]
    linarith
  have hFineSmall : fine < delta := by
    dsimp [fine]
    linarith
  let beta : ℕ → ℝ := fun k =>
    if k = n then frozen else if k = n + 1 then fine else 0
  have hbeta : ∀ k : ℕ, 0 ≤ beta k := by
    intro k
    by_cases hk : k = n
    · simp [beta, hk, le_of_lt hFrozen]
    · by_cases hk' : k = n + 1
      · change 0 ≤ if k = n then frozen else if k = n + 1 then fine else 0
        rw [if_neg hk, if_pos hk']
        exact le_of_lt hFinePos
      · simp [beta, hk, hk']
  have hFrozenAt : beta n = frozen := by simp [beta]
  have hFineAt : beta (n + 1) = fine := by simp [beta]
  have hAway : ∀ k, k ≠ n → k ≠ n + 1 → beta k = 0 := by
    intro k hk hk'
    simp [beta, hk, hk']
  have hFineBound :
      beta (n + 1) <
        physicalOriginalGlobalQuarterEnergyExplicitFineRadius
          H r (beta n) (hbeta n) := by
    simpa only [hFrozenAt, hFineAt] using hFineSmall
  have hEnergy :
      0 < physicalOriginalUnitReceiverFullLinkEnergy
        H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) := by
    simpa only [hFrozenAt] using
      (physicalOriginalUnitReceiverFullLinkEnergy_pos_of_beta_pos_SU2 H frozen hFrozen)
  have hFloor :
      0 < ((r + 1 : ℕ) : ℝ) *
        (physicalOriginalUnitReceiverFullLinkEnergy
          H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) / 4) :=
    mul_pos (by positivity) (div_pos hEnergy (by norm_num))
  have hRayleigh :
      ((r + 1 : ℕ) : ℝ) *
        (physicalOriginalUnitReceiverFullLinkEnergy
          H 2 specialUnitaryTwoWilsonRankPositive (beta n) (hbeta n) / 4) <
        (star (fun _ : Fin (r + 1) => (1 : ℝ)) ⬝ᵥ
          (Matrix.mulVec
            (fineRightKrylovPairHaarResidualGram
              (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
              n r)
            (fun _ : Fin (r + 1) => (1 : ℝ)))) /
          (∑ j : Fin (r + 1),
            ((fun _ : Fin (r + 1) => (1 : ℝ)) j) ^ 2) :=
    fineRightKrylovPairHaarResidualGram_ones_normalizedRayleigh_gt_globalQuarterEnergy_of_explicitRadius
      (halfExtent := halfExtent) (beta := beta) (hbeta := hbeta)
      n r hFineBound
  refine ⟨beta, hbeta, hFrozenAt, ?_, ?_, hAway, hFloor, hRayleigh⟩
  · rw [hFineAt]
    rfl
  · simpa only [hFineAt] using hFinePos

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
