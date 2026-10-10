import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarPhysicalDepthLossPositivity
import Mathlib.Tactic

/-!
# P4-Q2-X: physical full-link innovation energy bounds the certified depth horizon

The original signed Wilson posterior link Hilbert estimate is
  ‖I_e(f)‖² ≤ gamma(H,b) ‖f‖²
for each genuine spatial link e. The canonical physical constant u_H
has EXACT unit Haar-L² norm. Therefore summing the original link
innovations, without using any substitute posterior or transfer,

  0 < E_unit(H,b) ≤ L_H gamma(H,b),    b > 0.

The P4-Q2-W physically defined depth-loss coefficient is
  Q(H,b) = sqrt(L_H) sqrt(gamma(H,b)) C_H,
  C_H = 2 exp(A_H) A_H, A_H = 2 V_H,
where V_H is the ORIGINAL one-slab combinatorial action volume
(spatial plaquette-list length + spatial link-list length).
Thus the certified depth horizon has the physical upper bounds

  0 < R(H,b)/Q(H,b) ≤ 1/C_H ≤ 1/(4 V_H).

Consequently, a positive floor epsilon under the P4-Q2-U *sufficient*
fine-coupling radius at depth r forces
  4 V_H * r * epsilon ≤ 1.

These inequalities expose an obstruction to volume/depth-uniformity
of THIS global-action/signed-Hilbert telescoping certificate. They
do NOT disprove positive definiteness of the authentic Wilson Gram,
and do NOT imply absence or presence of a continuum mass gap.
No Dobrushin, no surrogate measure or transfer, no new axioms.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Filter
open scoped ENNReal InnerProductSpace InnerProduct BigOperators

noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 750000

local instance p4XGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4XCompact :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4XSecondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4XMeasurable :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4XBorel :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2
local instance p4XLinkFintype (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

/-- The ORIGINAL Wilson full-link constant-input posterior innovation
energy never exceeds the true number of links times the already-proved
signed Hilbert coefficient. The unit vector has actual norm one. -/
theorem physicalOriginalUnitReceiverFullLinkEnergy_le_card_mul_signedHilbert_SU2
    (H : ℕ) (frozen : ℝ) (hFrozen : 0 ≤ frozen) :
    physicalOriginalUnitReceiverFullLinkEnergy
      H 2 specialUnitaryTwoWilsonRankPositive frozen hFrozen ≤
      (Fintype.card (PeriodicHypercubicEvenSpatialSliceLink H) : ℝ) *
        originalWilsonPhysicalSignedInnovationHilbertCoefficient
          H 2 specialUnitaryTwoWilsonRankPositive frozen hFrozen := by
  classical
  let Link := PeriodicHypercubicEvenSpatialSliceLink H
  let u := periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector H 2
  let I := physicalOriginalReceiverPosteriorInnovation
    H 2 specialUnitaryTwoWilsonRankPositive frozen hFrozen
  let gamma := originalWilsonPhysicalSignedInnovationHilbertCoefficient
    H 2 specialUnitaryTwoWilsonRankPositive frozen hFrozen
  have hu : ‖u‖ = 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalConstantUnitVector_norm H 2
  change (∑ e : Link, ‖I e u‖ ^ 2) ≤ (Fintype.card Link : ℝ) * gamma
  calc
    (∑ e : Link, ‖I e u‖ ^ 2) ≤ ∑ _e : Link, gamma := by
      apply Finset.sum_le_sum
      intro e _he
      have hBound :=
        physicalOriginalReceiverPosteriorInnovation_norm_sq_le_signedHilbert
          H 2 specialUnitaryTwoWilsonRankPositive frozen hFrozen e u
      simpa only [hu, one_pow, mul_one] using hBound
    _ = (Fintype.card Link : ℝ) * gamma := by simp

/-- The exact true physical ratio R/Q of P4-Q2-W is bounded above by
the reciprocal C_H⁻¹ of the actual Wilson global-action step constant,
as a direct consequence of the full-link signed Hilbert estimate.
No volume-independent bound on E_unit is inserted. -/
theorem physicalOriginalGlobalQuarterEnergyDepthHorizonRatio_le_expActionInverse
    (H : ℕ) (frozen : ℝ) (hFrozen : 0 < frozen) :
    physicalOriginalGlobalQuarterEnergyDepthHorizonRatio
      H frozen (le_of_lt hFrozen) ≤
      (physicalOriginalNormalizedTransferExpActionLinearConstant H)⁻¹ := by
  let Link := PeriodicHypercubicEvenSpatialSliceLink H
  let L : ℝ := (Fintype.card Link : ℝ)
  let gamma : ℝ :=
    originalWilsonPhysicalSignedInnovationHilbertCoefficient
      H 2 specialUnitaryTwoWilsonRankPositive frozen (le_of_lt hFrozen)
  let Eunit : ℝ :=
    physicalOriginalUnitReceiverFullLinkEnergy
      H 2 specialUnitaryTwoWilsonRankPositive frozen (le_of_lt hFrozen)
  let R : ℝ := Real.sqrt Eunit
  let S : ℝ := Real.sqrt L * Real.sqrt gamma
  let C : ℝ := physicalOriginalNormalizedTransferExpActionLinearConstant H
  let Q : ℝ := physicalOriginalGlobalQuarterEnergyPhysicalDepthLoss
    H frozen (le_of_lt hFrozen)
  have hEnergy : 0 < Eunit :=
    physicalOriginalUnitReceiverFullLinkEnergy_pos_of_beta_pos_SU2
      H frozen hFrozen
  have hGamma : 0 ≤ gamma :=
    originalWilsonPhysicalSignedInnovationHilbertCoefficient_nonneg
      H 2 specialUnitaryTwoWilsonRankPositive frozen (le_of_lt hFrozen)
  have hL : 0 ≤ L := by
    dsimp [L]
    positivity
  have hEnergyLe : Eunit ≤ L * gamma :=
    physicalOriginalUnitReceiverFullLinkEnergy_le_card_mul_signedHilbert_SU2
      H frozen (le_of_lt hFrozen)
  have hRSq : R ^ 2 = Eunit := Real.sq_sqrt (le_of_lt hEnergy)
  have hSSq : S ^ 2 = L * gamma := by
    dsimp [S]
    rw [mul_pow, Real.sq_sqrt hL, Real.sq_sqrt hGamma]
  have hRnonneg : 0 ≤ R := Real.sqrt_nonneg _
  have hSnonneg : 0 ≤ S :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hRleS : R ≤ S := by
    nlinarith [hRSq, hSSq, hEnergyLe]
  have hQpos : 0 < Q :=
    physicalOriginalGlobalQuarterEnergyPhysicalDepthLoss_pos
      H frozen hFrozen
  have hActionPos :=
    physicalOriginalOneSlabGlobalActionBudget_pos_SU2 H frozen hFrozen
  have hCpos : 0 < C := by
    dsimp [C, physicalOriginalNormalizedTransferExpActionLinearConstant]
    exact mul_pos (mul_pos (by norm_num) (Real.exp_pos _)) hActionPos
  have hQeq : Q = S * C := rfl
  have hCancel : C⁻¹ * Q = S := by
    rw [hQeq]
    field_simp
  change R / Q ≤ C⁻¹
  apply (div_le_iff₀ hQpos).mpr
  rw [hCancel]
  exact hRleS

/-- The action constant C_H=2 exp(A_H) A_H is at least 4 times
the genuine one-slab combinatorial action volume V_H. This is a
finite-volume bound from the canonical Wilson action counts. -/
theorem physicalOriginalNormalizedTransferExpActionLinearConstant_ge_four_volume
    (H : ℕ) (frozen : ℝ) (hFrozen : 0 < frozen) :
    (4 : ℝ) *
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabCombinatorialVolume H : ℝ) ≤
        physicalOriginalNormalizedTransferExpActionLinearConstant H := by
  let A : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  let V : ℕ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabCombinatorialVolume H
  let C : ℝ := physicalOriginalNormalizedTransferExpActionLinearConstant H
  have hA : 0 < A :=
    physicalOriginalOneSlabGlobalActionBudget_pos_SU2 H frozen hFrozen
  have hExp : 1 ≤ Real.exp A := by
    have hh := Real.exp_le_exp.mpr (le_of_lt hA : (0 : ℝ) ≤ A)
    simpa using hh
  have hNonnegProduct :
      0 ≤ (Real.exp A - 1) * A :=
    mul_nonneg (sub_nonneg.mpr hExp) (le_of_lt hA)
  have hCge : 2 * A ≤ C := by
    change 2 * A ≤ 2 * Real.exp A * A
    nlinarith [hNonnegProduct]
  have hAeq : A = 2 * (V : ℝ) := rfl
  change (4 : ℝ) * (V : ℝ) ≤ C
  calc
    (4 : ℝ) * (V : ℝ) = 2 * A := by rw [hAeq]; ring
    _ ≤ C := hCge

/-- The physical certified depth horizon has an explicit crude
volume-dependent upper bound R/Q ≤ (4 V_H)⁻¹. This is a certificate
obstruction, not an assertion about the actual infinite-depth Gram. -/
theorem physicalOriginalGlobalQuarterEnergyDepthHorizonRatio_le_inv_four_volume
    (H : ℕ) (frozen : ℝ) (hFrozen : 0 < frozen) :
    physicalOriginalGlobalQuarterEnergyDepthHorizonRatio
      H frozen (le_of_lt hFrozen) ≤
      1 / (4 *
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabCombinatorialVolume H : ℝ)) := by
  let V : ℕ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabCombinatorialVolume H
  let C : ℝ := physicalOriginalNormalizedTransferExpActionLinearConstant H
  let A : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  have hA : 0 < A :=
    physicalOriginalOneSlabGlobalActionBudget_pos_SU2 H frozen hFrozen
  have hAeq : A = 2 * (V : ℝ) := rfl
  have hV : 0 < (V : ℝ) := by nlinarith [hA]
  have hFourV : 0 < (4 : ℝ) * (V : ℝ) := by positivity
  have hC : 0 < C := by
    dsimp [C, physicalOriginalNormalizedTransferExpActionLinearConstant]
    exact mul_pos (mul_pos (by norm_num) (Real.exp_pos _)) hA
  have hCge : (4 : ℝ) * (V : ℝ) ≤ C :=
    physicalOriginalNormalizedTransferExpActionLinearConstant_ge_four_volume
      H frozen hFrozen
  have hDiv : C⁻¹ ≤ 1 / (4 * (V : ℝ)) := by
    change (1 : ℝ) / C ≤ (1 : ℝ) / (4 * (V : ℝ))
    apply (div_le_div_iff₀ hC hFourV).mpr
    simpa using hCge
  calc
    physicalOriginalGlobalQuarterEnergyDepthHorizonRatio
        H frozen (le_of_lt hFrozen) ≤ C⁻¹ :=
      physicalOriginalGlobalQuarterEnergyDepthHorizonRatio_le_expActionInverse
        H frozen hFrozen
    _ ≤ 1 / (4 * (V : ℝ)) := hDiv

/-- A putative positive floor epsilon for the P4-Q2-U sufficient fine
radius at depth r forces the exact finite-H combinatorial condition
4 V_H * r * epsilon ≤ 1. The original Wilson Gram may still be
strictly positive beyond this certificate's regime. -/
theorem physicalOriginalGlobalQuarterEnergyExplicitFineRadius_floor_forces_volume_depth
    (H r : ℕ) (frozen : ℝ) (hFrozen : 0 < frozen)
    (epsilon : ℝ) (hEpsilon : 0 < epsilon)
    (hFloor :
      epsilon ≤ physicalOriginalGlobalQuarterEnergyExplicitFineRadius
        H r frozen (le_of_lt hFrozen)) :
    ((r : ℝ) * epsilon) *
      (4 * (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabCombinatorialVolume H : ℝ)) ≤
        1 := by
  let V : ℕ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabCombinatorialVolume H
  let A : ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGlobalActionBudget H
  have hA : 0 < A :=
    physicalOriginalOneSlabGlobalActionBudget_pos_SU2 H frozen hFrozen
  have hAeq : A = 2 * (V : ℝ) := rfl
  have hV : 0 < (V : ℝ) := by nlinarith [hA]
  have hFourV : 0 < (4 : ℝ) * (V : ℝ) := by positivity
  have hDepth :=
    physicalOriginalGlobalQuarterEnergyExplicitFineRadius_floor_depth_le_horizonRatio
      H r frozen hFrozen epsilon hEpsilon hFloor
  have hRatio :=
    physicalOriginalGlobalQuarterEnergyDepthHorizonRatio_le_inv_four_volume
      H frozen hFrozen
  have hChain : (r : ℝ) * epsilon ≤ 1 / (4 * (V : ℝ)) :=
    hDepth.trans hRatio
  exact (le_div_iff₀ hFourV).mp hChain

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D
