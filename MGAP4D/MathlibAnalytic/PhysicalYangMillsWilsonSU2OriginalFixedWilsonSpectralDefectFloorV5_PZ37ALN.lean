import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalAllScalesFixedCouplingHarnackObstructionV5_PZ37ALM
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferScaleUniformDefectBridge
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ALN: original Wilson beta0, full-top raw spectral defect, ALJ moment floor

The genuinely fixed beta0 = log(3/2)/64 cannot enter the existing all-s>8
Harnack/Schur high-temperature sufficient cutoffs (ALM). That failure of one
method does not imply absence of a Wilson spectral gap.

For each finite original SU(2) physical H, the full-top-orthogonal
normalized restriction R_H(beta0) is already strictly contractive by
positivity + compactness, although NO H-independent rate has been proved.

Here we preserve the ORIGINAL Hilbert space, actual physical Wilson P_H,
its normalized S_H = P_H/||P_H||, full eigenvalue-one orthogonal K_H,
unchanged Haar/source/AJA and fixed beta0. Let
  delta_H = 1 - ||R_H(beta0)||^2 > 0
  F_H     = exp(-beta0*p_H) * (ALI/ALJ genuine positive Wilson moment floor).
ALJ proves 0 < F_H <= ||P_H||. The exact raw-defect transport then gives
  delta_H * F_H^2 * ||x||^2
    <= ||P_H||^2 * ||x||^2 - ||P_H x||^2
for every x in the *same genuine* K_H.
The resulting positive model-specific coefficient is strictly better than
the analogous old crossing-partition-only coefficient at beta0.

This bound is unconditional at each finite H, but delta_H is allowed to
depend on H; no illicit uniform conclusion is inferred.

We also isolate an independent direct *sufficient* test:
  forall x in K_H, ||P_H x|| <= q * F_H * ||x||,
  0 <= q < 1
implies ||R_H|| <= q. If that stronger raw Wilson test is eventually proved
with one q for all H, the original beta0 uniform normalized gap follows.
No such all-H raw test is assumed true here.

Only one append-only Lean leaf. No original model, physical definitions,
existing Lean statements, fixed Lean/mathlib pin, roots or workflows changed.
No common-carrier/continuum Yang-Mills mass gap is asserted.
-/

namespace MGAP4D.MathlibAnalytic

open scoped InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4900000

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "beta0" => p4Q2PZ37ADC_fixedCoupling
local notation "G" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "P" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "S" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "K" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
    H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "R" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
    H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le

/-- Exact finite-volume squared spectral deficiency of the actual
normalized full-top-orthogonal Wilson transfer at original beta0. -/
def p4Q2PZ37ALN_originalFixedTopOrthogonalSquaredGap : ℝ :=
  1 - ‖R‖ ^ 2

local notation "deltaH" => p4Q2PZ37ALN_originalFixedTopOrthogonalSquaredGap H

theorem p4Q2PZ37ALN_originalFixedTopOrthogonalSquaredGap_pos :
    0 < deltaH := by
  have hR : ‖R‖ < (1 : ℝ) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
      H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
  have hR0 : (0 : ℝ) ≤ ‖R‖ := norm_nonneg R
  have hProd : 0 < (1 - ‖R‖) * (1 + ‖R‖) := by
    apply mul_pos
    · linarith
    · linarith
  unfold p4Q2PZ37ALN_originalFixedTopOrthogonalSquaredGap
  nlinarith only [hProd]

theorem p4Q2PZ37ALN_originalFixedTopOrthogonalSquaredGap_le_one :
    deltaH ≤ 1 := by
  unfold p4Q2PZ37ALN_originalFixedTopOrthogonalSquaredGap
  nlinarith only [sq_nonneg (‖R‖)]

/-- Original physical SU(2) Wilson norm lower floor at fixed beta0, with
the ALI exact even second/fourth Haar-moment corrections. -/
def p4Q2PZ37ALN_originalFixedPhysicalNormMomentFloor : ℝ :=
  Real.exp (-(beta0 * p4Q2PZ37AFZ_plaquetteCount H)) *
    p4Q2PZ37ALJ_originalWilsonNormScalarFloor H beta0

local notation "Fphys" => p4Q2PZ37ALN_originalFixedPhysicalNormMomentFloor H

theorem p4Q2PZ37ALN_originalFixedPhysicalNormMomentFloor_pos :
    0 < Fphys := by
  exact mul_pos (Real.exp_pos _)
    (p4Q2PZ37ALJ_originalWilsonNormScalarFloor_pos H beta0)

theorem p4Q2PZ37ALN_originalFixedPhysicalNormMomentFloor_le_norm :
    Fphys ≤ ‖P‖ :=
  p4Q2PZ37ALJ_originalPhysicalNorm_ge_scalarFloor
    H beta0 p4Q2PZ37ADC_fixedCoupling_pos.le

/-- Model-dependent raw spectral-defect coefficient. Its strictly
positive sign is unconditional at every finite H, but NOT H-uniform. -/
def p4Q2PZ37ALN_originalFixedMomentRawDefectCoefficient : ℝ :=
  deltaH * Fphys ^ 2

theorem p4Q2PZ37ALN_originalFixedMomentRawDefectCoefficient_pos :
    0 < p4Q2PZ37ALN_originalFixedMomentRawDefectCoefficient H := by
  unfold p4Q2PZ37ALN_originalFixedMomentRawDefectCoefficient
  exact mul_pos
    (p4Q2PZ37ALN_originalFixedTopOrthogonalSquaredGap_pos H)
    (sq_pos_of_pos (p4Q2PZ37ALN_originalFixedPhysicalNormMomentFloor_pos H))

/-- Genuine raw Wilson spectral-defect bound on the entire ORIGINAL
full-top-orthogonal SU(2) physical carrier at beta0. -/
theorem p4Q2PZ37ALN_originalFixedRawDefect_ge_momentFloor
    (x : K) :
    p4Q2PZ37ALN_originalFixedMomentRawDefectCoefficient H * ‖(x : G)‖ ^ 2 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabRawTopOrthogonalSquaredDefect
        H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le x := by
  have hSymm :
      (S : G →ₗ[ℝ] G).IsSymmetric :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
      H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
  have hGeneric :=
    realHilbertTopEigenspaceOrthogonalRestriction_sq_defect_lower_bound
      S hSymm x
  have hNormalized :
      deltaH * ‖(x : G)‖ ^ 2 ≤
        ‖(x : G)‖ ^ 2 - ‖S (x : G)‖ ^ 2 := by
    change (1 - ‖R‖ ^ 2) * ‖(x : G)‖ ^ 2 ≤
      ‖(x : G)‖ ^ 2 - ‖S (x : G)‖ ^ 2 at hGeneric
    exact hGeneric
  have hRaw :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlab_normalized_sq_defect_to_raw
      H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
      deltaH x hNormalized
  have hFloor : Fphys ≤ ‖P‖ :=
    p4Q2PZ37ALN_originalFixedPhysicalNormMomentFloor_le_norm H
  have hFloorSq : Fphys ^ 2 ≤ ‖P‖ ^ 2 := by
    nlinarith only [
      mul_self_le_mul_self
        (p4Q2PZ37ALN_originalFixedPhysicalNormMomentFloor_pos H).le hFloor]
  have hDelta : 0 ≤ deltaH :=
    (p4Q2PZ37ALN_originalFixedTopOrthogonalSquaredGap_pos H).le
  have hScaled :
      (deltaH * Fphys ^ 2) * ‖(x : G)‖ ^ 2 ≤
        (deltaH * ‖P‖ ^ 2) * ‖(x : G)‖ ^ 2 :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hFloorSq hDelta)
      (sq_nonneg _)
  calc
    p4Q2PZ37ALN_originalFixedMomentRawDefectCoefficient H * ‖(x : G)‖ ^ 2 =
        (deltaH * Fphys ^ 2) * ‖(x : G)‖ ^ 2 := rfl
    _ ≤ (deltaH * ‖P‖ ^ 2) * ‖(x : G)‖ ^ 2 := hScaled
    _ = deltaH * ‖P‖ ^ 2 * ‖(x : G)‖ ^ 2 := by ring
    _ ≤ _ := hRaw

/-- The true second/fourth moment correction makes this positive
raw-defect coefficient strictly bigger than the old crossing-only
coefficient. No strict vector-level claim is made at x=0. -/
theorem p4Q2PZ37ALN_originalFixedMomentCoefficient_gt_crossingOnly :
    deltaH *
      (Real.exp (-(beta0 * p4Q2PZ37AFZ_plaquetteCount H)) *
        p4Q2PZ37AIF_originalCrossingPartition H beta0) ^ 2 <
      p4Q2PZ37ALN_originalFixedMomentRawDefectCoefficient H := by
  let oldFloor : ℝ :=
    Real.exp (-(beta0 * p4Q2PZ37AFZ_plaquetteCount H)) *
      p4Q2PZ37AIF_originalCrossingPartition H beta0
  have hExp : 0 < Real.exp (-(beta0 * p4Q2PZ37AFZ_plaquetteCount H)) :=
    Real.exp_pos _
  have hZ : 0 < p4Q2PZ37AIF_originalCrossingPartition H beta0 :=
    p4Q2PZ37AIF_originalCrossingPartition_pos H beta0
  have hOldPos : 0 < oldFloor := mul_pos hExp hZ
  have hFloorPos : 0 < Fphys :=
    p4Q2PZ37ALN_originalFixedPhysicalNormMomentFloor_pos H
  have hOldLt : oldFloor < Fphys := by
    exact mul_lt_mul_of_pos_left
      (p4Q2PZ37ALJ_originalWilsonNormScalarFloor_gt_crossing
        H beta0 p4Q2PZ37ADC_fixedCoupling_pos) hExp
  have hSquare : oldFloor ^ 2 < Fphys ^ 2 := by
    have hProd : 0 < (Fphys - oldFloor) * (Fphys + oldFloor) :=
      mul_pos (sub_pos.mpr hOldLt) (add_pos hFloorPos hOldPos)
    nlinarith only [hProd]
  have hDelta : 0 < deltaH :=
    p4Q2PZ37ALN_originalFixedTopOrthogonalSquaredGap_pos H
  change deltaH * oldFloor ^ 2 < deltaH * Fphys ^ 2
  exact mul_lt_mul_of_pos_left hSquare hDelta

/-- New *cutoff-free* direct SU(2) Wilson sufficient condition.
It asks for a raw physical operator bound with ALJ's strictly positive
moment floor, not a replacement normalized transfer, not an assumption
about the high-temperature Harnack/Schur cutoff. -/
theorem p4Q2PZ37ALN_originalFixedNormalizedRestriction_norm_le_of_rawMomentBound
    (q : ℝ) (hq : 0 ≤ q)
    (hRaw : ∀ x : K, ‖P (x : G)‖ ≤ q * Fphys * ‖(x : G)‖) :
    ‖R‖ ≤ q := by
  apply ContinuousLinearMap.opNorm_le_bound R hq
  intro x
  change ‖S (x : G)‖ ≤ q * ‖(x : G)‖
  have hScale :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlab_raw_normalized_norm_scale
      H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le x
  have hFloor : Fphys ≤ ‖P‖ :=
    p4Q2PZ37ALN_originalFixedPhysicalNormMomentFloor_le_norm H
  have hPpos : 0 < ‖P‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
  have hFactor : 0 ≤ q * ‖(x : G)‖ :=
    mul_nonneg hq (norm_nonneg _)
  have hScaled :
      ‖P‖ * ‖S (x : G)‖ ≤ ‖P‖ * (q * ‖(x : G)‖) := by
    calc
      ‖P‖ * ‖S (x : G)‖ = ‖P (x : G)‖ := hScale
      _ ≤ q * Fphys * ‖(x : G)‖ := hRaw x
      _ = Fphys * (q * ‖(x : G)‖) := by ring
      _ ≤ ‖P‖ * (q * ‖(x : G)‖) :=
        mul_le_mul_of_nonneg_right hFloor hFactor
  exact (mul_le_mul_iff_of_pos_left hPpos).mp hScaled

/-- The same original raw Wilson bound provides the quantitative
fixed-beta0 normalized full-top spectral gap without invoking AKL/ALM
cutoffs. Positivity of 1-q is independent of H when q is. -/
theorem p4Q2PZ37ALN_originalFixedGap_ge_of_rawMomentBound
    (q : ℝ) (hq : 0 ≤ q) (hqLt : q < 1)
    (hRaw : ∀ x : K, ‖P (x : G)‖ ≤ q * Fphys * ‖(x : G)‖) :
    0 < 1 - q ∧
    1 - q ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
        H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le := by
  have hBound :=
    p4Q2PZ37ALN_originalFixedNormalizedRestriction_norm_le_of_rawMomentBound
      H q hq hRaw
  constructor
  · linarith
  · change 1 - q ≤ 1 - ‖R‖
    linarith

/-- Explicit fixed beta0, H-uniform SU(2) direct raw sufficient criterion
for the same 3071/3072 rate as AKL but using no Harnack cutoff.
The premise is *not* claimed to hold for the genuine Wilson model. -/
theorem p4Q2PZ37ALN_allH_originalFixedUniformGap_of_directRawWilsonMomentBound
    (hRaw : ∀ (H : ℕ)
      (x :
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
          H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le),
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
          (x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)‖ ≤
        (3071 / 3072 : ℝ) *
          p4Q2PZ37ALN_originalFixedPhysicalNormMomentFloor H *
          ‖(x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)‖) :
    ∀ H : ℕ,
      (1 / 3072 : ℝ) ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
          H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le := by
  intro H
  have h :=
    (p4Q2PZ37ALN_originalFixedGap_ge_of_rawMomentBound
      H (3071 / 3072 : ℝ) (by norm_num) (by norm_num)
      (hRaw H)).2
  convert h using 1 <;> norm_num

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALN_originalFixedTopOrthogonalSquaredGap
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALN_originalFixedTopOrthogonalSquaredGap_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALN_originalFixedTopOrthogonalSquaredGap_le_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALN_originalFixedPhysicalNormMomentFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALN_originalFixedPhysicalNormMomentFloor_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALN_originalFixedPhysicalNormMomentFloor_le_norm
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALN_originalFixedMomentRawDefectCoefficient
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALN_originalFixedMomentRawDefectCoefficient_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALN_originalFixedRawDefect_ge_momentFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALN_originalFixedMomentCoefficient_gt_crossingOnly
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALN_originalFixedNormalizedRestriction_norm_le_of_rawMomentBound
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALN_originalFixedGap_ge_of_rawMomentBound
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALN_allH_originalFixedUniformGap_of_directRawWilsonMomentBound
