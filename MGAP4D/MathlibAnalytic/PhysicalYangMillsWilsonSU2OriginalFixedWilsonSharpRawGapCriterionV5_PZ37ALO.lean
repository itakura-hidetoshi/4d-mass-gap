import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFixedWilsonSpectralDefectFloorV5_PZ37ALN
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ALO: sharp original fixed-coupling Wilson raw/gap equivalence

ALK/ALM proved the existing high-temperature Harnack/Schur cutoff family
does not reach the original beta0=log(3/2)/64. ALN then certified
a genuine positive finite-H Wilson raw spectral defect using ALJ's
moment-improved lower bound F_H <= ||P_H||, but no H-independent rate.

ALN also supplied a sufficient raw norm hypothesis
  ||P_H x|| <= q * F_H * ||x||
to imply ||R_H|| <= q. Since F_H <= ||P_H||, this hypothesis is
STRONGER than the sharp relative raw condition.

Here we prove an exact if-and-only-if for the unchanged physical
Wilson one-slab transfer P, normalized S=P/||P||, full top-orthogonal K,
with no Harnack, AJA surrogate, new source, or altered beta:
  ||R_H|| <= q   IFF
    forall x in K_H, ||P_H x|| <= q * ||P_H|| * ||x||
for every real q>=0. The same equivalence holds for ONE fixed q
quantified BEFORE all finite H. For q<1, the inequality is also
equivalent to the exact original normalized physical transfer gap >=1-q.

The ALJ physical norm-floor ratio rho_H=F_H/||P_H|| satisfies
0<rho_H<=1. We prove the sharper implication
  (forall x, ||P_H x|| <= q*F_H*||x||)
   -> ||R_H|| <= q*rho_H <= q
and the associated fixed-H gap >=1-q*rho_H.
This precisely records the extra burden of the ALN condition and
prevents conflating it with the necessary-and-sufficient raw test.

No unproved raw bound is instantiated; the actual fixed-beta0 H-uniform
gap remains NO_DATA. The finite-H compact positivity gap remains
unconditional, and the continuum Yang-Mills gap is NOT proved.
Only a new append-only Lean leaf, standard axioms audited individually.
-/

namespace MGAP4D.MathlibAnalytic

open scoped InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4900000

namespace GroundStatePosteriorJoint

/-- The operator-norm bound on an invariant full-top-orthogonal restriction
is equivalent to a pointwise estimate on the ORIGINAL Hilbert space.
The abstract proof avoids unresolved concrete dependent subtype
typeclass parameters observed in ALN's initial failed source. -/
theorem p4Q2PZ37ALO_genericOrthogonalNorm_le_iff_pointwise
    {E : Type*}
    [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E)
    (hSymm : (T : E →ₗ[ℝ] E).IsSymmetric)
    (q : ℝ) (hq : 0 ≤ q) :
    (‖realHilbertTopEigenspaceOrthogonalRestriction T hSymm‖ ≤ q) ↔
      ∀ x : (realHilbertTopEigenspace T)ᗮ,
        ‖T (x : E)‖ ≤ q * ‖(x : E)‖ := by
  constructor
  · intro hR x
    have hApply :=
      ContinuousLinearMap.le_opNorm
        (realHilbertTopEigenspaceOrthogonalRestriction T hSymm) x
    change ‖T (x : E)‖ ≤
      ‖realHilbertTopEigenspaceOrthogonalRestriction T hSymm‖ * ‖(x : E)‖
      at hApply
    exact hApply.trans
      (mul_le_mul_of_nonneg_right hR (norm_nonneg (x : E)))
  · intro hApply
    exact p4Q2PZ37ALN_genericTopOrthogonalNorm_le_of_pointwise
      T hSymm q hq hApply

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
local notation "Fphys" => p4Q2PZ37ALN_originalFixedPhysicalNormMomentFloor H

/-- The SHARP cutoff-free fixed-beta0 raw Wilson criterion, with actual
physical normalization ||P||. Neither direction requires knowing the
true numerical excited norm, a high-temperature cutoff, or ALJ. -/
theorem p4Q2PZ37ALO_originalFixedNormalizedNorm_le_iff_rawRelative
    (q : ℝ) (hq : 0 ≤ q) :
    (‖R‖ ≤ q) ↔
      ∀ x : K, ‖P (x : G)‖ ≤ q * ‖P‖ * ‖(x : G)‖ := by
  have hSymm : (S : G →ₗ[ℝ] G).IsSymmetric :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
      H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
  constructor
  · intro hNorm x
    have hApply :=
      (p4Q2PZ37ALO_genericOrthogonalNorm_le_iff_pointwise
        S hSymm q hq).mp hNorm x
    have hScale :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlab_raw_normalized_norm_scale
        H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le x
    calc
      ‖P (x : G)‖ = ‖P‖ * ‖S (x : G)‖ := hScale.symm
      _ ≤ ‖P‖ * (q * ‖(x : G)‖) :=
        mul_le_mul_of_nonneg_left hApply (norm_nonneg P)
      _ = q * ‖P‖ * ‖(x : G)‖ := by ring
  · intro hRaw
    apply (p4Q2PZ37ALO_genericOrthogonalNorm_le_iff_pointwise
      S hSymm q hq).mpr
    intro x
    have hScale :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlab_raw_normalized_norm_scale
        H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le x
    have hPpos : 0 < ‖P‖ :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
        H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
    apply (mul_le_mul_iff_of_pos_left hPpos).mp
    calc
      ‖P‖ * ‖S (x : G)‖ = ‖P (x : G)‖ := hScale
      _ ≤ q * ‖P‖ * ‖(x : G)‖ := hRaw x
      _ = ‖P‖ * (q * ‖(x : G)‖) := by ring

/-- Exact equivalence between a target normalized gap >=1-q and the
literal relative raw Wilson norm upper bound on the genuine full-top
orthogonal physical sector. -/
theorem p4Q2PZ37ALO_originalFixedGap_ge_iff_rawRelative
    (q : ℝ) (hq : 0 ≤ q) :
    ((1 - q : ℝ) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
        H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le) ↔
      ∀ x : K, ‖P (x : G)‖ ≤ q * ‖P‖ * ‖(x : G)‖ := by
  have hEquiv :=
    p4Q2PZ37ALO_originalFixedNormalizedNorm_le_iff_rawRelative H q hq
  constructor
  · intro hGap
    have hR : ‖R‖ ≤ q := by
      change 1 - q ≤ 1 - ‖R‖ at hGap
      linarith
    exact hEquiv.mp hR
  · intro hRaw
    have hR : ‖R‖ ≤ q := hEquiv.mpr hRaw
    change 1 - q ≤ 1 - ‖R‖
    linarith

/-- Exact ALJ moment floor / physical norm ratio, with no alteration
to the denominator (actual physical operator norm). -/
def p4Q2PZ37ALO_originalFixedMomentFloorNormRatio : ℝ :=
  Fphys / ‖P‖

local notation "rhoH" => p4Q2PZ37ALO_originalFixedMomentFloorNormRatio H

theorem p4Q2PZ37ALO_originalFixedMomentFloorNormRatio_pos :
    0 < rhoH := by
  unfold p4Q2PZ37ALO_originalFixedMomentFloorNormRatio
  exact div_pos
    (p4Q2PZ37ALN_originalFixedPhysicalNormMomentFloor_pos H)
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le)

theorem p4Q2PZ37ALO_originalFixedMomentFloorNormRatio_le_one :
    rhoH ≤ 1 := by
  unfold p4Q2PZ37ALO_originalFixedMomentFloorNormRatio
  apply (div_le_one
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le)).mpr
  exact p4Q2PZ37ALN_originalFixedPhysicalNormMomentFloor_le_norm H

/-- A raw norm premise measured against ALJ's moment floor certifies a
strictly SHARPER normalized ceiling q*rhoH (not merely q).
Since rhoH <= 1, this displays the extra strictness of ALN's sufficient
condition relative to the exact raw Wilson criterion. -/
theorem p4Q2PZ37ALO_originalFixedNorm_le_momentCorrectedCeiling
    (q : ℝ) (hq : 0 ≤ q)
    (hRaw : ∀ x : K,
      ‖P (x : G)‖ ≤ q * Fphys * ‖(x : G)‖) :
    ‖R‖ ≤ q * rhoH := by
  have hRatio : 0 ≤ rhoH :=
    (p4Q2PZ37ALO_originalFixedMomentFloorNormRatio_pos H).le
  have hPpos : 0 < ‖P‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
  apply (p4Q2PZ37ALO_originalFixedNormalizedNorm_le_iff_rawRelative
    H (q * rhoH) (mul_nonneg hq hRatio)).mpr
  intro x
  have hIdentity : (q * rhoH) * ‖P‖ = q * Fphys := by
    unfold p4Q2PZ37ALO_originalFixedMomentFloorNormRatio
    calc
      (q * (Fphys / ‖P‖)) * ‖P‖ =
          q * ((Fphys / ‖P‖) * ‖P‖) := by ring
      _ = q * Fphys := by rw [div_mul_cancel₀ _ hPpos.ne']
  calc
    ‖P (x : G)‖ ≤ q * Fphys * ‖(x : G)‖ := hRaw x
    _ = (q * rhoH) * ‖P‖ * ‖(x : G)‖ := by rw [hIdentity]

/-- Explicit numerical comparison of ALN's corrected ceiling to q. -/
theorem p4Q2PZ37ALO_originalFixedMomentCorrectedCeiling_le_q
    (q : ℝ) (hq : 0 ≤ q) :
    q * rhoH ≤ q := by
  calc
    q * rhoH ≤ q * (1 : ℝ) :=
      mul_le_mul_of_nonneg_left
        (p4Q2PZ37ALO_originalFixedMomentFloorNormRatio_le_one H) hq
    _ = q := by ring

/-- Enhanced quantitative original fixed-beta0 top-orthogonal gap
produced by ALN's overstrong moment-floor raw premise. This makes the
physical normalization loss rhoH explicit and visible. -/
theorem p4Q2PZ37ALO_originalFixedGap_ge_momentCorrectedCeiling
    (q : ℝ) (hq : 0 ≤ q)
    (hRaw : ∀ x : K,
      ‖P (x : G)‖ ≤ q * Fphys * ‖(x : G)‖) :
    (1 - q * rhoH : ℝ) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
        H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le := by
  have hR :=
    p4Q2PZ37ALO_originalFixedNorm_le_momentCorrectedCeiling H q hq hRaw
  change 1 - q * rhoH ≤ 1 - ‖R‖
  linarith

theorem p4Q2PZ37ALO_originalFixedGap_pos_of_momentRawBound
    (q : ℝ) (hq : 0 ≤ q) (hqLt : q < 1)
    (hRaw : ∀ x : K,
      ‖P (x : G)‖ ≤ q * Fphys * ‖(x : G)‖) :
    0 < 1 - q * rhoH ∧
      1 - q * rhoH ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
          H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le := by
  have hCeil :=
    p4Q2PZ37ALO_originalFixedMomentCorrectedCeiling_le_q H q hq
  exact ⟨by linarith,
    p4Q2PZ37ALO_originalFixedGap_ge_momentCorrectedCeiling H q hq hRaw⟩

/-- One q chosen before all H gives the SHARP scale-independent raw test
using the ACTUAL Wilson norm. It is equivalent to an H-uniform operator
norm bound and does not require any unknown Harnack frame condition. -/
theorem p4Q2PZ37ALO_allH_originalFixedNormBound_iff_rawRelative
    (q : ℝ) (hq : 0 ≤ q) :
    (∀ H : ℕ,
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le‖ ≤ q) ↔
      ∀ (H : ℕ)
        (x : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
          H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le),
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
          (x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)‖ ≤
          q * ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le‖ *
          ‖(x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)‖ := by
  constructor
  · intro hNorm H x
    exact
      (p4Q2PZ37ALO_originalFixedNormalizedNorm_le_iff_rawRelative H q hq).mp
        (hNorm H) x
  · intro hRaw H
    exact
      (p4Q2PZ37ALO_originalFixedNormalizedNorm_le_iff_rawRelative H q hq).mpr
        (hRaw H)

/-- Existence of a SINGLE H-uniform fixed-beta0 gap factor q<1 is equivalent
to existence of a SINGLE literal *relative* raw Wilson norm factor q<1.
This is an exact criterion, not a proof that either existential holds. -/
theorem p4Q2PZ37ALO_allH_originalFixedUniformGapFactor_iff_rawRelative :
    (∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧
      ∀ H : ℕ,
        ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
          H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le‖ ≤ q) ↔
      (∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧
        ∀ (H : ℕ)
          (x : periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
            H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le),
          ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
            H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
            (x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)‖ ≤
            q * ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
              H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le‖ *
            ‖(x : periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2)‖) := by
  constructor
  · rintro ⟨q, hq, hqLt, hBound⟩
    exact ⟨q, hq, hqLt,
      (p4Q2PZ37ALO_allH_originalFixedNormBound_iff_rawRelative q hq).mp hBound⟩
  · rintro ⟨q, hq, hqLt, hRaw⟩
    exact ⟨q, hq, hqLt,
      (p4Q2PZ37ALO_allH_originalFixedNormBound_iff_rawRelative q hq).mpr hRaw⟩

/-- Exact physical beta0 specialization of the already-proved
scale-uniform raw-squared-defect / positive-gap equivalence.
No additional coefficient estimate is supplied by this specialization. -/
theorem p4Q2PZ37ALO_originalFixedUniformRawSquaredDefect_iff_uniformGap :
    PeriodicHypercubicEvenSpecialUnitaryHasUniformRawTopOrthogonalSquaredDefect
      (fun H : ℕ => H) 2 (by norm_num)
      (fun _ : ℕ => beta0)
      (fun _ : ℕ => p4Q2PZ37ADC_fixedCoupling_pos.le) ↔
    PeriodicHypercubicEvenSpecialUnitaryHasUniformTopEigenspaceTransferGap
      (fun H : ℕ => H) 2 (by norm_num)
      (fun _ : ℕ => beta0)
      (fun _ : ℕ => p4Q2PZ37ADC_fixedCoupling_pos.le) := by
  exact periodicHypercubicEvenSpecialUnitary_uniformRawDefect_iff_uniformTransferGap
    (fun H : ℕ => H) 2 (by norm_num)
    (fun _ : ℕ => beta0)
    (fun _ : ℕ => p4Q2PZ37ADC_fixedCoupling_pos.le)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALO_genericOrthogonalNorm_le_iff_pointwise
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALO_originalFixedNormalizedNorm_le_iff_rawRelative
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALO_originalFixedGap_ge_iff_rawRelative
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALO_originalFixedMomentFloorNormRatio
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALO_originalFixedMomentFloorNormRatio_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALO_originalFixedMomentFloorNormRatio_le_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALO_originalFixedNorm_le_momentCorrectedCeiling
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALO_originalFixedMomentCorrectedCeiling_le_q
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALO_originalFixedGap_ge_momentCorrectedCeiling
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALO_originalFixedGap_pos_of_momentRawBound
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALO_allH_originalFixedNormBound_iff_rawRelative
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALO_allH_originalFixedUniformGapFactor_iff_rawRelative
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALO_originalFixedUniformRawSquaredDefect_iff_uniformGap
