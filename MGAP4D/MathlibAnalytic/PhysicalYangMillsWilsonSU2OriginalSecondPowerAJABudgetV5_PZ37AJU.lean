import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalTrueL2DefectFloorV5_PZ37AJT
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AJU — two-power genuine Wilson defect and exact AJA threshold

This append-only leaf keeps the genuine original ZW signed centered source,
the original positive normalized SU(2) one-slab physical Wilson transfer,
the complete top fixed eigenspace (NOT a chosen vacuum line), the original
spatial Haar probability, and every previous physical hypothesis unchanged.

AJT proved an unconditionally positive original physical L² one-step defect
floor d(H,beta)=beta*v_H/exp(beta*p_H) with the AIK certified rational Haar
source-variance floor v_H=(3*p_H/8)^2*(1/384)^(4*card(Link_H)).

Combine AJR's exact one-step deficit upper estimate with AJI's genuine
full-top orthogonal-sector contraction q=||R||<1 and the actual Pythagoras
identities. At the explicit INTEGER POWER 2 obtain

  ||S^2 f0||² + (1-q^4)*(d/(1+q))² <= V_H.

This is an UNCONDITIONAL strict improvement over source variance. The true
AJA margin/Haar budget B(H,beta) is not weakened or replaced. It follows
that the explicit comparison

  V_H - (1-q^4)*(d/(1+q))² < B(H,beta)

is a SUFFICIENT, not proven fulfilled, original two-power witness condition.
Under this one unresolved comparison, the witness n=2 is literal, and the
original normalized transferred source has a nonzero full-top-orthogonal
excitation sector (distinct from AJQ's unconditional PRE-transfer sector).

No unconditional n=2 AJA witness, numerical value for q or B, top
simplicity, H-uniform coercivity, Hamiltonian gap or 4D continuum mass
gap is claimed. Every quantitative object retains the original H,beta.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open Filter
open scoped InnerProductSpace Topology Classical ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Every real Hilbert selfadjoint contraction with a complete fixed
top space obeys a two-power loss bound from any genuine one-step lower
defect d, retaining the EXACT full-top orthogonal restriction norm q.
No assumption that the top eigenspace is one-dimensional. -/
theorem realHilbert_fullTop_secondPower_defect_floor_aju
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E]
    (S : E →L[ℝ] E)
    [(realHilbertTopEigenspace S).HasOrthogonalProjection]
    (hSymm : (S : E →ₗ[ℝ] E).IsSymmetric)
    (hq :
      ‖realHilbertTopEigenspaceOrthogonalRestriction S hSymm‖ < 1)
    (x : E) (d : ℝ) (hd : 0 ≤ d)
    (hdef : d ≤ ‖x - S x‖) :
    ‖(S ^ 2) x‖ ^ 2 +
      (1 - ‖realHilbertTopEigenspaceOrthogonalRestriction S hSymm‖ ^ 4) *
        (d / (1 + ‖realHilbertTopEigenspaceOrthogonalRestriction S hSymm‖)) ^ 2
      ≤ ‖x‖ ^ 2 := by
  let F : Submodule ℝ E := realHilbertTopEigenspace S
  let R := realHilbertTopEigenspaceOrthogonalRestriction S hSymm
  let q : ℝ := ‖R‖
  let p : ℝ := ‖(Fᗮ).starProjection x‖
  let c : ℝ := d / (1 + q)
  letI : CompleteSpace F := (realHilbertTopEigenspace_isClosed S).completeSpace_coe
  letI : CompleteSpace Fᗮ := F.isClosed_orthogonal.completeSpace_coe
  have hq0 : 0 ≤ q := norm_nonneg R
  have hp0 : 0 ≤ p := norm_nonneg _
  have hDen : 0 < 1 + q := by linarith
  have hOne : ‖x - S x‖ ≤ (1 + q) * p := by
    have h := realHilbert_fullTop_oneStep_defect_norm_le_ajr S hSymm x
    change ‖x - S x‖ ≤ (1 + q) * p at h
    exact h
  have hRatio : c ≤ p := by
    change d / (1 + q) ≤ p
    apply (div_le_iff₀ hDen).2
    exact hdef.trans hOne
  have hc0 : 0 ≤ c := div_nonneg hd hDen.le
  have hRatioSq : c ^ 2 ≤ p ^ 2 :=
    (sq_le_sq₀ hc0 hp0).2 hRatio
  have hq4 : q ^ 4 ≤ 1 := pow_le_one₀ hq0 hq.le
  have hCoef : 0 ≤ 1 - q ^ 4 := sub_nonneg.mpr hq4
  have hCorr : (1 - q ^ 4) * c ^ 2 ≤
      (1 - q ^ 4) * p ^ 2 :=
    mul_le_mul_of_nonneg_left hRatioSq hCoef
  have hFix : ∀ v : E, v ∈ F → S v = v := by
    intro v hv
    exact (realHilbertTopEigenspace_mem S v).mp hv
  have hPower :
      ‖(S ^ 2) x‖ ^ 2 =
        ‖F.starProjection x‖ ^ 2 +
          ‖(S ^ 2) x - F.starProjection x‖ ^ 2 := by
    have h := realHilbert_fixedSubspace_selectedPower_sq_split_ajn
      F S hSymm hFix 2 x (0 : E) F.zero_mem
    simpa using h
  have hTail :
      ‖(S ^ 2) x - F.starProjection x‖ ≤ q ^ 2 * p := by
    have h := realHilbert_fullTop_power_sub_projection_norm_le_aji
      S hSymm 2 (by norm_num) x
    change ‖(S ^ 2) x - F.starProjection x‖ ≤ q ^ 2 * p at h
    exact h
  have hTail0 : 0 ≤ q ^ 2 * p :=
    mul_nonneg (pow_nonneg hq0 2) hp0
  have hTailSq :
      ‖(S ^ 2) x - F.starProjection x‖ ^ 2 ≤
        q ^ 4 * p ^ 2 := by
    calc
      _ ≤ (q ^ 2 * p) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) hTail0).2 hTail
      _ = q ^ 4 * p ^ 2 := by ring
  have hPyth :
      ‖x‖ ^ 2 = ‖F.starProjection x‖ ^ 2 + p ^ 2 := by
    have h := F.norm_sq_eq_add_norm_sq_starProjection x
    simp only [F.starProjection_orthogonal_val] at h
    change ‖x‖ ^ 2 = ‖F.starProjection x‖ ^ 2 + p ^ 2 at h
    exact h
  change ‖(S ^ 2) x‖ ^ 2 + (1 - q ^ 4) * c ^ 2 ≤ ‖x‖ ^ 2
  calc
    _ = ‖F.starProjection x‖ ^ 2 +
          ‖(S ^ 2) x - F.starProjection x‖ ^ 2 +
          (1 - q ^ 4) * c ^ 2 := by rw [hPower]; ring
    _ ≤ ‖F.starProjection x‖ ^ 2 + q ^ 4 * p ^ 2 +
          (1 - q ^ 4) * c ^ 2 :=
      add_le_add_right (add_le_add_left hTailSq _) _
    _ ≤ ‖F.starProjection x‖ ^ 2 + q ^ 4 * p ^ 2 +
          (1 - q ^ 4) * p ^ 2 :=
      add_le_add_left hCorr _
    _ = ‖x‖ ^ 2 := by rw [hPyth]; ring

local notation "GU" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AJU_group : IsTopologicalGroup GU :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AJU_compact : CompactSpace GU :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AJU_secondCountable : SecondCountableTopology GU :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AJU_measurable : MeasurableSpace GU :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AJU_borel : BorelSpace GU :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AJU_linkFintype (K : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink K) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "PhysU" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "CfgU" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muU" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "fU" =>
  p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "SU" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator H 2 (by norm_num)
local notation "RU" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator H 2 (by norm_num)
local notation "VU" =>
  p4Q2PZ37AHN_originalSource_HaarSecondMoment H
local notation "vU" =>
  p4Q2PZ37AIK_elementarySourceVarianceFloor H
local notation "pU" =>
  p4Q2PZ37AFZ_plaquetteCount H
local notation "uU" =>
  p4Q2PZ37AIW_originalNormalizedSourceTransfer H
local notation "mU" =>
  p4Q2PZ37AIW_originalNormalizedNegativeMargin H

local instance p4Q2PZ37AJU_physicalComplete (K : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule K 2) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    K 2).completeSpace_coe

local instance p4Q2PZ37AJU_topComplete
    (K : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace
        K 2 (by norm_num) beta hbeta) :=
  (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_isClosed
    K 2 (by norm_num) beta hbeta).completeSpace_coe

/-- Existing AIK genuine SU(2) Haar-box rational floor in AJT's true
physical one-step defect, with the actual original source and kernel. -/
def p4Q2PZ37AJU_originalDefectFloor (beta : ℝ) : ℝ :=
  beta * vU / Real.exp (beta * pU)

theorem p4Q2PZ37AJU_originalDefectFloor_pos
    (beta : ℝ) (hbeta : 0 < beta) :
    0 < p4Q2PZ37AJU_originalDefectFloor H beta := by
  unfold p4Q2PZ37AJU_originalDefectFloor
  exact div_pos (mul_pos hbeta
    (p4Q2PZ37AIK_elementarySourceVarianceFloor_pos H)) (Real.exp_pos _)

theorem p4Q2PZ37AJU_originalDefectFloor_le_physicalDefect
    (beta : ℝ) (hbeta : 0 < beta) :
    p4Q2PZ37AJU_originalDefectFloor H beta ≤
      ‖fU - (SU beta hbeta.le) fU‖ := by
  exact p4Q2PZ37AJT_originalPhysicalDefect_ge_rationalVarianceFloor
    H beta hbeta

/-- Every factor remains from the ORIGINAL same-H beta Wilson model.
This correction is strictly positive (proved separately) but not
automatically large enough relative to the AJA Haar budget. -/
def p4Q2PZ37AJU_originalTwoPowerCorrection
    (beta : ℝ) (hbeta : 0 ≤ beta) : ℝ :=
  (1 - ‖RU beta hbeta‖ ^ 4) *
    (p4Q2PZ37AJU_originalDefectFloor H beta /
      (1 + ‖RU beta hbeta‖)) ^ 2

theorem p4Q2PZ37AJU_originalTwoPowerCorrection_pos
    (beta : ℝ) (hbeta : 0 < beta) :
    0 < p4Q2PZ37AJU_originalTwoPowerCorrection H beta hbeta.le := by
  let R := RU beta hbeta.le
  have hq : ‖R‖ < 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
      H 2 (by norm_num) beta hbeta.le
  have hq4 : ‖R‖ ^ 4 < 1 :=
    pow_lt_one₀ (norm_nonneg R) hq (by norm_num)
  have hδ : 0 < p4Q2PZ37AJU_originalDefectFloor H beta :=
    p4Q2PZ37AJU_originalDefectFloor_pos H beta hbeta
  have hden : 0 < 1 + ‖R‖ := by
    have hq0 : 0 ≤ ‖R‖ := norm_nonneg R
    linarith
  change 0 < (1 - ‖R‖ ^ 4) *
    (p4Q2PZ37AJU_originalDefectFloor H beta / (1 + ‖R‖)) ^ 2
  exact mul_pos (sub_pos.mpr hq4)
    (sq_pos_of_pos (div_pos hδ hden))

/-- TRUE original finite-H Wilson second power with unconditional,
strictly POSITIVE rational-source-defect correction. -/
theorem p4Q2PZ37AJU_originalSecondPower_sq_add_defectFloor_le_variance
    (beta : ℝ) (hbeta : 0 < beta) :
    ‖((SU beta hbeta.le) ^ 2) fU‖ ^ 2 +
      p4Q2PZ37AJU_originalTwoPowerCorrection H beta hbeta.le ≤ VU := by
  let S : PhysU →L[ℝ] PhysU := SU beta hbeta.le
  let F : Submodule ℝ PhysU := realHilbertTopEigenspace S
  let hS : (S : PhysU →ₗ[ℝ] PhysU).IsSymmetric :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
      H 2 (by norm_num) beta hbeta.le
  let R := realHilbertTopEigenspaceOrthogonalRestriction S hS
  letI : CompleteSpace F := (realHilbertTopEigenspace_isClosed S).completeSpace_coe
  letI : CompleteSpace Fᗮ := F.isClosed_orthogonal.completeSpace_coe
  have hq : ‖R‖ < 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator_norm_lt_one
      H 2 (by norm_num) beta hbeta.le
  have hδ : 0 ≤ p4Q2PZ37AJU_originalDefectFloor H beta :=
    (p4Q2PZ37AJU_originalDefectFloor_pos H beta hbeta).le
  have hdef : p4Q2PZ37AJU_originalDefectFloor H beta ≤ ‖fU - S fU‖ :=
    p4Q2PZ37AJU_originalDefectFloor_le_physicalDefect H beta hbeta
  have hGen :=
    realHilbert_fullTop_secondPower_defect_floor_aju
      S hS hq fU (p4Q2PZ37AJU_originalDefectFloor H beta) hδ hdef
  change
    ‖((SU beta hbeta.le) ^ 2) fU‖ ^ 2 +
      p4Q2PZ37AJU_originalTwoPowerCorrection H beta hbeta.le ≤
      ‖fU‖ ^ 2 at hGen
  rw [p4Q2PZ37AJR_originalSource_norm_sq_eq_HaarVariance H] at hGen
  exact hGen

/-- Genuine n=2 is already unconditionally and quantitatively below
the entire original centered source Haar variance, not necessarily
below the smaller original AJA margin/Haar certificate. -/
theorem p4Q2PZ37AJU_originalSecondPower_sq_strict_lt_variance
    (beta : ℝ) (hbeta : 0 < beta) :
    ‖((SU beta hbeta.le) ^ 2) fU‖ ^ 2 < VU := by
  have hBudget :=
    p4Q2PZ37AJU_originalSecondPower_sq_add_defectFloor_le_variance
      H beta hbeta
  have hPos :=
    p4Q2PZ37AJU_originalTwoPowerCorrection_pos H beta hbeta
  linarith

/-- A fully specified witness EXPONENT 2 follows if and only if the
required AJA side of the comparison is supplied independently.
No value for q, B or top multiplicity is fabricated. -/
theorem p4Q2PZ37AJU_originalSecondPower_AJA_of_strictThreshold
    (beta : ℝ) (hbeta : 0 < beta)
    (hThreshold :
      VU - p4Q2PZ37AJU_originalTwoPowerCorrection H beta hbeta.le <
        (mU beta hbeta.le) ^ 2 *
          Measure.real muU
            {B : CfgU |
              uU beta hbeta.le B < -(mU beta hbeta.le)}) :
    ‖((SU beta hbeta.le) ^ 2) fU‖ ^ 2 <
      (mU beta hbeta.le) ^ 2 *
        Measure.real muU
          {B : CfgU | uU beta hbeta.le B < -(mU beta hbeta.le)} := by
  have hFloor :=
    p4Q2PZ37AJU_originalSecondPower_sq_add_defectFloor_le_variance
      H beta hbeta
  linarith only [hFloor, hThreshold]

/-- Literal finite integer witness n=2, not a nonconstructive eventual n,
under exactly the still-open certified strict physical AJA comparison. -/
theorem p4Q2PZ37AJU_originalExplicitSecondPower_AJA_witness
    (beta : ℝ) (hbeta : 0 < beta)
    (hThreshold :
      VU - p4Q2PZ37AJU_originalTwoPowerCorrection H beta hbeta.le <
        (mU beta hbeta.le) ^ 2 *
          Measure.real muU
            {B : CfgU | uU beta hbeta.le B < -(mU beta hbeta.le)}) :
    ∃ n : ℕ, 0 < n ∧
      ‖((SU beta hbeta.le) ^ n) fU‖ ^ 2 <
        (mU beta hbeta.le) ^ 2 *
          Measure.real muU
            {B : CfgU | uU beta hbeta.le B < -(mU beta hbeta.le)} := by
  exact ⟨2, by norm_num,
    p4Q2PZ37AJU_originalSecondPower_AJA_of_strictThreshold
      H beta hbeta hThreshold⟩

/-- This explicit second-power budget threshold forces genuine original
source FULL-top smallness; the top is not assumed to be rank one. -/
theorem p4Q2PZ37AJU_originalFullTop_small_of_strictThreshold
    (beta : ℝ) (hbeta : 0 < beta)
    (hThreshold :
      VU - p4Q2PZ37AJU_originalTwoPowerCorrection H beta hbeta.le <
        (mU beta hbeta.le) ^ 2 *
          Measure.real muU
            {B : CfgU | uU beta hbeta.le B < -(mU beta hbeta.le)}) :
    ‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2 <
      (mU beta hbeta.le) ^ 2 *
        Measure.real muU
          {B : CfgU | uU beta hbeta.le B < -(mU beta hbeta.le)} := by
  exact
    (p4Q2PZ37AJI_fullTop_small_iff_exists_transferPower_budget
      H beta hbeta).2
        (p4Q2PZ37AJU_originalExplicitSecondPower_AJA_witness
          H beta hbeta hThreshold)

/-- Conditional, genuinely transferred full-top-orthogonal source
sector nonzero, distinct from AJQ's unconditional SOURCE pre-transfer.
The actual AJA certificate and AJD Pythagoras are kept. -/
theorem p4Q2PZ37AJU_originalTransferredOrthogonal_ne_zero_of_threshold
    (beta : ℝ) (hbeta : 0 < beta)
    (hThreshold :
      VU - p4Q2PZ37AJU_originalTwoPowerCorrection H beta hbeta.le <
        (mU beta hbeta.le) ^ 2 *
          Measure.real muU
            {B : CfgU | uU beta hbeta.le B < -(mU beta hbeta.le)}) :
    p4Q2PZ37AJC_originalNormalizedSourceOrthogonalComponent H beta hbeta ≠ 0 := by
  have hTop :=
    p4Q2PZ37AJU_originalFullTop_small_of_strictThreshold
      H beta hbeta hThreshold
  have hAJA :=
    p4Q2PZ37AJA_originalNormalizedPhysicalSource_norm_sq_ge_margin_measure
      H beta hbeta
  have hSplit :=
    p4Q2PZ37AJD_sourceImage_norm_sq_eq_sourceTop_add_orthogonal
      H beta hbeta
  intro hz
  rw [hz, norm_zero, zero_pow, add_zero] at hSplit
  rw [hSplit] at hAJA
  exact (not_lt_of_ge hAJA) hTop

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

/-! Every new true-code declaration is separately audited by the Lean kernel. -/
#print axioms MGAP4D.MathlibAnalytic.realHilbert_fullTop_secondPower_defect_floor_aju
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJU_originalDefectFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJU_originalDefectFloor_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJU_originalDefectFloor_le_physicalDefect
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJU_originalTwoPowerCorrection
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJU_originalTwoPowerCorrection_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJU_originalSecondPower_sq_add_defectFloor_le_variance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJU_originalSecondPower_sq_strict_lt_variance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJU_originalSecondPower_AJA_of_strictThreshold
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJU_originalExplicitSecondPower_AJA_witness
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJU_originalFullTop_small_of_strictThreshold
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AJU_originalTransferredOrthogonal_ne_zero_of_threshold
