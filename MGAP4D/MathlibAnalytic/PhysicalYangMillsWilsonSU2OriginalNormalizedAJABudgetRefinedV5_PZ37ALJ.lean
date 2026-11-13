import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalIndependentHaarFourthEnhancementV5_PZ37ALI
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ALJ — original Wilson normalized source and AJA budget

ALI's rigorously positive second- and fourth-moment corrections
strengthen the genuine original SU(2) Wilson physical norm lower
bound. This leaf applies that result to the *existing* physical
normalization ||P_H,beta|| and to the *unchanged* AIW/AIG normalized
source and negative-margin AJA certificate.

Let F_H(beta) = Zcross_H(beta) +
    beta^2/2*(2*kFloor_H(beta)*vBox_H) +
    beta^4/32*(kFloor_H(beta)*(8*vBox_H^2)).
For beta>=0, the existing original full physical Wilson transfer has
 ||P_H,beta|| >= exp(-beta*p_H)*F_H(beta).
For beta>0, F_H(beta)>Zcross_H(beta)>0, and hence
 Zcross_H(beta)/||P_H,beta||
   <= exp(beta*p_H)*Zcross_H(beta)/F_H(beta)
   <  exp(beta*p_H).

This yields a strictly improved upper envelope for the original
norm-normalized ZW physical source and normalized AJA negative margin.
The original *strict* negative-event set is NOT redefined. Its true
AJA budget m_H^2 * mu_H{u_H < -m_H} acquires a valid new upper bound,
but NO relation to the unknown whole-top projection energy is asserted.

This is not a spectral gap or continuum Yang-Mills construction.
No prior definitions, source, Wilson kernel, Haar measure, operator,
full-top, AJA condition, dependency pin, root or workflows are altered.
Append-only / tighten-only / overwrite-forbidden / same-root.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37ALJ_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37ALJ_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37ALJ_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37ALJ_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37ALJ_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37ALJ_links (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "Zcross" => p4Q2PZ37AIF_originalCrossingPartition H
local notation "kFloor" => p4Q2PZ37ALE_originalCrossingKernelFloor H
local notation "vBox" => p4Q2PZ37ALF_originalIdentityBoxVarianceFloor H
local notation "Vsrc" => p4Q2PZ37AHN_originalSource_HaarSecondMoment H
local notation "PW" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
    H 2 (by norm_num)
local notation "uH" => p4Q2PZ37AIW_originalNormalizedSourceTransfer H
local notation "mH" => p4Q2PZ37AIW_originalNormalizedNegativeMargin H

/-- Scalar lower-floor certificate for the exact original physical
one-slab operator, already proved by ALI. This derived scalar is not a
new physical partition function nor a substituted transfer operator. -/
def p4Q2PZ37ALJ_originalWilsonNormScalarFloor (beta : ℝ) : ℝ :=
  Zcross beta +
    (beta ^ 2 / 2) * (2 * kFloor beta * vBox) +
    (beta ^ 4 / 32) * (kFloor beta * (8 * vBox ^ 2))

local notation "D" => p4Q2PZ37ALJ_originalWilsonNormScalarFloor H

/-- At all real beta the scalar floor is positive, as it contains the
true strictly positive crossing partition and nonnegative corrections. -/
theorem p4Q2PZ37ALJ_originalWilsonNormScalarFloor_pos
    (beta : ℝ) : 0 < D beta := by
  have hZ : 0 < Zcross beta :=
    p4Q2PZ37AIF_originalCrossingPartition_pos H beta
  have hK : 0 < kFloor beta :=
    p4Q2PZ37ALE_originalCrossingKernelFloor_pos H beta
  have hBox : 0 < vBox :=
    p4Q2PZ37ALF_originalIdentityBoxVarianceFloor_pos H
  unfold p4Q2PZ37ALJ_originalWilsonNormScalarFloor
  positivity

/-- The original ALI second/fourth correction is strictly positive at
beta>0. No empirical Haar estimates are used in this strictness. -/
theorem p4Q2PZ37ALJ_originalWilsonNormScalarFloor_gt_crossing
    (beta : ℝ) (hbeta : 0 < beta) :
    Zcross beta < D beta := by
  have hK : 0 < kFloor beta :=
    p4Q2PZ37ALE_originalCrossingKernelFloor_pos H beta
  have hBox : 0 < vBox :=
    p4Q2PZ37ALF_originalIdentityBoxVarianceFloor_pos H
  have hTwo :
      0 < (beta ^ 2 / 2) * (2 * kFloor beta * vBox) := by
    positivity
  have hFour :
      0 ≤ (beta ^ 4 / 32) * (kFloor beta * (8 * vBox ^ 2)) := by
    positivity
  unfold p4Q2PZ37ALJ_originalWilsonNormScalarFloor
  linarith only [hTwo, hFour]

/-- Direct original physical transfer-norm floor, NOT a norm
equality, with both genuine endpoint Wilson spatial halfweights. -/
theorem p4Q2PZ37ALJ_originalPhysicalNorm_ge_scalarFloor
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Real.exp (-(beta * pH)) * D beta ≤ ‖PW beta hbeta‖ := by
  exact p4Q2PZ37ALI_originalPhysicalNorm_ge_enhancedFourthBox H beta hbeta

/-- New scalar certificate for the ratio of the *unchanged* crossing
partition to the *unchanged* physical operator norm. -/
def p4Q2PZ37ALJ_originalPartitionOverNormCeiling (beta : ℝ) : ℝ :=
  Real.exp (beta * pH) * (Zcross beta / D beta)

local notation "cap" => p4Q2PZ37ALJ_originalPartitionOverNormCeiling H

theorem p4Q2PZ37ALJ_originalPartitionOverNormCeiling_pos
    (beta : ℝ) : 0 < cap beta := by
  unfold p4Q2PZ37ALJ_originalPartitionOverNormCeiling
  exact mul_pos (Real.exp_pos _) <|
    div_pos (p4Q2PZ37AIF_originalCrossingPartition_pos H beta)
      (p4Q2PZ37ALJ_originalWilsonNormScalarFloor_pos H beta)

/-- The true original partition-to-physical-norm ratio is now bounded
by the ALI moment-enhanced scalar. All division signs have certified
strictly positive denominators. -/
theorem p4Q2PZ37ALJ_originalPartitionOverNorm_le_ceiling
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    Zcross beta / ‖PW beta hbeta‖ ≤ cap beta := by
  have hF := p4Q2PZ37ALJ_originalWilsonNormScalarFloor_pos H beta
  have hP :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 (by norm_num) beta hbeta
  have hNorm :=
    p4Q2PZ37ALJ_originalPhysicalNorm_ge_scalarFloor H beta hbeta
  have hCap := (p4Q2PZ37ALJ_originalPartitionOverNormCeiling_pos H beta).le
  have hCancelExp :
      Real.exp (beta * pH) * Real.exp (-(beta * pH)) = 1 := by
    rw [← Real.exp_add]
    simp
  have hCancelFraction :
      (Zcross beta / D beta) * D beta = Zcross beta :=
    div_mul_cancel₀ _ hF.ne'
  have hIdentity :
      cap beta * (Real.exp (-(beta * pH)) * D beta) = Zcross beta := by
    calc
      _ = (Real.exp (beta * pH) * Real.exp (-(beta * pH))) *
            ((Zcross beta / D beta) * D beta) := by
              unfold p4Q2PZ37ALJ_originalPartitionOverNormCeiling
              ring
      _ = Zcross beta := by rw [hCancelExp, hCancelFraction, one_mul]
  have hMul :=
    mul_le_mul_of_nonneg_left hNorm hCap
  apply (div_le_iff₀ hP).2
  exact hIdentity.symm.trans_le hMul

/-- The true ratio's new ceiling is strictly smaller than the old
AIW exponential envelope for every positive original coupling. -/
theorem p4Q2PZ37ALJ_originalPartitionOverNormCeiling_lt_old
    (beta : ℝ) (hbeta : 0 < beta) :
    cap beta < Real.exp (beta * pH) := by
  have hF := p4Q2PZ37ALJ_originalWilsonNormScalarFloor_pos H beta
  have hStrict :=
    p4Q2PZ37ALJ_originalWilsonNormScalarFloor_gt_crossing H beta hbeta
  have hDivision : Zcross beta / D beta < 1 := by
    apply (div_lt_one hF).2
    exact hStrict
  have hScaled := mul_lt_mul_of_pos_left hDivision (Real.exp_pos (beta * pH))
  simpa only [p4Q2PZ37ALJ_originalPartitionOverNormCeiling, mul_one]
    using hScaled

/-- The certified ratio ceiling contains the actual ratio, which is
at least one. Thus the improvement does not contradict AIW's
physical norm upper bound. -/
theorem p4Q2PZ37ALJ_originalPartitionOverNormCeiling_ge_one
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    1 ≤ cap beta := by
  exact (p4Q2PZ37AIW_originalCrossingPartition_div_norm_bounds
    H beta hbeta).1.trans
      (p4Q2PZ37ALJ_originalPartitionOverNorm_le_ceiling H beta hbeta)

/-- Upper bound on the genuine *norm-normalized* continuous signed ZW
source, with the unchanged pointwise original integral representative. -/
theorem p4Q2PZ37ALJ_originalNormalizedSource_abs_le_ceiling
    (beta : ℝ) (hbeta : 0 ≤ beta) (B : Cfg) :
    |uH beta hbeta B| ≤ (pH / 2) * cap beta := by
  have hCount := (p4Q2PZ37AHN_count_pos H).le
  exact (p4Q2PZ37AIW_originalNormalizedSourceTransfer_abs_le_relativeEnvelope
    H beta hbeta B).trans
      (mul_le_mul_of_nonneg_left
        (p4Q2PZ37ALJ_originalPartitionOverNorm_le_ceiling H beta hbeta)
        (div_nonneg hCount (by norm_num)))

/-- Original AIG margin, divided by exactly the original physical
operator norm, is bounded using the ALI scalar moment certificate.
Neither the negative set nor the margin is redefined. -/
theorem p4Q2PZ37ALJ_originalNormalizedNegativeMargin_le_ceiling
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    mH beta hbeta ≤
      (beta * Real.exp (-(2 * beta * pH)) * Vsrc / 2) * cap beta := by
  have hV := (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2.le
  have hFactor :
      0 ≤ beta * Real.exp (-(2 * beta * pH)) * Vsrc / 2 := by
    positivity
  have hRatio :=
    p4Q2PZ37ALJ_originalPartitionOverNorm_le_ceiling H beta hbeta
  rw [p4Q2PZ37AIW_originalNormalizedNegativeMargin_eq_relativeFactor H beta hbeta]
  exact mul_le_mul_of_nonneg_left hRatio hFactor

/-- Strict original normalized-margin improvement for positive beta,
relative to AIW's exp(-beta*p_H) physical norm bound. -/
theorem p4Q2PZ37ALJ_originalNormalizedNegativeMargin_lt_oldEnvelope
    (beta : ℝ) (hbeta : 0 < beta) :
    mH beta hbeta.le <
      beta * Real.exp (-(beta * pH)) * Vsrc / 2 := by
  have hV := (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  have hFactor :
      0 < beta * Real.exp (-(2 * beta * pH)) * Vsrc / 2 := by
    positivity
  have hCapLt :=
    p4Q2PZ37ALJ_originalPartitionOverNormCeiling_lt_old H beta hbeta
  have hExp :
      Real.exp (-(2 * beta * pH)) * Real.exp (beta * pH) =
        Real.exp (-(beta * pH)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    mH beta hbeta.le ≤
        (beta * Real.exp (-(2 * beta * pH)) * Vsrc / 2) * cap beta :=
      p4Q2PZ37ALJ_originalNormalizedNegativeMargin_le_ceiling
        H beta hbeta.le
    _ < (beta * Real.exp (-(2 * beta * pH)) * Vsrc / 2) *
          Real.exp (beta * pH) :=
      mul_lt_mul_of_pos_left hCapLt hFactor
    _ = beta * Real.exp (-(beta * pH)) * Vsrc / 2 := by
      calc
        _ = beta *
            (Real.exp (-(2 * beta * pH)) * Real.exp (beta * pH)) *
            Vsrc / 2 := by ring
        _ = _ := by rw [hExp]

/-- A sharper upper bound on the ORIGINAL AJA strict-negative-event
Haar budget. This is an upper bound on its actual original value,
NOT a new event, witness, top-energy inequality or gap theorem. -/
theorem p4Q2PZ37ALJ_originalAJABudget_le_improvedCeiling
    (beta : ℝ) (hbeta : 0 < beta) :
    (mH beta hbeta.le) ^ 2 *
      Measure.real muH
        {A : Cfg | uH beta hbeta.le A < -(mH beta hbeta.le)} ≤
    ((beta * Real.exp (-(2 * beta * pH)) * Vsrc / 2) * cap beta) ^ 2 *
      Measure.real muH
        {A : Cfg | uH beta hbeta.le A < -(mH beta hbeta.le)} := by
  have hm := p4Q2PZ37AIW_originalNormalizedNegativeMargin_pos H beta hbeta
  have hV := (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2.le
  have hCap := (p4Q2PZ37ALJ_originalPartitionOverNormCeiling_pos H beta).le
  have hFactor :
      0 ≤ beta * Real.exp (-(2 * beta * pH)) * Vsrc / 2 := by positivity
  have hCeil : 0 ≤
      (beta * Real.exp (-(2 * beta * pH)) * Vsrc / 2) * cap beta :=
    mul_nonneg hFactor hCap
  have hBound :=
    p4Q2PZ37ALJ_originalNormalizedNegativeMargin_le_ceiling H beta hbeta.le
  have hSq :
      (mH beta hbeta.le) ^ 2 ≤
        ((beta * Real.exp (-(2 * beta * pH)) * Vsrc / 2) * cap beta) ^ 2 := by
    have hProd := mul_nonneg (sub_nonneg.mpr hBound) (add_nonneg hCeil hm.le)
    nlinarith only [hProd]
  exact mul_le_mul_of_nonneg_right hSq ENNReal.toReal_nonneg

/-- The exactly unaltered fixed-coupling H22 ratio has a sharper
moment-certified denominator, with true original p22 = 292008. -/
theorem p4Q2PZ37ALJ_originalH22_fixedCoupling_partitionOverNorm
    :
    p4Q2PZ37AIF_originalCrossingPartition 22
        p4Q2PZ37ADC_fixedCoupling /
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
          22 2 (by norm_num) p4Q2PZ37ADC_fixedCoupling
            p4Q2PZ37ADC_fixedCoupling_pos.le‖ ≤
    Real.exp (p4Q2PZ37ADC_fixedCoupling * (292008 : ℝ)) *
      (p4Q2PZ37AIF_originalCrossingPartition 22
        p4Q2PZ37ADC_fixedCoupling /
        p4Q2PZ37ALJ_originalWilsonNormScalarFloor 22
          p4Q2PZ37ADC_fixedCoupling) := by
  have h :=
    p4Q2PZ37ALJ_originalPartitionOverNorm_le_ceiling
      22 p4Q2PZ37ADC_fixedCoupling p4Q2PZ37ADC_fixedCoupling_pos.le
  unfold p4Q2PZ37ALJ_originalPartitionOverNormCeiling at h
  rw [p4Q2PZ37AKX_originalH22_plaquetteCount_exact] at h
  exact h

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALJ_originalWilsonNormScalarFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALJ_originalWilsonNormScalarFloor_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALJ_originalWilsonNormScalarFloor_gt_crossing
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALJ_originalPhysicalNorm_ge_scalarFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALJ_originalPartitionOverNormCeiling
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALJ_originalPartitionOverNormCeiling_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALJ_originalPartitionOverNorm_le_ceiling
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALJ_originalPartitionOverNormCeiling_lt_old
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALJ_originalPartitionOverNormCeiling_ge_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALJ_originalNormalizedSource_abs_le_ceiling
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALJ_originalNormalizedNegativeMargin_le_ceiling
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALJ_originalNormalizedNegativeMargin_lt_oldEnvelope
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALJ_originalAJABudget_le_improvedCeiling
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALJ_originalH22_fixedCoupling_partitionOverNorm
