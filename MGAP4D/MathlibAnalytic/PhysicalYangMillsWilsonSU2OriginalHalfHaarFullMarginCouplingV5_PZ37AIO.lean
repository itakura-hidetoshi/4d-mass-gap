import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalIdentityNegativeAllPositiveCouplingV5_PZ37AIN
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AIO — half Haar mass at the unchanged full negative margin

Keep the ORIGINAL complete SU(2) Wilson slab action, both spatial halfweights,
signed ZW physical L2 source and its existing continuous representative, genuine
normalized spatial product Haar, and AIG's original epsilon and strict region.

On the original source-nonpositive set, W_H(B)<=p_H. Retaining AIN's quadratic
term therefore gives the quantitative physical-transfer bound
  T_beta f0(B) <= -delta_H(beta),
  delta_H(beta) = beta*exp(-7*beta*p_H/2)*V_H.
The exact old-margin identity is
  2*epsilon_H(beta) = Zcross_H(beta)*exp(3*beta*p_H/2)*delta_H(beta).
Consequently Zcross_H(beta)*exp(3*beta*p_H/2)<2 implies inclusion of the
source-nonpositive set in the SAME original full-margin negative region.
AIN's actual source-odd Haar symmetry supplies the lower mass 1/2.

AIL's already proved Zcross<=1 yields the elementary nonempty OPEN interval
  0 < beta < 2*log(2)/(3*p_H).
This cutoff is strictly above AIM's old cubic cutoff, although the old result
gives mass one on its smaller interval. At H=0 the unchanged fixed beta0 lies
in the new interval. No claim at the new upper endpoint, for arbitrary beta,
or for fixed beta0 at every H is inferred from this sufficient condition.

No existing definition, assumption, theorem, root, workflow, toolchain pin,
or resource budget changes. No volume-uniform positive amplitude, coercivity,
Hamiltonian spectral gap, or continuum mass gap follows from this leaf.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AIO_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AIO_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AIO_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AIO_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AIO_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "f0" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "fCont" => p4Q2PZ37AFZ_originalCenteredContinuous H
local notation "Vsrc" => p4Q2PZ37AHN_originalSource_HaarSecondMoment H
local notation "W" => periodicHypercubicEvenSpecialUnitarySpatialSliceWilsonAction H 2
local notation "KC" => periodicHypercubicEvenSpecialUnitaryTemporalGaugeCrossingKernel H 2
local notation "T" => decomposableOneSliceTransferIntegral H 2
local notation "Zcross" => p4Q2PZ37AIF_originalCrossingPartition H
local notation "r" => p4Q2PZ37ABN_originalTemporalWilsonCoefficient
local notation "margin" => p4Q2PZ37AIG_originalNegativeTransferMargin H
local notation "Region" => p4Q2PZ37AIG_originalNegativeTransferRegion H
local notation "beta0" => p4Q2PZ37ADC_fixedCoupling

local instance p4Q2PZ37AIO_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- A quantitative amplitude on the source-nonpositive set. This is NOT a
replacement definition for AIG's original margin. -/
def p4Q2PZ37AIO_sourceNonpositiveVarianceFloor (beta : ℝ) : ℝ :=
  beta * Real.exp (-(7 * beta * pH / 2)) * Vsrc

local notation "delta" => p4Q2PZ37AIO_sourceNonpositiveVarianceFloor H

theorem p4Q2PZ37AIO_sourceNonpositiveVarianceFloor_pos
    (beta : ℝ) (hbeta : 0 < beta) : 0 < delta beta := by
  exact mul_pos (mul_pos hbeta (Real.exp_pos _))
    (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2

/-- The original source-identity improves the right action bound on this
particular set; no bound for other boundaries is inserted. -/
theorem p4Q2PZ37AIO_originalAction_le_count_of_source_nonpos
    (B : Cfg) (hB : fCont B ≤ 0) : W B ≤ pH := by
  rw [p4Q2PZ37AGN_originalCenteredContinuous_eq H B] at hB
  linarith only [hB]

/-- Retain the actual crossing-weighted second moment in AIN, then use its
proved full-crossing lower bound against the genuine positive Haar variance. -/
theorem p4Q2PZ37AIO_originalRightWeightedTransfer_le_negativeVariance
    (beta : ℝ) (hbeta : 0 < beta) (B : Cfg) (hB : fCont B ≤ 0) :
    Real.exp ((beta / 2) * W B) * T beta f0 B ≤
      -(beta * Real.exp (-(3 * beta * pH)) * Vsrc) := by
  have hSource : Zcross beta * r beta ^ 4 * fCont B ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos
      (mul_pos (p4Q2PZ37AIF_originalCrossingPartition_pos H beta)
        (pow_pos (p4Q2PZ37ABN_originalTemporalWilsonCoefficient_pos beta hbeta) 4)).le hB
  have hSourceScaled := mul_nonpos_of_nonneg_of_nonpos
    (Real.exp_pos (-(beta * (pH / 2)))).le hSource
  have hCoefficient : 0 ≤ Real.exp (-(beta * (pH / 2))) *
      (beta * Real.exp (-(beta * (pH / 2)))) := by positivity
  have hSecond := mul_le_mul_of_nonneg_left
    (p4Q2PZ37AIN_originalCrossingSecondMoment_lower H beta hbeta.le B) hCoefficient
  have hExp : Real.exp (-(beta * (pH / 2))) *
      (Real.exp (-(beta * (pH / 2))) * Real.exp (-(2 * beta * pH))) =
        Real.exp (-(3 * beta * pH)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hFloor : Real.exp (-(beta * (pH / 2))) *
      (beta * Real.exp (-(beta * (pH / 2)))) *
        (Real.exp (-(2 * beta * pH)) * Vsrc) =
      beta * Real.exp (-(3 * beta * pH)) * Vsrc := by
    calc
      _ = beta * (Real.exp (-(beta * (pH / 2))) *
          (Real.exp (-(beta * (pH / 2))) * Real.exp (-(2 * beta * pH)))) * Vsrc := by ring
      _ = _ := by rw [hExp]
  calc
    _ ≤ Real.exp (-(beta * (pH / 2))) *
        (Zcross beta * r beta ^ 4 * fCont B -
          (beta * Real.exp (-(beta * (pH / 2)))) *
            (∫ A : Cfg, KC beta A B * (fCont A) ^ 2 ∂muH)) :=
      p4Q2PZ37AIN_originalRightWeightedTransfer_quadraticUpper H beta hbeta.le B
    _ ≤ -(Real.exp (-(beta * (pH / 2))) *
        (beta * Real.exp (-(beta * (pH / 2)))) *
          (∫ A : Cfg, KC beta A B * (fCont A) ^ 2 ∂muH)) := by
      nlinarith only [hSourceScaled]
    _ ≤ -(Real.exp (-(beta * (pH / 2))) *
        (beta * Real.exp (-(beta * (pH / 2)))) *
          (Real.exp (-(2 * beta * pH)) * Vsrc)) := neg_le_neg hSecond
    _ = _ := by rw [hFloor]

/-- Restore the ORIGINAL right halfweight with W(B)<=p_H. Both halfweights
and the complete crossing action contribute to the exponent 7/2. -/
theorem p4Q2PZ37AIO_originalTransfer_le_negativeVarianceFloor
    (beta : ℝ) (hbeta : 0 < beta) (B : Cfg) (hB : fCont B ≤ 0) :
    T beta f0 B ≤ -(delta beta) := by
  have hW := p4Q2PZ37AIO_originalAction_le_count_of_source_nonpos H B hB
  have hInverse : Real.exp (-(beta * pH / 2)) ≤ Real.exp (-(beta / 2) * W B) := by
    apply Real.exp_le_exp.mpr
    have hMul := mul_le_mul_of_nonneg_left hW hbeta.le
    nlinarith only [hMul]
  have hNonpos : -(beta * Real.exp (-(3 * beta * pH)) * Vsrc) ≤ 0 :=
    neg_nonpos.mpr (mul_pos (mul_pos hbeta (Real.exp_pos _))
      (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2).le
  have hCancel : Real.exp (-(beta / 2) * W B) *
      Real.exp ((beta / 2) * W B) = 1 := by
    have hArg : -(beta / 2) * W B + (beta / 2) * W B = 0 := by ring
    rw [← Real.exp_add, hArg, Real.exp_zero]
  have hExp : Real.exp (-(beta * pH / 2)) * Real.exp (-(3 * beta * pH)) =
      Real.exp (-(7 * beta * pH / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    T beta f0 B = Real.exp (-(beta / 2) * W B) *
        (Real.exp ((beta / 2) * W B) * T beta f0 B) := by
      rw [← mul_assoc, hCancel, one_mul]
    _ ≤ Real.exp (-(beta / 2) * W B) *
        (-(beta * Real.exp (-(3 * beta * pH)) * Vsrc)) :=
      mul_le_mul_of_nonneg_left
        (p4Q2PZ37AIO_originalRightWeightedTransfer_le_negativeVariance H beta hbeta B hB)
        (Real.exp_pos _).le
    _ ≤ Real.exp (-(beta * pH / 2)) *
        (-(beta * Real.exp (-(3 * beta * pH)) * Vsrc)) :=
      mul_le_mul_of_nonpos_right hInverse hNonpos
    _ = -(beta * (Real.exp (-(beta * pH / 2)) *
        Real.exp (-(3 * beta * pH))) * Vsrc) := by ring
    _ = -(delta beta) := by rw [hExp]; rfl

/-- Exact identity with the UNCHANGED AIG epsilon, before imposing any
coupling condition. Neither its partition nor its variance is replaced. -/
theorem p4Q2PZ37AIO_originalNegativeMargin_ratio_identity (beta : ℝ) :
    2 * margin beta =
      (Zcross beta * Real.exp (3 * beta * pH / 2)) * delta beta := by
  have hExp : Real.exp (3 * beta * pH / 2) * Real.exp (-(7 * beta * pH / 2)) =
      Real.exp (-(2 * beta * pH)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold p4Q2PZ37AIG_originalNegativeTransferMargin
    p4Q2PZ37AIO_sourceNonpositiveVarianceFloor
  rw [← hExp]
  ring

/-- Strict comparison is PROVED from the specified actual-partition
condition; it is not supplied as an assumption on the old negative region. -/
theorem p4Q2PZ37AIO_originalNegativeMargin_lt_varianceFloor
    (beta : ℝ) (hbeta : 0 < beta)
    (hCoupling : Zcross beta * Real.exp (3 * beta * pH / 2) < 2) :
    margin beta < delta beta := by
  have hScaled := mul_lt_mul_of_pos_right hCoupling
    (p4Q2PZ37AIO_sourceNonpositiveVarianceFloor_pos H beta hbeta)
  have hIdentity := p4Q2PZ37AIO_originalNegativeMargin_ratio_identity H beta
  nlinarith only [hScaled, hIdentity]

/-- Includes the source zero set, without a zero-set measure assumption. -/
theorem p4Q2PZ37AIO_originalSource_nonpos_subset_fullNegativeRegion
    (beta : ℝ) (hbeta : 0 < beta)
    (hCoupling : Zcross beta * Real.exp (3 * beta * pH / 2) < 2) :
    {B : Cfg | fCont B ≤ 0} ⊆ Region beta := by
  intro B hB
  exact (p4Q2PZ37AIO_originalTransfer_le_negativeVarianceFloor H beta hbeta B hB).trans_lt
    (neg_lt_neg (p4Q2PZ37AIO_originalNegativeMargin_lt_varianceFloor H beta hbeta hCoupling))

/-- The half-Haar lower bound now applies to AIG's original full epsilon. -/
theorem p4Q2PZ37AIO_originalFullNegativeRegion_Haar_half_of_partition
    (beta : ℝ) (hbeta : 0 < beta)
    (hCoupling : Zcross beta * Real.exp (3 * beta * pH / 2) < 2) :
    (1 / 2 : ℝ≥0∞) ≤ muH (Region beta) :=
  (p4Q2PZ37AIN_originalSource_nonpos_Haar_half H).trans
    (measure_mono
      (p4Q2PZ37AIO_originalSource_nonpos_subset_fullNegativeRegion H beta hbeta hCoupling))

theorem p4Q2PZ37AIO_originalFullNegativeRegion_realHaar_half_of_partition
    (beta : ℝ) (hbeta : 0 < beta)
    (hCoupling : Zcross beta * Real.exp (3 * beta * pH / 2) < 2) :
    (1 / 2 : ℝ) ≤ Measure.real muH (Region beta) := by
  have h := ENNReal.toReal_mono (measure_ne_top muH (Region beta))
    (p4Q2PZ37AIO_originalFullNegativeRegion_Haar_half_of_partition H beta hbeta hCoupling)
  simpa [Measure.real] using h

/-- Entirely elementary OPEN upper endpoint. No source or partition integral
or small-ball constant occurs in this sufficient coupling cutoff. -/
def p4Q2PZ37AIO_halfHaarCouplingCutoff : ℝ :=
  2 * Real.log 2 / (3 * pH)

local notation "cutoff" => p4Q2PZ37AIO_halfHaarCouplingCutoff H

theorem p4Q2PZ37AIO_halfHaarCouplingCutoff_pos : 0 < cutoff := by
  have hp := p4Q2PZ37AHN_count_pos H
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold p4Q2PZ37AIO_halfHaarCouplingCutoff
  positivity

/-- AIL's exact original partition upper bound supplies a strictly verified
condition on the elementary open interval. No endpoint inclusion is asserted. -/
theorem p4Q2PZ37AIO_originalPartitionCondition_of_below_cutoff
    (beta : ℝ) (hbeta : 0 ≤ beta) (hSmall : beta < cutoff) :
    Zcross beta * Real.exp (3 * beta * pH / 2) < 2 := by
  have hp := p4Q2PZ37AHN_count_pos H
  have hDen : 0 < 3 * pH := by positivity
  have hProduct : beta * (3 * pH) < 2 * Real.log 2 :=
    (lt_div_iff₀ hDen).mp hSmall
  have hArg : 3 * beta * pH / 2 < Real.log 2 := by nlinarith only [hProduct]
  have hExp : Real.exp (3 * beta * pH / 2) < 2 := by
    calc
      _ < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr hArg
      _ = 2 := Real.exp_log (by norm_num)
  calc
    _ ≤ 1 * Real.exp (3 * beta * pH / 2) :=
      mul_le_mul_of_nonneg_right
        (p4Q2PZ37AIL_originalCrossingPartition_le_one H beta hbeta) (Real.exp_pos _).le
    _ < 2 := by simpa only [one_mul] using hExp

theorem p4Q2PZ37AIO_originalSource_nonpos_subset_fullNegativeRegion_of_below_cutoff
    (beta : ℝ) (hbeta : 0 < beta) (hSmall : beta < cutoff) :
    {B : Cfg | fCont B ≤ 0} ⊆ Region beta :=
  p4Q2PZ37AIO_originalSource_nonpos_subset_fullNegativeRegion H beta hbeta
    (p4Q2PZ37AIO_originalPartitionCondition_of_below_cutoff H beta hbeta.le hSmall)

theorem p4Q2PZ37AIO_originalFullNegativeRegion_Haar_half
    (beta : ℝ) (hbeta : 0 < beta) (hSmall : beta < cutoff) :
    (1 / 2 : ℝ≥0∞) ≤ muH (Region beta) :=
  p4Q2PZ37AIO_originalFullNegativeRegion_Haar_half_of_partition H beta hbeta
    (p4Q2PZ37AIO_originalPartitionCondition_of_below_cutoff H beta hbeta.le hSmall)

theorem p4Q2PZ37AIO_originalFullNegativeRegion_realHaar_half
    (beta : ℝ) (hbeta : 0 < beta) (hSmall : beta < cutoff) :
    (1 / 2 : ℝ) ≤ Measure.real muH (Region beta) :=
  p4Q2PZ37AIO_originalFullNegativeRegion_realHaar_half_of_partition H beta hbeta
    (p4Q2PZ37AIO_originalPartitionCondition_of_below_cutoff H beta hbeta.le hSmall)

/-- The new half-Haar interval strictly contains AIM's old cubic interval.
The old mass-one conclusion on that smaller interval is retained unchanged. -/
theorem p4Q2PZ37AIO_oldCubicSmallCoupling_lt_halfHaarCutoff :
    p4Q2PZ37AIM_elementaryCubicSmallCoupling H < cutoff := by
  have hp := p4Q2PZ37AHN_count_pos H
  have hDenOld : 0 < 16 * pH + 1 := by positivity
  have hDenNew : 0 < 3 * pH := by positivity
  have hlog := Real.one_sub_inv_le_log_of_pos (x := (2 : ℝ)) (by norm_num)
  norm_num at hlog
  calc
    p4Q2PZ37AIM_elementaryCubicSmallCoupling H ≤ 1 / (16 * pH + 1) :=
      div_le_div_of_nonneg_right (p4Q2PZ37AIM_identityHaarRoot_le_one H) hDenOld.le
    _ < 1 / (3 * pH) := (div_lt_div_iff₀ hDenOld hDenNew).mpr (by nlinarith only [hp])
    _ ≤ 2 * Real.log 2 / (3 * pH) :=
      div_le_div_of_nonneg_right (by linarith only [hlog]) hDenNew.le
    _ = cutoff := rfl

/-- A concrete positive interior coupling for every finite H. -/
theorem p4Q2PZ37AIO_halfCutoff_certificate :
    0 < cutoff / 2 ∧
      (1 / 2 : ℝ) ≤ Measure.real muH (Region (cutoff / 2)) := by
  have hPos := p4Q2PZ37AIO_halfHaarCouplingCutoff_pos H
  refine ⟨by linarith only [hPos], ?_⟩
  exact p4Q2PZ37AIO_originalFullNegativeRegion_realHaar_half H (cutoff / 2)
    (by linarith only [hPos]) (by linarith only [hPos])

/-- At the original minimal finite volume, beta0 is inside the new interval.
This statement does not assert the same condition at all larger volumes. -/
theorem p4Q2PZ37AIO_originalFixedCoupling_lt_cutoff_at_zero :
    beta0 < p4Q2PZ37AIO_halfHaarCouplingCutoff 0 := by
  have hp0 : p4Q2PZ37AFZ_plaquetteCount 0 = 24 := by
    rw [p4Q2PZ37AIB_plaquetteCount_exact]
    norm_num
  have hlog : Real.log (3 / 2 : ℝ) < Real.log 2 :=
    Real.log_lt_log (by norm_num) (by norm_num)
  have hlogPos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold p4Q2PZ37AIO_halfHaarCouplingCutoff p4Q2PZ37ADC_fixedCoupling
  rw [hp0]
  norm_num
  linarith only [hlog, hlogPos]

theorem p4Q2PZ37AIO_originalFixedFullNegativeRegion_realHaar_half_at_zero :
    (1 / 2 : ℝ) ≤ Measure.real
      (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure 0 2)
      (p4Q2PZ37AIG_originalNegativeTransferRegion 0 beta0) :=
  p4Q2PZ37AIO_originalFullNegativeRegion_realHaar_half
    0 beta0 p4Q2PZ37ADC_fixedCoupling_pos
    p4Q2PZ37AIO_originalFixedCoupling_lt_cutoff_at_zero

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIO_sourceNonpositiveVarianceFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIO_sourceNonpositiveVarianceFloor_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIO_originalAction_le_count_of_source_nonpos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIO_originalRightWeightedTransfer_le_negativeVariance
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIO_originalTransfer_le_negativeVarianceFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIO_originalNegativeMargin_ratio_identity
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIO_originalNegativeMargin_lt_varianceFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIO_originalSource_nonpos_subset_fullNegativeRegion
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIO_originalFullNegativeRegion_Haar_half_of_partition
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIO_originalFullNegativeRegion_realHaar_half_of_partition
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIO_halfHaarCouplingCutoff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIO_halfHaarCouplingCutoff_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIO_originalPartitionCondition_of_below_cutoff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIO_originalSource_nonpos_subset_fullNegativeRegion_of_below_cutoff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIO_originalFullNegativeRegion_Haar_half
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIO_originalFullNegativeRegion_realHaar_half
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIO_oldCubicSmallCoupling_lt_halfHaarCutoff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIO_halfCutoff_certificate
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIO_originalFixedCoupling_lt_cutoff_at_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIO_originalFixedFullNegativeRegion_realHaar_half_at_zero
