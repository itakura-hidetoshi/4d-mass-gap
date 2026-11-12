import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFixedCouplingQuadraticFrontierV5_PZ37AKP
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalHalfWeightedTopQuadraticAJANoGoV5_PZ37AKN
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AKQ: genuine H=14 original Haar-negative mass threshold

The original beta0=log(3/2)/64 and exact H=14 finite SU2 Wilson
operator P, S=P/||P||, signed centered source f0, Haar probability,
the TRUE full-top Q, negative region {u<-m}, and original AJA
certificate B=m^2 mu{u<-m} are never changed.

AKP shows that the earlier scalar Gaussian no-witness test
beta0^2*p_14/2<=log 4 is FALSE, not that an AJA witness exists.
We retain the actual negative-region Haar mass r in AKN's weighted
top pairing, obtaining the genuinely weaker (mass-sensitive) test

    r * Z_cross^2 <= 4*||P||  ==>  B <= ||Q f0||^2.

A further genuine original spatial-mean norm and AIQ Gaussian bound
show the sufficient test r*exp(beta^2*p_H/2)<=4. At H=14, the
original p_H=81000, so only the true original Haar-negative
region mass requires independent measurement/certification.
The corresponding strict mass inequality is necessary for a
finite AJA witness but does NOT suffice to construct one.

This leaf does NOT assume a numerical Haar mass value, does not
prove a witness or no-witness at H=14 without a mass input, and
does not prove a Hamiltonian or continuum Yang--Mills mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace Topology Classical ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4900000
set_option synthInstance.maxHeartbeats 1050000

/-- A real-algebra lemma that retains the ORIGINAL negative-region mass.
This is stronger than replacing the genuine Haar mass by one. -/
theorem real_weighted_haar_budget_le_top_of_mass_partition_akq
    (lambda a Z m F r : ℝ)
    (hlambda : 0 < lambda) (hr : 0 ≤ r)
    (hWeighted : r * Z ^ 2 ≤ 4 * lambda)
    (hMargin : m * lambda = a * Z / 2)
    (hOverlap : a ^ 2 ≤ lambda * F ^ 2) :
    m ^ 2 * r ≤ F ^ 2 := by
  have hZr : 0 ≤ Z ^ 2 * r := mul_nonneg (sq_nonneg Z) hr
  have hScaledOverlap :=
    mul_le_mul_of_nonneg_right hOverlap hZr
  have hScaledMass :=
    mul_le_mul_of_nonneg_left hWeighted
      (mul_nonneg hlambda.le (sq_nonneg F))
  have hExact : 4 * (m ^ 2 * r) * lambda ^ 2 =
      a ^ 2 * (Z ^ 2 * r) := by
    calc
      _ = 4 * (m * lambda) ^ 2 * r := by ring
      _ = 4 * (a * Z / 2) ^ 2 * r := by rw [hMargin]
      _ = a ^ 2 * (Z ^ 2 * r) := by ring
  have hScaled :
      4 * (m ^ 2 * r) * lambda ^ 2 ≤
        4 * F ^ 2 * lambda ^ 2 := by
    calc
      _ = a ^ 2 * (Z ^ 2 * r) := hExact
      _ ≤ (lambda * F ^ 2) * (Z ^ 2 * r) := hScaledOverlap
      _ = (lambda * F ^ 2) * (r * Z ^ 2) := by ring
      _ ≤ (lambda * F ^ 2) * (4 * lambda) := hScaledMass
      _ = 4 * F ^ 2 * lambda ^ 2 := by ring
  have hPos : 0 < (4 : ℝ) * lambda ^ 2 := by positivity
  apply (mul_le_mul_iff_of_pos_right hPos).mp
  nlinarith only [hScaled]

local notation "GQ" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AKQ_group : IsTopologicalGroup GQ :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AKQ_compact : CompactSpace GQ :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AKQ_countable : SecondCountableTopology GQ :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AKQ_measurable : MeasurableSpace GQ :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AKQ_borel : BorelSpace GQ :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AKQ_links (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "CfgQ" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muQ" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "fQ" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "pQ" => p4Q2PZ37AFZ_plaquetteCount H
local notation "VQ" => p4Q2PZ37AHN_originalSource_HaarSecondMoment H
local notation "ZQ" => p4Q2PZ37AIF_originalCrossingPartition H
local notation "PQ" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator H 2 (by norm_num)
local notation "SQ" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator H 2 (by norm_num)
local notation "psiQ" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector H 2 (by norm_num)
local notation "mQ" => p4Q2PZ37AIW_originalNormalizedNegativeMargin H
local notation "uQ" => p4Q2PZ37AIW_originalNormalizedSourceTransfer H
local notation "beta0" => p4Q2PZ37ADC_fixedCoupling

local instance p4Q2PZ37AKQ_probability : IsProbabilityMeasure muQ := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- A direct original Haar-negative mass and crossing-partition test.
No replacement by the full Haar mass one is made. -/
theorem p4Q2PZ37AKQ_originalBudget_le_fullTop_of_weightedHaarMass
    (beta : ℝ) (hbeta : 0 < beta)
    (hMass :
      Measure.real muQ
        {A : CfgQ | uQ beta hbeta.le A < -(mQ beta hbeta.le)} *
          (ZQ beta) ^ 2 ≤ 4 * ‖PQ beta hbeta.le‖) :
    (mQ beta hbeta.le) ^ 2 *
      Measure.real muQ
        {A : CfgQ | uQ beta hbeta.le A < -(mQ beta hbeta.le)} ≤
      ‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2 := by
  let lambda : ℝ := ‖PQ beta hbeta.le‖
  let a : ℝ := beta * Real.exp (-(2 * beta * pQ)) * VQ
  let F : ℝ := inner ℝ fQ (psiQ beta hbeta.le)
  let r : ℝ := Measure.real muQ
    {A : CfgQ | uQ beta hbeta.le A < -(mQ beta hbeta.le)}
  have hNorm : 0 < lambda :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 (by norm_num) beta hbeta.le
  have hr : 0 ≤ r := ENNReal.toReal_nonneg
  have hm : mQ beta hbeta.le * lambda = a * ZQ beta / 2 := by
    rw [p4Q2PZ37AIW_originalNormalizedNegativeMargin_eq_relativeFactor H beta hbeta.le]
    change (a / 2 * (ZQ beta / lambda)) * lambda = a * ZQ beta / 2
    field_simp [hNorm.ne']
  have ha : a ^ 2 ≤ lambda * F ^ 2 :=
    p4Q2PZ37AKN_originalOverlap_scaledHalfWeightedFloor H beta hbeta
  have hBudget : (mQ beta hbeta.le) ^ 2 * r ≤ F ^ 2 :=
    real_weighted_haar_budget_le_top_of_mass_partition_akq
      lambda a (ZQ beta) (mQ beta hbeta.le) F r
      hNorm hr hMass hm ha
  exact hBudget.trans
    (p4Q2PZ37AKK_originalNonnegativeTop_overlap_sq_le_fullTop H beta hbeta)

/-- The actual original finite-power AJA strict witness is excluded
whenever the measured genuine Haar-negative mass satisfies the test. -/
theorem p4Q2PZ37AKQ_original_no_AJA_witness_of_weightedHaarMass
    (beta : ℝ) (hbeta : 0 < beta)
    (hMass :
      Measure.real muQ
        {A : CfgQ | uQ beta hbeta.le A < -(mQ beta hbeta.le)} *
          (ZQ beta) ^ 2 ≤ 4 * ‖PQ beta hbeta.le‖) :
    ¬ ∃ n : ℕ, ‖((SQ beta hbeta.le) ^ n) fQ‖ ^ 2 <
      (mQ beta hbeta.le) ^ 2 *
        Measure.real muQ
          {A : CfgQ | uQ beta hbeta.le A < -(mQ beta hbeta.le)} := by
  rintro ⟨n, hn⟩
  exact (not_lt_of_ge
    ((p4Q2PZ37AKQ_originalBudget_le_fullTop_of_weightedHaarMass
        H beta hbeta hMass).trans
      (p4Q2PZ37AJH_originalFullTop_norm_sq_le_transferPower
        H beta hbeta n))) hn

/-- Original spatial mean norm floor eliminates the expensive physical
operator norm from the weighted Haar test without replacing the model. -/
theorem p4Q2PZ37AKQ_original_no_AJA_witness_of_partitionHaarMass
    (beta : ℝ) (hbeta : 0 < beta)
    (hMass :
      Measure.real muQ
        {A : CfgQ | uQ beta hbeta.le A < -(mQ beta hbeta.le)} *
          ZQ beta ≤ 4 * Real.exp (-(beta * pQ))) :
    ¬ ∃ n : ℕ, ‖((SQ beta hbeta.le) ^ n) fQ‖ ^ 2 <
      (mQ beta hbeta.le) ^ 2 *
        Measure.real muQ
          {A : CfgQ | uQ beta hbeta.le A < -(mQ beta hbeta.le)} := by
  have hZ : 0 ≤ ZQ beta :=
    (p4Q2PZ37AIF_originalCrossingPartition_pos H beta).le
  have hMult := mul_le_mul_of_nonneg_right hMass hZ
  have hNorm :=
    p4Q2PZ37AIW_originalPhysicalTransfer_norm_ge_spatialMean H beta hbeta.le
  apply p4Q2PZ37AKQ_original_no_AJA_witness_of_weightedHaarMass H beta hbeta
  calc
    _ = (Measure.real muQ
          {A : CfgQ | uQ beta hbeta.le A < -(mQ beta hbeta.le)} *
        ZQ beta) * ZQ beta := by ring
    _ ≤ (4 * Real.exp (-(beta * pQ))) * ZQ beta := hMult
    _ = 4 * (Real.exp (-(beta * pQ)) * ZQ beta) := by ring
    _ ≤ 4 * ‖PQ beta hbeta.le‖ :=
      mul_le_mul_of_nonneg_left hNorm (by norm_num)

/-- Gaussian control of the original crossing partition reduces the
remaining H=14 test to the TRUE Haar-negative region mass alone. -/
theorem p4Q2PZ37AKQ_original_no_AJA_witness_of_gaussianHaarMass
    (beta : ℝ) (hbeta : 0 < beta)
    (hMass :
      Measure.real muQ
        {A : CfgQ | uQ beta hbeta.le A < -(mQ beta hbeta.le)} *
        Real.exp (beta ^ 2 * pQ / 2) ≤ 4) :
    ¬ ∃ n : ℕ, ‖((SQ beta hbeta.le) ^ n) fQ‖ ^ 2 <
      (mQ beta hbeta.le) ^ 2 *
        Measure.real muQ
          {A : CfgQ | uQ beta hbeta.le A < -(mQ beta hbeta.le)} := by
  have hr : 0 ≤ Measure.real muQ
      {A : CfgQ | uQ beta hbeta.le A < -(mQ beta hbeta.le)} :=
    ENNReal.toReal_nonneg
  have hZ :
      ZQ beta ≤ Real.exp (-(beta * pQ)) *
        Real.exp (beta ^ 2 * pQ / 2) := by
    calc
      ZQ beta ≤ Real.exp (pQ * (-beta + beta ^ 2 / 2)) :=
        p4Q2PZ37AIQ_originalCrossingPartition_le_gaussian H beta
      _ = Real.exp (-(beta * pQ)) *
          Real.exp (beta ^ 2 * pQ / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hSimpler :
      Measure.real muQ
        {A : CfgQ | uQ beta hbeta.le A < -(mQ beta hbeta.le)} *
        ZQ beta ≤ 4 * Real.exp (-(beta * pQ)) := by
    calc
      _ ≤ (Measure.real muQ
            {A : CfgQ | uQ beta hbeta.le A < -(mQ beta hbeta.le)}) *
          (Real.exp (-(beta * pQ)) *
            Real.exp (beta ^ 2 * pQ / 2)) :=
        mul_le_mul_of_nonneg_left hZ hr
      _ = Real.exp (-(beta * pQ)) *
        ((Measure.real muQ
          {A : CfgQ | uQ beta hbeta.le A < -(mQ beta hbeta.le)}) *
          Real.exp (beta ^ 2 * pQ / 2)) := by ring
      _ ≤ Real.exp (-(beta * pQ)) * 4 :=
        mul_le_mul_of_nonneg_left hMass (Real.exp_pos _).le
      _ = 4 * Real.exp (-(beta * pQ)) := by ring
  exact p4Q2PZ37AKQ_original_no_AJA_witness_of_partitionHaarMass
    H beta hbeta hSimpler

/-- At the exact original H=14 and beta0, the Gaussian-adjusted true
negative-region Haar mass is the only additional test datum. -/
theorem p4Q2PZ37AKQ_originalH14_no_AJA_witness_of_genuineHaarMass
    (hMass :
      Measure.real (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure 14 2)
        {A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration 14 2 |
          p4Q2PZ37AIW_originalNormalizedSourceTransfer 14
            beta0 p4Q2PZ37ADC_fixedCoupling_pos.le A <
            -(p4Q2PZ37AIW_originalNormalizedNegativeMargin 14
              beta0 p4Q2PZ37ADC_fixedCoupling_pos.le)} *
        Real.exp (beta0 ^ 2 * (81000 : ℝ) / 2) ≤ 4) :
    ¬ ∃ n : ℕ,
      ‖((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          14 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le) ^ n)
        (p4Q2PZ37ZW_originalCenteredPhysicalDirection 14)‖ ^ 2 <
      (p4Q2PZ37AIW_originalNormalizedNegativeMargin 14
        beta0 p4Q2PZ37ADC_fixedCoupling_pos.le) ^ 2 *
        Measure.real (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure 14 2)
          {A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration 14 2 |
            p4Q2PZ37AIW_originalNormalizedSourceTransfer 14
              beta0 p4Q2PZ37ADC_fixedCoupling_pos.le A <
              -(p4Q2PZ37AIW_originalNormalizedNegativeMargin 14
                beta0 p4Q2PZ37ADC_fixedCoupling_pos.le)} := by
  have hp : (p4Q2PZ37AFZ_plaquetteCount 14 : ℝ) = 81000 := by
    rw [p4Q2PZ37AIB_plaquetteCount_exact]
    norm_num
  have hExact :
      Measure.real (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure 14 2)
        {A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration 14 2 |
          p4Q2PZ37AIW_originalNormalizedSourceTransfer 14
            beta0 p4Q2PZ37ADC_fixedCoupling_pos.le A <
            -(p4Q2PZ37AIW_originalNormalizedNegativeMargin 14
              beta0 p4Q2PZ37ADC_fixedCoupling_pos.le)} *
        Real.exp (beta0 ^ 2 * (p4Q2PZ37AFZ_plaquetteCount 14) / 2) ≤ 4 := by
    simpa only [hp] using hMass
  exact p4Q2PZ37AKQ_original_no_AJA_witness_of_gaussianHaarMass
    14 beta0 p4Q2PZ37ADC_fixedCoupling_pos hExact

/-- A genuine original H14 finite-power witness would NECESSARILY force
the Gaussian-adjusted true Haar-negative mass above four.
No such witness or measured mass is asserted here. -/
theorem p4Q2PZ37AKQ_originalH14_witness_requires_genuineHaarMass_gt_four
    (hWitness :
      ∃ n : ℕ,
      ‖((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          14 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le) ^ n)
        (p4Q2PZ37ZW_originalCenteredPhysicalDirection 14)‖ ^ 2 <
      (p4Q2PZ37AIW_originalNormalizedNegativeMargin 14
        beta0 p4Q2PZ37ADC_fixedCoupling_pos.le) ^ 2 *
        Measure.real (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure 14 2)
          {A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration 14 2 |
            p4Q2PZ37AIW_originalNormalizedSourceTransfer 14
              beta0 p4Q2PZ37ADC_fixedCoupling_pos.le A <
              -(p4Q2PZ37AIW_originalNormalizedNegativeMargin 14
                beta0 p4Q2PZ37ADC_fixedCoupling_pos.le)}) :
    4 <
      Measure.real (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure 14 2)
        {A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration 14 2 |
          p4Q2PZ37AIW_originalNormalizedSourceTransfer 14
            beta0 p4Q2PZ37ADC_fixedCoupling_pos.le A <
            -(p4Q2PZ37AIW_originalNormalizedNegativeMargin 14
              beta0 p4Q2PZ37ADC_fixedCoupling_pos.le)} *
        Real.exp (beta0 ^ 2 * (81000 : ℝ) / 2) := by
  by_contra hn
  have hMass : _ ≤ (4 : ℝ) := le_of_not_gt hn
  exact (p4Q2PZ37AKQ_originalH14_no_AJA_witness_of_genuineHaarMass hMass)
    hWitness

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.real_weighted_haar_budget_le_top_of_mass_partition_akq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKQ_originalBudget_le_fullTop_of_weightedHaarMass
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKQ_original_no_AJA_witness_of_weightedHaarMass
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKQ_original_no_AJA_witness_of_partitionHaarMass
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKQ_original_no_AJA_witness_of_gaussianHaarMass
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKQ_originalH14_no_AJA_witness_of_genuineHaarMass
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKQ_originalH14_witness_requires_genuineHaarMass_gt_four
