import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalH14ExactCharacterMomentAJANoGoV5_PZ37AKS
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AKT — genuine original fixed beta0 AJA no-witness through H=16

AKS proves the original SU(2) normalized Haar one-link character has
second moment 1/4 and establishes the genuine original crossing
partition inequality Z_H(beta)<=exp(p_H*(-beta+beta^2/4)) for beta in
[0,1]. This is the UNCHANGED AIF partition; it is not a new Gaussian
measure or an assumption of plaquette independence.

This leaf extends the exact same original-model AKS/AKQ argument from
H=14 to all finite H<=16 using ONLY the original plaquette count
p_H=24*(H+1)^3, the original beta0=log(3/2)/64 and the existing
certified bounds beta0<=1/156 and 11/8<=log4.

The original finite SU(2) Wilson action, normalized Haar probability,
physical P, normalized S, signed ZW centered source f0, AIG negative
margin m, original negative Haar region, full top projection and strict
AJA budget B=m^2*mu{u<-m} are all preserved literally.

For H<=16 the *actual* Haar mass r_H is at most one because the genuine
Haar measure is a probability. Then AKS's original partition bound and
beta0^2*p_H/4<=log4 yield AKQ's original partition-Haar sufficient
criterion without an unknown numerical r_H input.

No numerical Haar negative mass, Delta_H sign, H-uniform coercivity,
Hamiltonian mass gap or 4D continuum Yang--Mills mass gap is asserted.
This finite-H no-witness theorem is not an H-uniform spectral theorem.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace Topology Classical ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4900000
set_option synthInstance.maxHeartbeats 1050000

local notation "GT" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AKT_group : IsTopologicalGroup GT :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AKT_compact : CompactSpace GT :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AKT_countable : SecondCountableTopology GT :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AKT_measurable : MeasurableSpace GT :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AKT_borel : BorelSpace GT :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AKT_links (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "CfgT" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muT" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "pT" => p4Q2PZ37AFZ_plaquetteCount H
local notation "ZT" => p4Q2PZ37AIF_originalCrossingPartition H
local notation "beta0" => p4Q2PZ37ADC_fixedCoupling
local notation "fT" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "ST" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H 2 (by norm_num)
local notation "uT" => p4Q2PZ37AIW_originalNormalizedSourceTransfer H
local notation "mT" => p4Q2PZ37AIW_originalNormalizedNegativeMargin H
local notation "ET" =>
  (fun A : CfgT =>
    uT beta0 p4Q2PZ37ADC_fixedCoupling_pos.le A <
      -(mT beta0 p4Q2PZ37ADC_fixedCoupling_pos.le))

local instance p4Q2PZ37AKT_probability : IsProbabilityMeasure muT := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- Bound the exact original plaquette count through H=16.
This is NOT a rescaled or synthetic lattice count. -/
theorem p4Q2PZ37AKT_originalPlaquetteCount_le_sixteen
    (hH : H ≤ 16) : pT ≤ 117912 := by
  have hHR : (H : ℝ) ≤ 16 := by exact_mod_cast hH
  have hCube : ((H : ℝ) + 1) ^ 3 ≤ (17 : ℝ) ^ 3 :=
    pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (H : ℝ) + 1)
      (by linarith only [hHR]) 3
  rw [p4Q2PZ37AIB_plaquetteCount_exact]
  norm_num at hCube ⊢
  nlinarith only [hCube]

/-- A fully rational certificate for AKS's *sharper* genuine SU(2)
Haar-character quarter-Gaussian partition test through H=16. -/
theorem p4Q2PZ37AKT_originalFixedCoupling_quarterBudget_le_logFour
    (hH : H ≤ 16) :
    beta0 ^ 2 * pT / 4 ≤ Real.log 4 := by
  have hb0 : 0 ≤ beta0 := p4Q2PZ37ADC_fixedCoupling_pos.le
  have hb : beta0 ≤ (1 / 156 : ℝ) :=
    p4Q2PZ37AKO_originalFixedCoupling_le_oneOver156
  have hp : pT ≤ (117912 : ℝ) :=
    p4Q2PZ37AKT_originalPlaquetteCount_le_sixteen H hH
  have hbSq := pow_le_pow_left₀ hb0 hb 2
  have hMul1 := mul_le_mul_of_nonneg_right hbSq (p4Q2PZ37AHN_count_pos H).le
  have hMul2 := mul_le_mul_of_nonneg_left hp (sq_nonneg (1 / 156 : ℝ))
  have hSmall : beta0 ^ 2 * pT / 4 ≤ (11 / 8 : ℝ) := by
    nlinarith only [hMul1, hMul2]
  exact hSmall.trans p4Q2PZ37AKO_elevenEighths_le_log_four

/-- The genuine original negative-set Haar mass is bounded by one
and AKS's original SU(2) partition estimate proves AKQ's ACTUAL
partition-Haar no-go criterion, for every H<=16. -/
theorem p4Q2PZ37AKT_originalFixedCoupling_partitionHaarMass_of_le_sixteen
    (hH : H ≤ 16) :
    Measure.real muT ET * ZT beta0 ≤
      4 * Real.exp (-(beta0 * pT)) := by
  have hOne : beta0 ≤ (1 : ℝ) := by
    have h := p4Q2PZ37AKO_originalFixedCoupling_le_oneOver156
    linarith only [h]
  have hQuarter : beta0 ^ 2 * pT / 4 ≤ Real.log 4 :=
    p4Q2PZ37AKT_originalFixedCoupling_quarterBudget_le_logFour H hH
  have hExpFour : Real.exp (beta0 ^ 2 * pT / 4) ≤ 4 := by
    calc
      _ ≤ Real.exp (Real.log 4) := Real.exp_le_exp.mpr hQuarter
      _ = 4 := Real.exp_log (by norm_num)
  have hZ :
      ZT beta0 ≤ Real.exp (-(beta0 * pT)) *
        Real.exp (beta0 ^ 2 * pT / 4) := by
    calc
      _ ≤ Real.exp (pT * (-beta0 + beta0 ^ 2 / 4)) :=
        p4Q2PZ37AKS_originalCrossingPartition_le_quarterGaussian H
          beta0 p4Q2PZ37ADC_fixedCoupling_pos.le hOne
      _ = Real.exp (-(beta0 * pT)) * Real.exp (beta0 ^ 2 * pT / 4) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hr : Measure.real muT ET ≤ (1 : ℝ) := measureReal_le_one
  have hZpos : 0 ≤ ZT beta0 :=
    (p4Q2PZ37AIF_originalCrossingPartition_pos H beta0).le
  calc
    Measure.real muT ET * ZT beta0 ≤ 1 * ZT beta0 :=
      mul_le_mul_of_nonneg_right hr hZpos
    _ = ZT beta0 := one_mul _
    _ ≤ Real.exp (-(beta0 * pT)) * Real.exp (beta0 ^ 2 * pT / 4) := hZ
    _ ≤ Real.exp (-(beta0 * pT)) * 4 :=
      mul_le_mul_of_nonneg_left hExpFour (Real.exp_pos _).le
    _ = 4 * Real.exp (-(beta0 * pT)) := by ring

/-- No strict ORIGINAL AJA finite-power witness exists at fixed beta0
for any genuine original finite volume H<=16; the result does not
use measured negative Haar masses or change the strict original budget. -/
theorem p4Q2PZ37AKT_originalFixedCoupling_le_sixteen_no_AJA_power_witness
    (hH : H ≤ 16) :
    ¬ ∃ n : ℕ,
      ‖((ST beta0 p4Q2PZ37ADC_fixedCoupling_pos.le) ^ n) fT‖ ^ 2 <
        (mT beta0 p4Q2PZ37ADC_fixedCoupling_pos.le) ^ 2 *
          Measure.real muT ET := by
  exact p4Q2PZ37AKQ_original_no_AJA_witness_of_partitionHaarMass
    H beta0 p4Q2PZ37ADC_fixedCoupling_pos
    (p4Q2PZ37AKT_originalFixedCoupling_partitionHaarMass_of_le_sixteen H hH)

/-- In particular, the unchanged original physical H=16 slab
admits no original AJA strict finite-power witness at beta0. -/
theorem p4Q2PZ37AKT_originalH16_no_AJA_power_witness :
    ¬ ∃ n : ℕ,
      ‖((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          16 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le) ^ n)
        (p4Q2PZ37ZW_originalCenteredPhysicalDirection 16)‖ ^ 2 <
      (p4Q2PZ37AIW_originalNormalizedNegativeMargin 16 beta0
        p4Q2PZ37ADC_fixedCoupling_pos.le) ^ 2 *
        Measure.real (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure 16 2)
          {A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration 16 2 |
            p4Q2PZ37AIW_originalNormalizedSourceTransfer 16 beta0
              p4Q2PZ37ADC_fixedCoupling_pos.le A <
              -(p4Q2PZ37AIW_originalNormalizedNegativeMargin 16 beta0
                p4Q2PZ37ADC_fixedCoupling_pos.le)} := by
  exact p4Q2PZ37AKT_originalFixedCoupling_le_sixteen_no_AJA_power_witness
    16 (by omega)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKT_originalPlaquetteCount_le_sixteen
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKT_originalFixedCoupling_quarterBudget_le_logFour
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKT_originalFixedCoupling_partitionHaarMass_of_le_sixteen
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKT_originalFixedCoupling_le_sixteen_no_AJA_power_witness
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKT_originalH16_no_AJA_power_witness
