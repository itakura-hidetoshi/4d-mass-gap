import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalH21SmallCouplingThirdTaylorAJANoGoV5_PZ37AKW
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AKX — original H22 genuine Haar-mass threshold and AJA/top obstruction

The mechanically certified AKW original crossing partition bound is
  Z_H(beta0) <= exp(-beta0*p_H)*exp((44/351)*beta0²*p_H)
at exactly the original beta0=log(3/2)/64, with the actual SU(2) Haar
one-link character and original crossing product (NOT a Gaussian model).

At H22, the exact original plaquette count p_22=292008 and genuine
negative-region Haar mass r_22 give the explicit **conditional**
physical threshold
  r_22 <= 4 * exp(-(44/351)*beta0²*292008).
The original AKQ/AJA finite-power strict witness is then excluded,
and the true AKU full-top comparison B_22 <= ||Q f0_22||² holds.

No numerical r_22 upper bound is proved or assumed unconditionally.
The contrapositive states any genuine H22 AJA strict witness would
require r_22 to exceed the exact threshold. The strict top-Haar
residual sign/equality, H-uniform GL coercivity, Hamiltonian spectral
gap, and continuum four-dimensional Yang--Mills mass gap remain OPEN.
No original definitions, source, Haar, margin, budget, top, mathlib
pins, existing theorem statements or workflow are changed.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace Topology Classical ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4900000
set_option synthInstance.maxHeartbeats 1050000

local notation "GX" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AKX_group : IsTopologicalGroup GX :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AKX_compact : CompactSpace GX :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AKX_countable : SecondCountableTopology GX :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AKX_measurable : MeasurableSpace GX :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AKX_borel : BorelSpace GX :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AKX_links (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "CfgX" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muX" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "pX" => p4Q2PZ37AFZ_plaquetteCount H
local notation "ZX" => p4Q2PZ37AIF_originalCrossingPartition H
local notation "fX" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "SX" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
    H 2 (by norm_num)
local notation "uX" => p4Q2PZ37AIW_originalNormalizedSourceTransfer H
local notation "mX" => p4Q2PZ37AIW_originalNormalizedNegativeMargin H
local notation "beta0" => p4Q2PZ37ADC_fixedCoupling
local notation "EX" =>
  (fun A : CfgX =>
    uX beta0 p4Q2PZ37ADC_fixedCoupling_pos.le A <
      -(mX beta0 p4Q2PZ37ADC_fixedCoupling_pos.le))

local instance p4Q2PZ37AKX_probability : IsProbabilityMeasure muX := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- AKW's original genuine small-beta partition bound retains the
actual Haar-negative mass, rather than replacing it by one. -/
theorem p4Q2PZ37AKX_originalFixedCoupling_partitionHaarMass_of_sharpThreshold
    (hMass :
      Measure.real muX EX *
        Real.exp (44 * beta0 ^ 2 * pX / 351) ≤ 4) :
    Measure.real muX EX * ZX beta0 ≤
      4 * Real.exp (-(beta0 * pX)) := by
  have hOne : beta0 ≤ (1 / 156 : ℝ) :=
    p4Q2PZ37AKO_originalFixedCoupling_le_oneOver156
  have hZ :
      ZX beta0 ≤ Real.exp (-(beta0 * pX)) *
        Real.exp (44 * beta0 ^ 2 * pX / 351) := by
    calc
      _ ≤ Real.exp (pX * (-beta0 + 44 * beta0 ^ 2 / 351)) :=
        p4Q2PZ37AKW_originalCrossingPartition_le_fortyFourThreeFiftyOneGaussian H
          beta0 p4Q2PZ37ADC_fixedCoupling_pos.le hOne
      _ = Real.exp (-(beta0 * pX)) *
          Real.exp (44 * beta0 ^ 2 * pX / 351) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hr : 0 ≤ Measure.real muX EX := ENNReal.toReal_nonneg
  calc
    _ ≤ Measure.real muX EX *
        (Real.exp (-(beta0 * pX)) * Real.exp (44 * beta0 ^ 2 * pX / 351)) :=
      mul_le_mul_of_nonneg_left hZ hr
    _ = Real.exp (-(beta0 * pX)) *
        (Measure.real muX EX * Real.exp (44 * beta0 ^ 2 * pX / 351)) := by ring
    _ ≤ Real.exp (-(beta0 * pX)) * 4 :=
      mul_le_mul_of_nonneg_left hMass (Real.exp_pos _).le
    _ = 4 * Real.exp (-(beta0 * pX)) := by ring

/-- The genuine original AJA strict finite-power witness cannot exist
under the indicated actual Haar-mass bound. -/
theorem p4Q2PZ37AKX_originalFixedCoupling_no_AJA_of_sharpThreshold
    (hMass :
      Measure.real muX EX *
        Real.exp (44 * beta0 ^ 2 * pX / 351) ≤ 4) :
    ¬ ∃ n : ℕ,
      ‖((SX beta0 p4Q2PZ37ADC_fixedCoupling_pos.le) ^ n) fX‖ ^ 2 <
        (mX beta0 p4Q2PZ37ADC_fixedCoupling_pos.le) ^ 2 *
          Measure.real muX EX := by
  exact p4Q2PZ37AKQ_original_no_AJA_witness_of_partitionHaarMass
    H beta0 p4Q2PZ37ADC_fixedCoupling_pos
    (p4Q2PZ37AKX_originalFixedCoupling_partitionHaarMass_of_sharpThreshold H hMass)

/-- The ACTUAL original Haar budget is below its genuine full-top
projection energy under the same sharp mass-sensitive test. -/
theorem p4Q2PZ37AKX_originalFixedCoupling_budget_le_top_of_sharpThreshold
    (hMass :
      Measure.real muX EX *
        Real.exp (44 * beta0 ^ 2 * pX / 351) ≤ 4) :
    (mX beta0 p4Q2PZ37ADC_fixedCoupling_pos.le) ^ 2 *
      Measure.real muX EX ≤
      ‖p4Q2PZ37AJD_originalSourceTopComponent H beta0
        p4Q2PZ37ADC_fixedCoupling_pos‖ ^ 2 := by
  exact p4Q2PZ37AKU_originalBudget_le_fullTop_of_partitionHaarMass
    H beta0 p4Q2PZ37ADC_fixedCoupling_pos
    (p4Q2PZ37AKX_originalFixedCoupling_partitionHaarMass_of_sharpThreshold H hMass)

/-- Consequently, the unchanged original Haar-minus-top residual
is nonpositive, not necessarily strictly negative. -/
theorem p4Q2PZ37AKX_originalFixedCoupling_delta_nonpos_of_sharpThreshold
    (hMass :
      Measure.real muX EX *
        Real.exp (44 * beta0 ^ 2 * pX / 351) ≤ 4) :
    (mX beta0 p4Q2PZ37ADC_fixedCoupling_pos.le) ^ 2 *
      Measure.real muX EX -
      ‖p4Q2PZ37AJD_originalSourceTopComponent H beta0
        p4Q2PZ37ADC_fixedCoupling_pos‖ ^ 2 ≤ 0 := by
  exact sub_nonpos.mpr
    (p4Q2PZ37AKX_originalFixedCoupling_budget_le_top_of_sharpThreshold H hMass)

/-- Exact original plaquette count at H=22. -/
theorem p4Q2PZ37AKX_originalH22_plaquetteCount_exact :
    (p4Q2PZ37AFZ_plaquetteCount 22 : ℝ) = 292008 := by
  rw [p4Q2PZ37AIB_plaquetteCount_exact]
  norm_num

local notation "Cfg22" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration 22 2
local notation "mu22" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure 22 2
local notation "u22" =>
  p4Q2PZ37AIW_originalNormalizedSourceTransfer 22 beta0
    p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "m22" =>
  p4Q2PZ37AIW_originalNormalizedNegativeMargin 22 beta0
    p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "E22" => (fun A : Cfg22 => u22 A < -(m22))
local notation "r22" => Measure.real mu22 E22
local notation "q22" => 44 * beta0 ^ 2 * (292008 : ℝ) / 351

/-- The H22 numerical threshold is an exact inequality on the
genuine (still unknown) original Haar-negative-region mass. -/
theorem p4Q2PZ37AKX_originalH22_sharpThreshold_to_massFactor
    (hMass : r22 ≤ 4 * Real.exp (-q22)) :
    r22 * Real.exp (44 * beta0 ^ 2 *
      p4Q2PZ37AFZ_plaquetteCount 22 / 351) ≤ 4 := by
  rw [p4Q2PZ37AKX_originalH22_plaquetteCount_exact]
  have hMult := mul_le_mul_of_nonneg_right hMass (Real.exp_pos q22).le
  have hInv : Real.exp (-q22) * Real.exp q22 = 1 := by
    rw [← Real.exp_add]
    simp
  have hRight : (4 * Real.exp (-q22)) * Real.exp q22 = 4 := by
    calc
      _ = 4 * (Real.exp (-q22) * Real.exp q22) := by ring
      _ = 4 := by rw [hInv]; ring
  exact hMult.trans_eq hRight

/-- Conditional H22 no-witness: the input is a true Haar-mass upper
bound, NOT an inferred numerical certificate. -/
theorem p4Q2PZ37AKX_originalH22_no_AJA_of_genuineHaarMass
    (hMass : r22 ≤ 4 * Real.exp (-q22)) :
    ¬ ∃ n : ℕ,
      ‖((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          22 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le) ^ n)
        (p4Q2PZ37ZW_originalCenteredPhysicalDirection 22)‖ ^ 2 <
        (m22) ^ 2 * r22 := by
  exact p4Q2PZ37AKX_originalFixedCoupling_no_AJA_of_sharpThreshold 22
    (p4Q2PZ37AKX_originalH22_sharpThreshold_to_massFactor hMass)

/-- Conditional H22 actual original budget/top comparison. -/
theorem p4Q2PZ37AKX_originalH22_budget_le_top_of_genuineHaarMass
    (hMass : r22 ≤ 4 * Real.exp (-q22)) :
    (m22) ^ 2 * r22 ≤
      ‖p4Q2PZ37AJD_originalSourceTopComponent 22 beta0
        p4Q2PZ37ADC_fixedCoupling_pos‖ ^ 2 := by
  exact p4Q2PZ37AKX_originalFixedCoupling_budget_le_top_of_sharpThreshold 22
    (p4Q2PZ37AKX_originalH22_sharpThreshold_to_massFactor hMass)

/-- Conditional H22 original Haar-minus-top residual <=0. -/
theorem p4Q2PZ37AKX_originalH22_delta_nonpos_of_genuineHaarMass
    (hMass : r22 ≤ 4 * Real.exp (-q22)) :
    (m22) ^ 2 * r22 -
      ‖p4Q2PZ37AJD_originalSourceTopComponent 22 beta0
        p4Q2PZ37ADC_fixedCoupling_pos‖ ^ 2 ≤ 0 := by
  exact sub_nonpos.mpr
    (p4Q2PZ37AKX_originalH22_budget_le_top_of_genuineHaarMass hMass)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKX_originalFixedCoupling_partitionHaarMass_of_sharpThreshold
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKX_originalFixedCoupling_no_AJA_of_sharpThreshold
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKX_originalFixedCoupling_budget_le_top_of_sharpThreshold
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKX_originalFixedCoupling_delta_nonpos_of_sharpThreshold
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKX_originalH22_plaquetteCount_exact
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKX_originalH22_sharpThreshold_to_massFactor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKX_originalH22_no_AJA_of_genuineHaarMass
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKX_originalH22_budget_le_top_of_genuineHaarMass
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKX_originalH22_delta_nonpos_of_genuineHaarMass
