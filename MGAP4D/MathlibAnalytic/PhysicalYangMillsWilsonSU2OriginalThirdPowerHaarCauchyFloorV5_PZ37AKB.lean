import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalSecondPowerHaarCauchyFloorV5_PZ37AKA
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AKB — original Wilson third-power Haar-Cauchy floor

AKA certified the actual second-power floor B²/V ≤ ‖S² f₀‖².
For symmetric S, Cauchy--Schwarz also gives
  (‖S² x‖²)² ≤ ‖S x‖² * ‖S³ x‖².
Combining this with (‖S x‖²)² ≤ ‖x‖² * ‖S² x‖² yields
  (‖S x‖²)³ ≤ (‖x‖²)² * ‖S³ x‖².
The true Haar certificate B>0, B≤‖S f₀‖² and V=‖f₀‖²>0
then gives 0 < B³/V² ≤ ‖S³ f₀‖² and B³/V² < B.

This is a true finite-H n=3 lower bound, not a strict AJA witness,
uniform-volume result, top rank-one theorem, or continuum mass gap.
Original Wilson/Haar/ZW/AJA definitions, hypotheses, and pins are unchanged.
-/

namespace MGAP4D.MathlibAnalytic
open MeasureTheory
open scoped InnerProductSpace Topology Classical ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Shift genuine symmetric operator Cauchy--Schwarz to powers 1,2,3. -/
theorem realHilbert_symmetric_shiftedSecondPower_normSq_Cauchy_akb
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : E →L[ℝ] E)
    (hSymm : (S : E →ₗ[ℝ] E).IsSymmetric) (x : E) :
    (‖(S ^ 2) x‖ ^ 2) ^ 2 ≤ ‖S x‖ ^ 2 * ‖(S ^ 3) x‖ ^ 2 := by
  have hTwo : (S ^ 2) x = S (S x) := by
    rw [pow_two]
    rfl
  have hThree : (S ^ 3) x = (S ^ 2) (S x) := by
    change (S ^ (2 + 1)) x = (S ^ 2) (S x)
    rw [pow_succ]
    rfl
  have hCS :=
    realHilbert_symmetric_secondPower_normSq_Cauchy_aka S hSymm (S x)
  calc
    (‖(S ^ 2) x‖ ^ 2) ^ 2 = (‖S (S x)‖ ^ 2) ^ 2 := by rw [hTwo]
    _ ≤ ‖S x‖ ^ 2 * ‖(S ^ 2) (S x)‖ ^ 2 := hCS
    _ = ‖S x‖ ^ 2 * ‖(S ^ 3) x‖ ^ 2 := by rw [hThree]

/-- Third-power log-convex bound; the cancellation uses a strictly
positive first-step energy, later supplied by the original Haar certificate. -/
theorem realHilbert_symmetric_thirdPower_normSq_Cauchy_akb
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : E →L[ℝ] E)
    (hSymm : (S : E →ₗ[ℝ] E).IsSymmetric)
    (x : E) (hFirst : 0 < ‖S x‖ ^ 2) :
    (‖S x‖ ^ 2) ^ 3 ≤ (‖x‖ ^ 2) ^ 2 * ‖(S ^ 3) x‖ ^ 2 := by
  let a0 : ℝ := ‖x‖ ^ 2
  let a1 : ℝ := ‖S x‖ ^ 2
  let a2 : ℝ := ‖(S ^ 2) x‖ ^ 2
  let a3 : ℝ := ‖(S ^ 3) x‖ ^ 2
  have hFirstPos : 0 < a1 := hFirst
  have hStep0 : a1 ^ 2 ≤ a0 * a2 :=
    realHilbert_symmetric_secondPower_normSq_Cauchy_aka S hSymm x
  have hStep1 : a2 ^ 2 ≤ a1 * a3 :=
    realHilbert_symmetric_shiftedSecondPower_normSq_Cauchy_akb S hSymm x
  have hBoth : 0 ≤ a0 * a2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hStep0Sq : (a1 ^ 2) ^ 2 ≤ (a0 * a2) ^ 2 :=
    (sq_le_sq₀ (sq_nonneg _) hBoth).2 hStep0
  have hStep1Mul : a0 ^ 2 * a2 ^ 2 ≤ a0 ^ 2 * (a1 * a3) :=
    mul_le_mul_of_nonneg_left hStep1 (sq_nonneg _)
  have hFour : a1 ^ 4 ≤ a0 ^ 2 * (a1 * a3) := by
    calc
      a1 ^ 4 = (a1 ^ 2) ^ 2 := by ring
      _ ≤ (a0 * a2) ^ 2 := hStep0Sq
      _ = a0 ^ 2 * a2 ^ 2 := by ring
      _ ≤ a0 ^ 2 * (a1 * a3) := hStep1Mul
  have hCancel : a1 * (a1 ^ 3) ≤ a1 * (a0 ^ 2 * a3) := by
    calc
      a1 * (a1 ^ 3) = a1 ^ 4 := by ring
      _ ≤ a0 ^ 2 * (a1 * a3) := hFour
      _ = a1 * (a0 ^ 2 * a3) := by ring
  exact (mul_le_mul_iff_of_pos_left hFirstPos).mp hCancel

/-- Transfer a genuine positive one-step Haar budget to the third power. -/
theorem realHilbert_oneStep_margin_thirdPower_Cauchy_akb
    (B a V w : ℝ) (hB : 0 ≤ B) (hBA : B ≤ a)
    (hThird : a ^ 3 ≤ V ^ 2 * w) :
    B ^ 3 ≤ V ^ 2 * w := by
  exact (pow_le_pow_left₀ hB hBA 3).trans hThird

local notation "GA" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AKB_group : IsTopologicalGroup GA :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AKB_compact : CompactSpace GA :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AKB_secondCountable : SecondCountableTopology GA :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AKB_measurable : MeasurableSpace GA :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AKB_borel : BorelSpace GA :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AKB_linkFintype (K : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink K) :=
  Fintype.ofFinite _

namespace GroundStatePosteriorJoint
variable (H : ℕ)

local notation "PhysB" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "CfgB" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muB" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "fB" =>
  p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "SB" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator H 2 (by norm_num)
local notation "VB" =>
  p4Q2PZ37AHN_originalSource_HaarSecondMoment H
local notation "uB" =>
  p4Q2PZ37AIW_originalNormalizedSourceTransfer H
local notation "mB" =>
  p4Q2PZ37AIW_originalNormalizedNegativeMargin H

local instance p4Q2PZ37AKB_physicalComplete (K : ℕ) :
    CompleteSpace
      (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule K 2) :=
  (periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule_isClosed
    K 2).completeSpace_coe

/-- Actual original third-power floor: B³ ≤ V² * ‖S³ f₀‖². -/
theorem p4Q2PZ37AKB_originalThirdPower_cube_le_varianceSq_mul_energy
    (beta : ℝ) (hbeta : 0 < beta) :
    ((mB beta hbeta.le) ^ 2 *
      Measure.real muB
        {U : CfgB | uB beta hbeta.le U < -(mB beta hbeta.le)}) ^ 3 ≤
      VB ^ 2 * ‖((SB beta hbeta.le) ^ 3) fB‖ ^ 2 := by
  let S : PhysB →L[ℝ] PhysB := SB beta hbeta.le
  let B : ℝ :=
    (mB beta hbeta.le) ^ 2 *
      Measure.real muB
        {U : CfgB | uB beta hbeta.le U < -(mB beta hbeta.le)}
  have hSymm : (S : PhysB →ₗ[ℝ] PhysB).IsSymmetric :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
      H 2 (by norm_num) beta hbeta.le
  have hBA : B ≤ ‖S fB‖ ^ 2 :=
    p4Q2PZ37AJA_originalNormalizedPhysicalSource_norm_sq_ge_margin_measure
      H beta hbeta
  have hBpos : 0 < B :=
    p4Q2PZ37AJA_originalQuantitativeHaarL2_certificate_pos H beta hbeta
  have hFirst : 0 < ‖S fB‖ ^ 2 := hBpos.trans_le hBA
  have hThird :=
    realHilbert_symmetric_thirdPower_normSq_Cauchy_akb S hSymm fB hFirst
  have hVariance : ‖fB‖ ^ 2 = VB :=
    p4Q2PZ37AJR_originalSource_norm_sq_eq_HaarVariance H
  have hThird' :
      (‖S fB‖ ^ 2) ^ 3 ≤ VB ^ 2 * ‖(S ^ 3) fB‖ ^ 2 := by
    calc
      (‖S fB‖ ^ 2) ^ 3 ≤ (‖fB‖ ^ 2) ^ 2 * ‖(S ^ 3) fB‖ ^ 2 := hThird
      _ = VB ^ 2 * ‖(S ^ 3) fB‖ ^ 2 := by rw [hVariance]
  exact realHilbert_oneStep_margin_thirdPower_Cauchy_akb
    B (‖S fB‖ ^ 2) VB (‖(S ^ 3) fB‖ ^ 2)
    hBpos.le hBA hThird'

/-- Unconditional finite-H original n=3 energy lower bound B³/V². -/
theorem p4Q2PZ37AKB_originalThirdPower_energy_ge_cube_div_varianceSq
    (beta : ℝ) (hbeta : 0 < beta) :
    (((mB beta hbeta.le) ^ 2 *
      Measure.real muB
        {U : CfgB | uB beta hbeta.le U < -(mB beta hbeta.le)}) ^ 3) /
      (VB ^ 2) ≤
    ‖((SB beta hbeta.le) ^ 3) fB‖ ^ 2 := by
  have hV : 0 < VB :=
    (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  have hFloor :=
    p4Q2PZ37AKB_originalThirdPower_cube_le_varianceSq_mul_energy H beta hbeta
  apply (div_le_iff₀ (pow_pos hV 2)).2
  nlinarith only [hFloor]

/-- The true original third Wilson power does not vanish. -/
theorem p4Q2PZ37AKB_originalThirdPower_energy_pos
    (beta : ℝ) (hbeta : 0 < beta) :
    0 < ‖((SB beta hbeta.le) ^ 3) fB‖ ^ 2 := by
  have hV : 0 < VB :=
    (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  have hB :
      0 < (mB beta hbeta.le) ^ 2 *
        Measure.real muB
          {U : CfgB | uB beta hbeta.le U < -(mB beta hbeta.le)} :=
    p4Q2PZ37AJA_originalQuantitativeHaarL2_certificate_pos H beta hbeta
  have hFloor :=
    p4Q2PZ37AKB_originalThirdPower_energy_ge_cube_div_varianceSq H beta hbeta
  have hPos :
      0 <
      (((mB beta hbeta.le) ^ 2 *
        Measure.real muB
          {U : CfgB | uB beta hbeta.le U < -(mB beta hbeta.le)}) ^ 3) /
        (VB ^ 2) :=
    div_pos (pow_pos hB 3) (pow_pos hV 2)
  exact hPos.trans_le hFloor

/-- The new lower floor stays BELOW the AJA certificate, not a witness. -/
theorem p4Q2PZ37AKB_originalAJA_cube_div_varianceSq_lt_AJA
    (beta : ℝ) (hbeta : 0 < beta) :
    (((mB beta hbeta.le) ^ 2 *
      Measure.real muB
        {U : CfgB | uB beta hbeta.le U < -(mB beta hbeta.le)}) ^ 3) /
      (VB ^ 2) <
    (mB beta hbeta.le) ^ 2 *
      Measure.real muB
        {U : CfgB | uB beta hbeta.le U < -(mB beta hbeta.le)} := by
  let B : ℝ :=
    (mB beta hbeta.le) ^ 2 *
      Measure.real muB
        {U : CfgB | uB beta hbeta.le U < -(mB beta hbeta.le)}
  have hB : 0 < B :=
    p4Q2PZ37AJA_originalQuantitativeHaarL2_certificate_pos H beta hbeta
  have hV : 0 < VB :=
    (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  have hCap : B ≤ VB / 16 :=
    p4Q2PZ37AJX_originalAJA_certificate_le_sixteenth_variance
      H beta hbeta
  have hLess : B < VB := by linarith only [hCap, hV]
  have hDiff : 0 < (VB - B) * (VB + B) :=
    mul_pos (sub_pos.mpr hLess) (add_pos hV hB)
  have hSq : B ^ 2 < VB ^ 2 := by nlinarith only [hDiff]
  have hCube : B ^ 3 < B * VB ^ 2 := by
    calc
      B ^ 3 = B * B ^ 2 := by ring
      _ < B * VB ^ 2 := mul_lt_mul_of_pos_left hSq hB
  apply (div_lt_iff₀ (pow_pos hV 2)).2
  nlinarith only [hCube]

/-- Exact interval conditional on a separately supplied strict n=3 witness. -/
theorem p4Q2PZ37AKB_originalThirdPower_AJA_witness_interval
    (beta : ℝ) (hbeta : 0 < beta)
    (hPower :
      ‖((SB beta hbeta.le) ^ 3) fB‖ ^ 2 <
      (mB beta hbeta.le) ^ 2 *
        Measure.real muB
          {U : CfgB | uB beta hbeta.le U < -(mB beta hbeta.le)}) :
    (((mB beta hbeta.le) ^ 2 *
      Measure.real muB
        {U : CfgB | uB beta hbeta.le U < -(mB beta hbeta.le)}) ^ 3) /
      (VB ^ 2) ≤
      ‖((SB beta hbeta.le) ^ 3) fB‖ ^ 2 ∧
    ‖((SB beta hbeta.le) ^ 3) fB‖ ^ 2 <
      (mB beta hbeta.le) ^ 2 *
        Measure.real muB
          {U : CfgB | uB beta hbeta.le U < -(mB beta hbeta.le)} :=
  ⟨p4Q2PZ37AKB_originalThirdPower_energy_ge_cube_div_varianceSq
      H beta hbeta, hPower⟩

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

/-! Eight distinct kernel axiom audits for eight new theorems. -/
#print axioms MGAP4D.MathlibAnalytic.realHilbert_symmetric_shiftedSecondPower_normSq_Cauchy_akb
#print axioms MGAP4D.MathlibAnalytic.realHilbert_symmetric_thirdPower_normSq_Cauchy_akb
#print axioms MGAP4D.MathlibAnalytic.realHilbert_oneStep_margin_thirdPower_Cauchy_akb
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKB_originalThirdPower_cube_le_varianceSq_mul_energy
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKB_originalThirdPower_energy_ge_cube_div_varianceSq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKB_originalThirdPower_energy_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKB_originalAJA_cube_div_varianceSq_lt_AJA
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKB_originalThirdPower_AJA_witness_interval
