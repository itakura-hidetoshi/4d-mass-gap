import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalSmallCouplingAJAWitnessNoGoV5_PZ37AKG
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalCauchyCubicSmallCouplingV5_PZ37AIM
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AKH — original AJA no-witness band strictly outside AIL

AKG certifies the original AJA witness obstruction only on 0 < beta <= tau_H.
AIM already supplies a stronger actual-model raw transfer estimate on
0 < beta <= theta_H, where the UNCHANGED original definitions satisfy
  tau_H < theta_H = (1/384)^n_H / (16*p_H+1) < beta0.
Here we connect that distinct certified raw estimate to the true fixed-top
overlap and the ORIGINAL normalized AJA budget. Thus the nonempty NEW band
  tau_H < beta <= theta_H
has no strict original AJA power witness. No conclusion is transported to
beta > theta_H, in particular not to the old fixed beta0.

First isolate the actual-model bridge: any certified uniform nonpositive
raw-source bound P f0 <= -a, with a>=0, implies <f0,psi> <= -a for the
EXISTING nonnegative unit top vector psi. It implies ||S^n f0||^2 >= a^2
for all n. The bridge is conditional; the AIM application discharges its
premise using the genuine raw Wilson integral and its Haar-a.e. bridge.

Neither source, operator, Haar measure, normalization, AJA margin nor either
old cutoff is redefined. No top-rank-one or mass-gap assumption is used.
This leaf extends the certified domain, not an existing theorem's hypotheses.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped InnerProductSpace Topology Classical ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "GH" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AKH_group : IsTopologicalGroup GH :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AKH_compact : CompactSpace GH :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AKH_countable : SecondCountableTopology GH :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AKH_measurable : MeasurableSpace GH :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AKH_borel : BorelSpace GH :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AKH_links (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "CfgH" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "PhysH" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "fH" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "VH" => p4Q2PZ37AHN_originalSource_HaarSecondMoment H
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "PH" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator H 2 (by norm_num)
local notation "SH" => periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator H 2 (by norm_num)
local notation "psiH" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector H 2 (by norm_num)
local notation "tauH" => p4Q2PZ37AIL_elementarySmallCoupling H
local notation "thetaH" => p4Q2PZ37AIM_elementaryCubicSmallCoupling H
local notation "uH" => p4Q2PZ37AIW_originalNormalizedSourceTransfer H
local notation "mH" => p4Q2PZ37AIW_originalNormalizedNegativeMargin H

local instance p4Q2PZ37AKH_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- Conditional bridge on the actual Wilson model. Its raw floor premise
is explicit and is discharged by AIM in the interval theorem below. -/
theorem p4Q2PZ37AKH_originalSource_top_overlap_of_rawFloor
    (beta : ℝ) (hbeta : 0 < beta) (a : ℝ) (ha : 0 ≤ a)
    (hFloor : ∀ A : CfgH,
      decomposableOneSliceTransferIntegral H 2 beta fH A ≤ -a) :
    inner ℝ fH (psiH beta hbeta.le) ≤ -a := by
  let P : PhysH →L[ℝ] PhysH := PH beta hbeta.le
  let psi : PhysH := psiH beta hbeta.le
  let g : Lp ℝ 2 muH := psi
  let I : ℝ := ∫ A : CfgH, g A ∂muH
  have hNorm : 0 < ‖P‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 (by norm_num) beta hbeta.le
  have hRaw : ∀ᵐ A ∂muH, ((P fH : PhysH) : Lp ℝ 2 muH) A ≤ -a := by
    filter_upwards [p4Q2PZ37AIW_originalPhysicalTransfer_coeFn H beta hbeta.le fH]
      with A hA
    change ((P fH : PhysH) : Lp ℝ 2 muH) A =
      decomposableOneSliceTransferIntegral H 2 beta fH A at hA
    rw [hA]
    exact hFloor A
  have hg : ∀ᵐ A ∂muH, 0 ≤ g A :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_ae_nonnegative
      H 2 (by norm_num) beta hbeta.le
  have hPair : inner ℝ (P fH) psi ≤ -a * I :=
    realL2_inner_le_neg_floor_mul_mass_akg muH (P fH : Lp ℝ 2 muH) g a hRaw hg
  have hSymm : (P : PhysH →ₗ[ℝ] PhysH).IsSymmetric :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_isSymmetric
      H 2 (by norm_num) beta hbeta.le
  have hEigen : P psi = ‖P‖ • psi :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_eigen
      H 2 (by norm_num) beta hbeta.le
  have hEq : inner ℝ (P fH) psi = ‖P‖ * inner ℝ fH psi := by
    calc
      inner ℝ (P fH) psi = inner ℝ fH (P psi) := hSymm fH psi
      _ = ‖P‖ * inner ℝ fH psi := by
        rw [hEigen]
        exact real_inner_smul_right (fH : PhysH) psi ‖P‖
  have hMass : ‖P‖ ≤ I :=
    p4Q2PZ37AKG_originalNonnegativeTop_mass_ge_norm H beta hbeta.le
  have hBound : ‖P‖ * inner ℝ fH psi ≤ ‖P‖ * (-a) := by
    calc
      ‖P‖ * inner ℝ fH psi = inner ℝ (P fH) psi := hEq.symm
      _ ≤ -a * I := hPair
      _ ≤ -a * ‖P‖ := mul_le_mul_of_nonpos_left hMass (neg_nonpos.mpr ha)
      _ = ‖P‖ * (-a) := mul_comm _ _
  change inner ℝ fH psi ≤ -a
  by_contra hNot
  have hGt : -a < inner ℝ fH psi := lt_of_not_ge hNot
  exact (not_lt_of_ge hBound) (mul_lt_mul_of_pos_left hGt hNorm)

/-- The raw floor controls every genuine normalized power, without any
rank-one claim or identification of Haar centering with vacuum centering. -/
theorem p4Q2PZ37AKH_originalAllPowers_energy_ge_rawFloor_sq
    (beta : ℝ) (hbeta : 0 < beta) (a : ℝ) (ha : 0 ≤ a)
    (hFloor : ∀ A : CfgH,
      decomposableOneSliceTransferIntegral H 2 beta fH A ≤ -a) (n : ℕ) :
    a ^ 2 ≤ ‖((SH beta hbeta.le) ^ n) fH‖ ^ 2 := by
  let P : PhysH →L[ℝ] PhysH := PH beta hbeta.le
  let S : PhysH →L[ℝ] PhysH := SH beta hbeta.le
  let psi : PhysH := psiH beta hbeta.le
  have hUnit : ‖psi‖ = 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_norm
      H 2 (by norm_num) beta hbeta.le
  have hNorm : 0 < ‖P‖ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 (by norm_num) beta hbeta.le
  have hEigen : P psi = ‖P‖ • psi :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_eigen
      H 2 (by norm_num) beta hbeta.le
  have hFix : S psi = psi := by
    change ‖P‖⁻¹ • P psi = psi
    rw [hEigen, smul_smul, inv_mul_cancel₀ hNorm.ne', one_smul]
  have hSymm : (S : PhysH →ₗ[ℝ] PhysH).IsSymmetric :=
    periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator_isSymmetric
      H 2 (by norm_num) beta hbeta.le
  exact realHilbert_fixedUnit_power_normSq_ge_neg_overlap_akg S hSymm psi hUnit hFix
    fH a ha (p4Q2PZ37AKH_originalSource_top_overlap_of_rawFloor
      H beta hbeta a ha hFloor) n

/-- The unchanged normalized AJA budget on the larger AIM interval.
The set has genuine Haar mass one by AIM, not by an AIL extrapolation. -/
theorem p4Q2PZ37AKH_originalCubic_AJA_le_halfVariance_sq
    (beta : ℝ) (hbeta : 0 < beta) (hCubic : beta ≤ thetaH) :
    (mH beta hbeta.le) ^ 2 *
      Measure.real muH {A : CfgH | uH beta hbeta.le A < -(mH beta hbeta.le)} ≤
        (beta * VH / 2) ^ 2 := by
  have hMass :
      Measure.real muH {A : CfgH | uH beta hbeta.le A < -(mH beta hbeta.le)} = 1 := by
    rw [p4Q2PZ37AIW_originalNormalizedNegativeRegion_eq_original H beta hbeta.le]
    exact p4Q2PZ37AIM_originalFullNegativeRegion_realMeasure_one H beta hbeta hCubic
  have hp : 0 < pH := p4Q2PZ37AHN_count_pos H
  have hV : 0 < VH := (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  have hExp : Real.exp (-(beta * pH)) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (neg_nonpos.mpr (mul_nonneg hbeta.le hp.le))
  have hMargin := (p4Q2PZ37AIW_originalNormalizedNegativeMargin_bounds H beta hbeta.le).2
  have hScaled := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hExp hbeta.le) hV.le
  have hm : mH beta hbeta.le ≤ beta * VH / 2 := by
    linarith only [hMargin, hScaled]
  have hm0 : 0 ≤ mH beta hbeta.le :=
    (p4Q2PZ37AIW_originalNormalizedNegativeMargin_pos H beta hbeta).le
  rw [hMass, mul_one]
  exact pow_le_pow_left₀ hm0 hm 2

/-- Actual-model quantitative no-go beyond the former AIL endpoint.
Every premise of the conditional raw-floor bridge is discharged here. -/
theorem p4Q2PZ37AKH_originalCubicAllPowers_ge_nineQuarters_AJA
    (beta : ℝ) (hbeta : 0 < beta) (hCubic : beta ≤ thetaH) (n : ℕ) :
    (9 / 4 : ℝ) * ((mH beta hbeta.le) ^ 2 *
      Measure.real muH {A : CfgH | uH beta hbeta.le A < -(mH beta hbeta.le)}) ≤
        ‖((SH beta hbeta.le) ^ n) fH‖ ^ 2 := by
  have hV : 0 < VH := (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  have hPower := p4Q2PZ37AKH_originalAllPowers_energy_ge_rawFloor_sq H beta hbeta
    (3 * beta * VH / 4) (by positivity)
    (fun A => (p4Q2PZ37AIM_originalTransfer_lt_negThreeQuarterVariance
      H beta hbeta hCubic A).le) n
  have hBudget := p4Q2PZ37AKH_originalCubic_AJA_le_halfVariance_sq H beta hbeta hCubic
  nlinarith only [hPower, hBudget]

/-- No finite exponent works on the enlarged interval, including theta_H.
This uses the original positive AJA certificate and original source. -/
theorem p4Q2PZ37AKH_originalCubic_no_AJA_power_witness
    (beta : ℝ) (hbeta : 0 < beta) (hCubic : beta ≤ thetaH) :
    ¬ ∃ n : ℕ, ‖((SH beta hbeta.le) ^ n) fH‖ ^ 2 <
      (mH beta hbeta.le) ^ 2 *
        Measure.real muH {A : CfgH | uH beta hbeta.le A < -(mH beta hbeta.le)} := by
  rintro ⟨n, hWitness⟩
  have hPower := p4Q2PZ37AKH_originalCubicAllPowers_ge_nineQuarters_AJA
    H beta hbeta hCubic n
  have hPositive := p4Q2PZ37AJA_originalQuantitativeHaarL2_certificate_pos H beta hbeta
  linarith only [hPower, hPositive, hWitness]

/-- Necessary location of any genuine future witness. This is not a
sufficiency or an existence assertion above the cubic cutoff. -/
theorem p4Q2PZ37AKH_originalAJA_witness_requires_above_cubic
    (beta : ℝ) (hbeta : 0 < beta)
    (hWitness : ∃ n : ℕ, ‖((SH beta hbeta.le) ^ n) fH‖ ^ 2 <
      (mH beta hbeta.le) ^ 2 *
        Measure.real muH {A : CfgH | uH beta hbeta.le A < -(mH beta hbeta.le)}) :
    thetaH < beta := by
  by_contra hNot
  exact p4Q2PZ37AKH_originalCubic_no_AJA_power_witness H beta hbeta
    (le_of_not_gt hNot) hWitness

/-- Specified ORIGINAL coupling strictly outside AIL: theta_H itself.
Its separation from the fixed beta0 explicitly preserves the open domain. -/
theorem p4Q2PZ37AKH_originalOutsideAIL_endpoint_certificate :
    tauH < thetaH ∧ thetaH < p4Q2PZ37ADC_fixedCoupling ∧
      ¬ ∃ n : ℕ,
        ‖((SH thetaH (p4Q2PZ37AIM_elementaryCubicSmallCoupling_pos H).le) ^ n) fH‖ ^ 2 <
          (mH thetaH (p4Q2PZ37AIM_elementaryCubicSmallCoupling_pos H).le) ^ 2 *
            Measure.real muH {A : CfgH |
              uH thetaH (p4Q2PZ37AIM_elementaryCubicSmallCoupling_pos H).le A <
                -(mH thetaH (p4Q2PZ37AIM_elementaryCubicSmallCoupling_pos H).le)} := by
  refine ⟨p4Q2PZ37AIM_oldSmallCoupling_lt_cubic H,
    p4Q2PZ37AIM_elementaryCubicSmallCoupling_lt_fixedCoupling H, ?_⟩
  exact p4Q2PZ37AKH_originalCubic_no_AJA_power_witness H thetaH
    (p4Q2PZ37AIM_elementaryCubicSmallCoupling_pos H) le_rfl

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

/-! Seven new theorems; each has an independent kernel axiom audit. -/
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKH_originalSource_top_overlap_of_rawFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKH_originalAllPowers_energy_ge_rawFloor_sq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKH_originalCubic_AJA_le_halfVariance_sq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKH_originalCubicAllPowers_ge_nineQuarters_AJA
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKH_originalCubic_no_AJA_power_witness
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKH_originalAJA_witness_requires_above_cubic
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKH_originalOutsideAIL_endpoint_certificate
