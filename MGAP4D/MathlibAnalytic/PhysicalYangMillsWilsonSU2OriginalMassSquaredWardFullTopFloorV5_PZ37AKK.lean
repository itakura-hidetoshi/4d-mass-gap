import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalWardCoefficientBeyondLogAJANoGoV5_PZ37AKJ
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AKK — genuine full-top floor from the squared Haar mass

Keep the unchanged finite-H SU(2) Wilson physical transfer P, normalization
S=P/||P||, original signed centered ZW source f0, original Haar probability,
full top projection Q, and original AJA margin and strict negative region.

AKG's kernel-pairing proof gives lambda <= I^2 for the genuine nonnegative
unit top vector, before weakening this to lambda <= I. Retain that square
together with AKJ's affine Ward pairing (lambda-c) F <= -d I, where
  lambda=||P||, c=Zcross*exp(-beta*p)*r(beta)^4,
  d=beta*exp(-3*beta*p)*V, I=integral psi, F=<f0,psi>.
For every beta>0 this proves lambda-c>0 and
  d^2 < d^2*lambda/(lambda-c)^2 <= ||Q f0||^2 <= ||S^n f0||^2
for every natural n. The strict improvement uses the already proved
0<lambda<1. Membership of psi in the FULL top eigenspace is proved directly;
no identification with the separately selected top vector is needed.

The new floor is a bound, not a replacement source, operator, or budget.
Comparison with the original AJA Haar budget remains conditional:
B<=floor excludes every strict power witness; a witness requires floor<B.
The converse is not asserted. This leaf does not settle a new numerical
coupling, assume top simplicity, or provide an H-uniform or continuum gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory Filter
open scoped InnerProductSpace Topology Classical ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- Keep the squared mass when descending an affine top-pairing estimate.
All physical hypotheses are supplied by the original model below. -/
theorem real_affine_massSq_overlap_floor_akk
    (lambda c d I F : ℝ)
    (hc : c ≤ lambda) (hd : 0 < d) (hI : 0 < I)
    (hMassSq : lambda ≤ I ^ 2)
    (hPair : (lambda - c) * F ≤ -d * I) :
    0 < lambda - c ∧
      d ^ 2 * lambda / (lambda - c) ^ 2 ≤ F ^ 2 := by
  have hGap : 0 < lambda - c := by
    by_contra hn
    have hz : lambda - c = 0 :=
      le_antisymm (le_of_not_gt hn) (sub_nonneg.mpr hc)
    rw [hz, zero_mul] at hPair
    have hPos := mul_pos hd hI
    linarith only [hPair, hPos]
  have hBound : d * I ≤ (lambda - c) * (-F) := by
    nlinarith only [hPair]
  have hSquare :=
    pow_le_pow_left₀ (mul_nonneg hd.le hI.le) hBound 2
  have hScaled :=
    mul_le_mul_of_nonneg_left hMassSq (sq_nonneg d)
  refine ⟨hGap, (div_le_iff₀ (pow_pos hGap 2)).2 ?_⟩
  nlinarith only [hSquare, hScaled]

local notation "GK" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AKK_group : IsTopologicalGroup GK :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AKK_compact : CompactSpace GK :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AKK_countable : SecondCountableTopology GK :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AKK_measurable : MeasurableSpace GK :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AKK_borel : BorelSpace GK :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AKK_links (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

namespace GroundStatePosteriorJoint

variable (H : ℕ)

local notation "CfgK" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muK" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "PhysK" => periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H 2
local notation "fK" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "VK" => p4Q2PZ37AHN_originalSource_HaarSecondMoment H
local notation "PK" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator H 2 (by norm_num)
local notation "SK" => periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator H 2 (by norm_num)
local notation "psiK" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector H 2 (by norm_num)
local notation "TopK" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace H 2 (by norm_num)
local notation "uK" => p4Q2PZ37AIW_originalNormalizedSourceTransfer H
local notation "mK" => p4Q2PZ37AIW_originalNormalizedNegativeMargin H
local notation "cK" => p4Q2PZ37AKI_originalAffineCoefficient H
local notation "dK" => p4Q2PZ37AKI_originalWardTopFloor H

local instance p4Q2PZ37AKK_probability : IsProbabilityMeasure muK := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- Auxiliary lower bound built only from the original norm and Ward data.
Its denominator is proved strictly positive below. -/
def p4Q2PZ37AKK_originalMassSquaredWardFloor
    (beta : ℝ) (hbeta : 0 < beta) : ℝ :=
  (dK beta) ^ 2 * ‖PK beta hbeta.le‖ /
    (‖PK beta hbeta.le‖ - cK beta) ^ 2

local notation "LK" => p4Q2PZ37AKK_originalMassSquaredWardFloor H

/-- Export the unweakened genuine Haar mass-square estimate already used
inside AKG. The unit top vector and full Wilson kernel are unchanged. -/
theorem p4Q2PZ37AKK_originalNonnegativeTop_massSq_ge_norm
    (beta : ℝ) (hbeta : 0 ≤ beta) :
    ‖PK beta hbeta‖ ≤
      (∫ A : CfgK, (psiK beta hbeta : Lp ℝ 2 muK) A ∂muK) ^ 2 := by
  let P : PhysK →L[ℝ] PhysK := PK beta hbeta
  let psi : PhysK := psiK beta hbeta
  let g : Lp ℝ 2 muK := psi
  let K : Lp ℝ 2 (Measure.prod muK muK) :=
    periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2
      H 2 (by norm_num) beta hbeta
  let I : ℝ := ∫ A : CfgK, g A ∂muK
  have hg : ∀ᵐ A ∂muK, 0 ≤ g A :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_ae_nonnegative
      H 2 (by norm_num) beta hbeta
  have hUnit : ‖psi‖ = 1 :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_norm
      H 2 (by norm_num) beta hbeta
  have hEigen : P psi = ‖P‖ • psi :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabNonnegativeTopEigenvector_eigen
      H 2 (by norm_num) beta hbeta
  have hK : ∀ᵐ z ∂(Measure.prod muK muK), K z ≤ 1 := by
    have hRep := periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernelPairL2_coeFn
      H 2 (by norm_num) beta hbeta
    filter_upwards [hRep] with z hz
    change K z = periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel
      H 2 beta z.1 z.2 at hz
    rw [hz]
    exact (le_abs_self _).trans
      (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabKernel_abs_le_one
        H 2 (by norm_num) beta hbeta z.1 z.2)
  have hPair : realL2HilbertSchmidtKernelPairing K g g = inner ℝ (P psi) psi := by
    change realL2HilbertSchmidtKernelPairing K g g =
      inner ℝ (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator
        H 2 (by norm_num) beta hbeta g) g
    exact (periodicHypercubicEvenSpecialUnitaryTemporalGaugeOneSlabTransferOperator_inner
      H 2 (by norm_num) beta hbeta g g).symm
  have hQuad : inner ℝ (P psi) psi = ‖P‖ :=
    realHilbert_inner_eq_opNorm_of_unit_eigen P psi hUnit hEigen
  have hSq : ‖P‖ ≤ I ^ 2 := by
    have h := realL2_nonnegative_kernelPairing_le_mass_sq_akg muK K g hK hg
    rw [hPair, hQuad] at h
    exact h
  exact hSq

/-- The affine denominator is positive and the original nonnegative top
overlap dominates the new floor, for every positive coupling. -/
theorem p4Q2PZ37AKK_originalAffineGap_and_overlap_floor
    (beta : ℝ) (hbeta : 0 < beta) :
    0 < ‖PK beta hbeta.le‖ - cK beta ∧
      LK beta hbeta ≤ (inner ℝ fK (psiK beta hbeta.le)) ^ 2 := by
  let lambda : ℝ := ‖PK beta hbeta.le‖
  let I : ℝ :=
    ∫ A : CfgK, (psiK beta hbeta.le : Lp ℝ 2 muK) A ∂muK
  have hNorm : 0 < lambda :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 (by norm_num) beta hbeta.le
  have hMass : lambda ≤ I :=
    p4Q2PZ37AKG_originalNonnegativeTop_mass_ge_norm H beta hbeta.le
  have hMassSq : lambda ≤ I ^ 2 :=
    p4Q2PZ37AKK_originalNonnegativeTop_massSq_ge_norm H beta hbeta.le
  have hc : 0 ≤ cK beta ∧ cK beta ≤ lambda :=
    p4Q2PZ37AKI_originalAffineCoefficient_bounds H beta hbeta
  have hV : 0 < VK := (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  have hd : 0 < dK beta := by
    dsimp [p4Q2PZ37AKI_originalWardTopFloor]
    positivity
  exact real_affine_massSq_overlap_floor_akk
    lambda (cK beta) (dK beta) I (inner ℝ fK (psiK beta hbeta.le))
    hc.2 hd (hNorm.trans_le hMass) hMassSq
    (p4Q2PZ37AKJ_originalAffineTopPairing H beta hbeta)

/-- Pair with the actual nonnegative top vector through the complete top
projection. No selected-vacuum identification or dimension premise is used. -/
theorem p4Q2PZ37AKK_originalNonnegativeTop_overlap_sq_le_fullTop
    (beta : ℝ) (hbeta : 0 < beta) :
    (inner ℝ fK (psiK beta hbeta.le)) ^ 2 ≤
      ‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2 := by
  let P : PhysK →L[ℝ] PhysK := PK beta hbeta.le
  let S : PhysK →L[ℝ] PhysK := SK beta hbeta.le
  let psi : PhysK := psiK beta hbeta.le
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
  have hMem : psi ∈ TopK beta hbeta.le :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspace_mem
      H 2 (by norm_num) beta hbeta.le psi).2 hFix
  have hBound :=
    p4Q2PZ37AJE_originalSource_fullTop_inner_bound H beta hbeta psi hMem
  rw [hUnit, mul_one] at hBound
  have hSquare := pow_le_pow_left₀ (abs_nonneg (inner ℝ fK psi)) hBound 2
  simpa only [sq_abs] using hSquare

/-- Unconditional lower bound on the genuine full-top source component,
retaining both the squared Haar mass and the affine Ward coefficient. -/
theorem p4Q2PZ37AKK_originalFullTop_energy_ge_massSquaredWardFloor
    (beta : ℝ) (hbeta : 0 < beta) :
    LK beta hbeta ≤
      ‖p4Q2PZ37AJD_originalSourceTopComponent H beta hbeta‖ ^ 2 :=
  (p4Q2PZ37AKK_originalAffineGap_and_overlap_floor H beta hbeta).2.trans
    (p4Q2PZ37AKK_originalNonnegativeTop_overlap_sq_le_fullTop H beta hbeta)

/-- The same genuine lower bound survives every natural transfer power,
including power zero, because the complete top component is preserved. -/
theorem p4Q2PZ37AKK_originalAllPowers_energy_ge_massSquaredWardFloor
    (beta : ℝ) (hbeta : 0 < beta) (n : ℕ) :
    LK beta hbeta ≤ ‖((SK beta hbeta.le) ^ n) fK‖ ^ 2 :=
  (p4Q2PZ37AKK_originalFullTop_energy_ge_massSquaredWardFloor H beta hbeta).trans
    (p4Q2PZ37AJH_originalFullTop_norm_sq_le_transferPower H beta hbeta n)

/-- The improvement over AKI's d^2 is strict at every finite H,beta>0.
This follows from the original raw norm being strictly below one. -/
theorem p4Q2PZ37AKK_originalMassSquaredWardFloor_strictly_gt_wardFloor_sq
    (beta : ℝ) (hbeta : 0 < beta) :
    (dK beta) ^ 2 < LK beta hbeta := by
  let lambda : ℝ := ‖PK beta hbeta.le‖
  let c : ℝ := cK beta
  have hNorm : 0 < lambda :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator_norm_pos
      H 2 (by norm_num) beta hbeta.le
  have hLt : lambda < 1 :=
    p4Q2PZ37AIV_originalPhysicalTransfer_norm_lt_one H beta hbeta
  have hc : 0 ≤ c ∧ c ≤ lambda :=
    p4Q2PZ37AKI_originalAffineCoefficient_bounds H beta hbeta
  have hGap : 0 < lambda - c :=
    (p4Q2PZ37AKK_originalAffineGap_and_overlap_floor H beta hbeta).1
  have hGapLe : lambda - c ≤ lambda := sub_le_self lambda hc.1
  have hGapSq : (lambda - c) ^ 2 ≤ lambda ^ 2 :=
    pow_le_pow_left₀ hGap.le hGapLe 2
  have hNormSq : lambda ^ 2 < lambda := by
    have hPos := mul_pos hNorm (sub_pos.mpr hLt)
    nlinarith only [hPos]
  have hStrict : (lambda - c) ^ 2 < lambda := hGapSq.trans_lt hNormSq
  have hV : 0 < VK := (p4Q2PZ37AHN_originalSource_twoHaarMoments_pos H).2
  have hd : 0 < dK beta := by
    dsimp [p4Q2PZ37AKI_originalWardTopFloor]
    positivity
  change (dK beta) ^ 2 < (dK beta) ^ 2 * lambda / (lambda - c) ^ 2
  exact (lt_div_iff₀ (pow_pos hGap 2)).2
    (mul_lt_mul_of_pos_left hStrict (pow_pos hd 2))

/-- Compare with the unchanged original AJA Haar budget. A certified
budget below the new floor excludes ALL strict finite-power witnesses. -/
theorem p4Q2PZ37AKK_originalAJA_no_witness_of_budget_le_massSquaredWardFloor
    (beta : ℝ) (hbeta : 0 < beta)
    (hBudget :
      (mK beta hbeta.le) ^ 2 *
        Measure.real muK
          {A : CfgK | uK beta hbeta.le A < -(mK beta hbeta.le)} ≤
        LK beta hbeta) :
    ¬ ∃ n : ℕ, ‖((SK beta hbeta.le) ^ n) fK‖ ^ 2 <
      (mK beta hbeta.le) ^ 2 *
        Measure.real muK
          {A : CfgK | uK beta hbeta.le A < -(mK beta hbeta.le)} := by
  rintro ⟨n, hn⟩
  exact (not_lt_of_ge (hBudget.trans
    (p4Q2PZ37AKK_originalAllPowers_energy_ge_massSquaredWardFloor
      H beta hbeta n))) hn

/-- Any genuine original AJA witness must beat the new floor. This
necessary test is not a sufficient witness construction. -/
theorem p4Q2PZ37AKK_originalAJA_witness_requires_floor_lt_budget
    (beta : ℝ) (hbeta : 0 < beta)
    (hWitness :
      ∃ n : ℕ, ‖((SK beta hbeta.le) ^ n) fK‖ ^ 2 <
        (mK beta hbeta.le) ^ 2 *
          Measure.real muK
            {A : CfgK | uK beta hbeta.le A < -(mK beta hbeta.le)}) :
    LK beta hbeta <
      (mK beta hbeta.le) ^ 2 *
        Measure.real muK
          {A : CfgK | uK beta hbeta.le A < -(mK beta hbeta.le)} := by
  obtain ⟨n, hn⟩ := hWitness
  exact (p4Q2PZ37AKK_originalAllPowers_energy_ge_massSquaredWardFloor
    H beta hbeta n).trans_lt hn

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

/-! Audit every new named definition and theorem. -/
#print axioms MGAP4D.MathlibAnalytic.real_affine_massSq_overlap_floor_akk
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKK_originalMassSquaredWardFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKK_originalNonnegativeTop_massSq_ge_norm
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKK_originalAffineGap_and_overlap_floor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKK_originalNonnegativeTop_overlap_sq_le_fullTop
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKK_originalFullTop_energy_ge_massSquaredWardFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKK_originalAllPowers_energy_ge_massSquaredWardFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKK_originalMassSquaredWardFloor_strictly_gt_wardFloor_sq
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKK_originalAJA_no_witness_of_budget_le_massSquaredWardFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKK_originalAJA_witness_requires_floor_lt_budget
