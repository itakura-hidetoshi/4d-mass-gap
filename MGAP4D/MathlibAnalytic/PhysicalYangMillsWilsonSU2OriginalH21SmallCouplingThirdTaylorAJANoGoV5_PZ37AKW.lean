import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalH18ThirdTaylorAJANoGoV5_PZ37AKV
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AKW — original SU(2) small-coupling Taylor bound H<=21

Retain the actual original SU(2) Wilson kernel, original normalized
Haar probability, signed centered ZW source, negative AIG margin,
strict AJA budget and true full-top Q. At the original beta0<=1/156,
the pinned Real.exp_bound n=3 gives on |x|<=1/156:
 exp x <= 1 + x + (176/351)*x².
The true SU(2) Haar E chi=0 and E chi²=1/4 then give
 mgf_original(beta) <= 1+(44/351)*beta²
 Zcross_original_H(beta) <= exp(p_H*(-beta+(44/351)*beta²))
for 0<=beta<=1/156. Original plaquette count p_H=24*(H+1)^3
and fixed beta0=log(3/2)/64 certify the AKQ partition-Haar
condition for all H<=21, hence original finite-power AJA no-witness
and B_H<=||Q f0_H||², Delta_H<=0. This is NOT a numerical
Haar mass value, H>=22 result, strict residual sign/equality,
Hamiltonian gap, uniform Rayleigh lower bound or continuum mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4900000
set_option synthInstance.maxHeartbeats 1050000

/-- True third-Taylor remainder on a small fixed interval. -/
theorem real_exp_le_one_add_oneSeventySixThreeFiftyOne_sq_akw
    (x : ℝ) (hx : |x| ≤ (1 / 156 : ℝ)) :
    Real.exp x ≤ 1 + x + (176 / 351 : ℝ) * x ^ 2 := by
  have hUnit : |x| ≤ (1 : ℝ) := by linarith only [hx]
  have hPoly :
      (∑ m ∈ Finset.range 3, x ^ m / (m.factorial : ℝ)) =
        1 + x + x ^ 2 / 2 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hBound := Real.exp_bound (x := x) hUnit (n := 3) (by decide)
  rw [hPoly] at hBound
  have hRem :
      |Real.exp x - (1 + x + x ^ 2 / 2)| ≤
        |x| ^ 3 * (2 / 9 : ℝ) := by
    convert hBound using 1; norm_num [Nat.factorial]
  have hAbs3 : |x| ^ 3 ≤ (1 / 156 : ℝ) * x ^ 2 := by
    calc
      |x| ^ 3 = |x| ^ 2 * |x| := by ring
      _ ≤ |x| ^ 2 * (1 / 156 : ℝ) :=
        mul_le_mul_of_nonneg_left hx (sq_nonneg _)
      _ = (1 / 156 : ℝ) * x ^ 2 := by simp [sq_abs, mul_comm]
  have hUpper := (abs_le.mp hRem).2
  nlinarith only [hUpper, hAbs3]

local notation "GK" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AKW_group : IsTopologicalGroup GK :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AKW_compact : CompactSpace GK :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AKW_countable : SecondCountableTopology GK :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AKW_measurable : MeasurableSpace GK :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AKW_borel : BorelSpace GK :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AKW_links (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

namespace GroundStatePosteriorJoint

local notation "nuK" => normalizedCompactHaar GK
local notation "chiK" => p4Q2PZ35C_originalOneLinkCharacter
local notation "zK" => p4Q2PZ37AIF_originalSingleLinkPartition
local notation "beta0" => p4Q2PZ37ADC_fixedCoupling
local instance p4Q2PZ37AKW_singleHaarProbability : IsProbabilityMeasure nuK :=
  normalizedCompactHaar_isProbabilityMeasure GK

/-- Exact genuine SU(2) Haar variance of the SAME Wilson character,
obtained from ACK's existing four-translate Gram, not a replacement law. -/
theorem p4Q2PZ37AKW_originalSingleLinkCharacter_secondMoment :
    (∫ g : GK, chiK g ^ 2 ∂nuK) = (1 / 4 : ℝ) := by
  have h := p4Q2PZ37ACK_fourModeCharacter_gram (0 : Fin 4) (0 : Fin 4)
  simpa [p4Q2PZ37ACK_fourModeCharacter_zero, pow_two] using h

/-- A variance-sensitive MGF upper bound, retaining the original Haar
integral for the genuine SU(2) one-link Wilson character. -/
theorem p4Q2PZ37AKW_originalSingleLinkCharacter_mgf_le_fortyFourThreeFiftyOne
    (beta : ℝ) (hbeta : 0 ≤ beta) (hOne : beta ≤ (1 / 156 : ℝ)) :
    ProbabilityTheory.mgf chiK nuK beta ≤ 1 + 44 * beta ^ 2 / 351 := by
  have hChiInt : Integrable chiK nuK :=
    p4Q2PZ37AIQ_originalSingleLinkCharacter_continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hSqInt : Integrable (fun g : GK => chiK g ^ 2) nuK :=
    (p4Q2PZ37AIQ_originalSingleLinkCharacter_continuous.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hConst : Integrable (fun _ : GK => (1 : ℝ)) nuK :=
    integrable_const (μ := nuK) (1 : ℝ)
  have hScaled : Integrable (fun g : GK => beta * chiK g) nuK :=
    hChiInt.const_mul beta
  have hQuadratic : Integrable (fun g : GK => (176 / 351 : ℝ) * beta ^ 2 * chiK g ^ 2) nuK :=
    hSqInt.const_mul ((176 / 351 : ℝ) * beta ^ 2)
  have hPoly : Integrable (fun g : GK =>
      (1 : ℝ) + beta * chiK g + (176 / 351 : ℝ) * beta ^ 2 * chiK g ^ 2) nuK :=
    (hConst.add hScaled).add hQuadratic
  have hConstIntegral : (∫ g : GK, (1 : ℝ) ∂nuK) = 1 := by
    simp
  have hLinearIntegral : (∫ g : GK, beta * chiK g ∂nuK) = 0 := by
    rw [integral_const_mul, p4Q2PZ37AIQ_originalSingleLinkCharacter_mean_zero, mul_zero]
  have hQuadraticIntegral :
      (∫ g : GK, (176 / 351 : ℝ) * beta ^ 2 * chiK g ^ 2 ∂nuK) = 44 * beta ^ 2 / 351 := by
    rw [integral_const_mul,
      p4Q2PZ37AKW_originalSingleLinkCharacter_secondMoment]
    ring
  have hPolyIntegral :
      (∫ g : GK, ((1 : ℝ) + beta * chiK g + (176 / 351 : ℝ) * beta ^ 2 * chiK g ^ 2) ∂nuK) =
      1 + 44 * beta ^ 2 / 351 := by
    calc
      _ = (∫ g : GK, ((1 : ℝ) + beta * chiK g) ∂nuK) +
          (∫ g : GK, (176 / 351 : ℝ) * beta ^ 2 * chiK g ^ 2 ∂nuK) :=
        integral_add (hConst.add hScaled) hQuadratic
      _ = ((∫ g : GK, (1 : ℝ) ∂nuK) +
          (∫ g : GK, beta * chiK g ∂nuK)) +
          (∫ g : GK, (176 / 351 : ℝ) * beta ^ 2 * chiK g ^ 2 ∂nuK) := by
        exact congrArg
          (fun t : ℝ => t + (∫ g : GK, (176 / 351 : ℝ) * beta ^ 2 * chiK g ^ 2 ∂nuK))
          (integral_add hConst hScaled)
      _ = 1 + 44 * beta ^ 2 / 351 := by
        rw [hConstIntegral, hLinearIntegral, hQuadraticIntegral]
        ring
  have hExp : Integrable (fun g : GK => Real.exp (beta * chiK g)) nuK :=
    p4Q2PZ37AIQ_originalSingleLinkCharacter_subgaussian.integrable_exp_mul beta
  have hTaylor (g : GK) :
      Real.exp (beta * chiK g) ≤
        1 + beta * chiK g + (176 / 351 : ℝ) * beta ^ 2 * chiK g ^ 2 := by
    have hChi : |chiK g| ≤ (1 : ℝ) :=
      abs_le.mpr (p4Q2PZ37AIQ_originalSingleLinkCharacter_mem_interval g)
    have hBetaChi : |beta * chiK g| ≤ (1 / 156 : ℝ) := by
      calc
        |beta * chiK g| = beta * |chiK g| := by
          rw [abs_mul, abs_of_nonneg hbeta]
        _ ≤ beta * 1 := mul_le_mul_of_nonneg_left hChi hbeta
        _ = beta := by ring
        _ ≤ (1 / 156 : ℝ) := hOne
    have hRemainder :=
      real_exp_le_one_add_oneSeventySixThreeFiftyOne_sq_akw (beta * chiK g) hBetaChi
    nlinarith only [hRemainder]
  calc
    ProbabilityTheory.mgf chiK nuK beta =
        ∫ g : GK, Real.exp (beta * chiK g) ∂nuK := rfl
    _ ≤ ∫ g : GK,
        ((1 : ℝ) + beta * chiK g + (176 / 351 : ℝ) * beta ^ 2 * chiK g ^ 2) ∂nuK :=
      integral_mono hExp hPoly hTaylor
    _ = 1 + 44 * beta ^ 2 / 351 := hPolyIntegral

/-- Refine the genuine original one-link partition at beta<=1 without
a fictitious Gaussian SU(2) law or modified Wilson factor. -/
theorem p4Q2PZ37AKW_originalSingleLinkPartition_le_fortyFourThreeFiftyOneGaussian
    (beta : ℝ) (hbeta : 0 ≤ beta) (hOne : beta ≤ (1 / 156 : ℝ)) :
    zK beta ≤ Real.exp (-beta + 44 * beta ^ 2 / 351) := by
  have hMGF := p4Q2PZ37AKW_originalSingleLinkCharacter_mgf_le_fortyFourThreeFiftyOne
    beta hbeta hOne
  have hTangent := Real.add_one_le_exp (44 * beta ^ 2 / 351)
  calc
    zK beta = Real.exp (-beta) * ProbabilityTheory.mgf chiK nuK beta :=
      p4Q2PZ37AIQ_originalSingleLinkPartition_characterMGF beta
    _ ≤ Real.exp (-beta) * (1 + 44 * beta ^ 2 / 351) :=
      mul_le_mul_of_nonneg_left hMGF (Real.exp_pos _).le
    _ ≤ Real.exp (-beta) * Real.exp (44 * beta ^ 2 / 351) :=
      mul_le_mul_of_nonneg_left (by linarith only [hTangent]) (Real.exp_pos _).le
    _ = Real.exp (-beta + 44 * beta ^ 2 / 351) :=
      (Real.exp_add _ _).symm

/-- The ACTUAL original crossing partition is a finite product of the
single-link Haar factor, as already proved in AIF/AIP. -/
theorem p4Q2PZ37AKW_originalCrossingPartition_le_fortyFourThreeFiftyOneGaussian
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (hOne : beta ≤ (1 / 156 : ℝ)) :
    p4Q2PZ37AIF_originalCrossingPartition H beta ≤
      Real.exp (p4Q2PZ37AFZ_plaquetteCount H * (-beta + 44 * beta ^ 2 / 351)) := by
  let nH := Nat.card (PeriodicHypercubicEvenSpatialSliceLink H)
  have hPow := pow_le_pow_left₀
    (p4Q2PZ37AIF_originalSingleLinkPartition_pos beta).le
    (p4Q2PZ37AKW_originalSingleLinkPartition_le_fortyFourThreeFiftyOneGaussian
      beta hbeta hOne) nH
  have hExp :
      Real.exp (-beta + 44 * beta ^ 2 / 351) ^ nH =
      Real.exp (p4Q2PZ37AFZ_plaquetteCount H * (-beta + 44 * beta ^ 2 / 351)) := by
    rw [← Real.exp_nat_mul, p4Q2PZ37AIP_originalLinkCount_eq_plaquettes H]
  rw [hExp] at hPow
  simpa only [p4Q2PZ37AIF_originalCrossingPartition, Fintype.card_eq_nat_card]
    using hPow

variable (H : ℕ)

local notation "CfgT" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muT" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "pT" => p4Q2PZ37AFZ_plaquetteCount H
local notation "ZT" => p4Q2PZ37AIF_originalCrossingPartition H
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

local instance p4Q2PZ37AKW_probability : IsProbabilityMeasure muT := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- Bound the exact original plaquette count through H=21.
This is NOT a rescaled or synthetic lattice count. -/
theorem p4Q2PZ37AKW_originalPlaquetteCount_le_twentyOne
    (hH : H ≤ 21) : pT ≤ 255552 := by
  have hHR : (H : ℝ) ≤ 21 := by exact_mod_cast hH
  have hCube : ((H : ℝ) + 1) ^ 3 ≤ (22 : ℝ) ^ 3 :=
    pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (H : ℝ) + 1)
      (by linarith only [hHR]) 3
  rw [p4Q2PZ37AIB_plaquetteCount_exact]
  norm_num at hCube ⊢
  nlinarith only [hCube]

/-- A fully rational certificate for AKS's *sharper* genuine SU(2)
Haar-character forty-four/three-fifty-one small-coupling partition test through H=21. -/
theorem p4Q2PZ37AKW_originalFixedCoupling_fortyFourThreeFiftyOneBudget_le_logFour
    (hH : H ≤ 21) :
    44 * beta0 ^ 2 * pT / 351 ≤ Real.log 4 := by
  have hb0 : 0 ≤ beta0 := p4Q2PZ37ADC_fixedCoupling_pos.le
  have hb : beta0 ≤ (1 / 156 : ℝ) :=
    p4Q2PZ37AKO_originalFixedCoupling_le_oneOver156
  have hp : pT ≤ (255552 : ℝ) :=
    p4Q2PZ37AKW_originalPlaquetteCount_le_twentyOne H hH
  have hbSq := pow_le_pow_left₀ hb0 hb 2
  have hMul1 := mul_le_mul_of_nonneg_right hbSq (p4Q2PZ37AHN_count_pos H).le
  have hMul2 := mul_le_mul_of_nonneg_left hp (sq_nonneg (1 / 156 : ℝ))
  have hSmall : 44 * beta0 ^ 2 * pT / 351 ≤ (11 / 8 : ℝ) := by
    nlinarith only [hMul1, hMul2]
  exact hSmall.trans p4Q2PZ37AKO_elevenEighths_le_log_four

/-- The genuine original negative-set Haar mass is bounded by one
and AKS's original SU(2) partition estimate proves AKQ's ACTUAL
partition-Haar no-go criterion, for every H<=21. -/
theorem p4Q2PZ37AKW_originalFixedCoupling_partitionHaarMass_of_le_twentyOne
    (hH : H ≤ 21) :
    Measure.real muT ET * ZT beta0 ≤
      4 * Real.exp (-(beta0 * pT)) := by
  have hOne : beta0 ≤ (1 / 156 : ℝ) :=
    p4Q2PZ37AKO_originalFixedCoupling_le_oneOver156
  have hQuarter : 44 * beta0 ^ 2 * pT / 351 ≤ Real.log 4 :=
    p4Q2PZ37AKW_originalFixedCoupling_fortyFourThreeFiftyOneBudget_le_logFour H hH
  have hExpFour : Real.exp (44 * beta0 ^ 2 * pT / 351) ≤ 4 := by
    calc
      _ ≤ Real.exp (Real.log 4) := Real.exp_le_exp.mpr hQuarter
      _ = 4 := Real.exp_log (by norm_num)
  have hZ :
      ZT beta0 ≤ Real.exp (-(beta0 * pT)) *
        Real.exp (44 * beta0 ^ 2 * pT / 351) := by
    calc
      _ ≤ Real.exp (pT * (-beta0 + 44 * beta0 ^ 2 / 351)) :=
        p4Q2PZ37AKW_originalCrossingPartition_le_fortyFourThreeFiftyOneGaussian H
          beta0 p4Q2PZ37ADC_fixedCoupling_pos.le hOne
      _ = Real.exp (-(beta0 * pT)) * Real.exp (44 * beta0 ^ 2 * pT / 351) := by
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
    _ ≤ Real.exp (-(beta0 * pT)) * Real.exp (44 * beta0 ^ 2 * pT / 351) := hZ
    _ ≤ Real.exp (-(beta0 * pT)) * 4 :=
      mul_le_mul_of_nonneg_left hExpFour (Real.exp_pos _).le
    _ = 4 * Real.exp (-(beta0 * pT)) := by ring

/-- No strict ORIGINAL AJA finite-power witness exists at fixed beta0
for any genuine original finite volume H<=21; the result does not
use measured negative Haar masses or change the strict original budget. -/
theorem p4Q2PZ37AKW_originalFixedCoupling_le_twentyOne_no_AJA_power_witness
    (hH : H ≤ 21) :
    ¬ ∃ n : ℕ,
      ‖((ST beta0 p4Q2PZ37ADC_fixedCoupling_pos.le) ^ n) fT‖ ^ 2 <
        (mT beta0 p4Q2PZ37ADC_fixedCoupling_pos.le) ^ 2 *
          Measure.real muT ET := by
  exact p4Q2PZ37AKQ_original_no_AJA_witness_of_partitionHaarMass
    H beta0 p4Q2PZ37ADC_fixedCoupling_pos
    (p4Q2PZ37AKW_originalFixedCoupling_partitionHaarMass_of_le_twentyOne H hH)

/-- In particular, the unchanged original physical H=21 slab
admits no original AJA strict finite-power witness at beta0. -/
theorem p4Q2PZ37AKW_originalH21_no_AJA_power_witness :
    ¬ ∃ n : ℕ,
      ‖((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          21 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le) ^ n)
        (p4Q2PZ37ZW_originalCenteredPhysicalDirection 21)‖ ^ 2 <
      (p4Q2PZ37AIW_originalNormalizedNegativeMargin 21 beta0
        p4Q2PZ37ADC_fixedCoupling_pos.le) ^ 2 *
        Measure.real (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure 21 2)
          {A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration 21 2 |
            p4Q2PZ37AIW_originalNormalizedSourceTransfer 21 beta0
              p4Q2PZ37ADC_fixedCoupling_pos.le A <
              -(p4Q2PZ37AIW_originalNormalizedNegativeMargin 21 beta0
                p4Q2PZ37ADC_fixedCoupling_pos.le)} := by
  exact p4Q2PZ37AKW_originalFixedCoupling_le_twentyOne_no_AJA_power_witness
    21 (by omega)


/-- The ACTUAL original Haar budget is bounded by the actual full-top
orthogonal projection for all original H<=21, without a mass estimate. -/
theorem p4Q2PZ37AKW_originalFixedCoupling_budget_le_fullTop_of_le_twentyOne
    (hH : H ≤ 21) :
    (mT beta0 p4Q2PZ37ADC_fixedCoupling_pos.le) ^ 2 *
      Measure.real muT ET ≤
      ‖p4Q2PZ37AJD_originalSourceTopComponent H beta0
        p4Q2PZ37ADC_fixedCoupling_pos‖ ^ 2 := by
  exact p4Q2PZ37AKU_originalBudget_le_fullTop_of_partitionHaarMass
    H beta0 p4Q2PZ37ADC_fixedCoupling_pos
    (p4Q2PZ37AKW_originalFixedCoupling_partitionHaarMass_of_le_twentyOne H hH)

/-- Non-strict sign only: the original Haar-minus-top residual <=0. -/
theorem p4Q2PZ37AKW_originalFixedCoupling_topHaarResidual_nonpos_of_le_twentyOne
    (hH : H ≤ 21) :
    (mT beta0 p4Q2PZ37ADC_fixedCoupling_pos.le) ^ 2 *
      Measure.real muT ET -
      ‖p4Q2PZ37AJD_originalSourceTopComponent H beta0
        p4Q2PZ37ADC_fixedCoupling_pos‖ ^ 2 ≤ 0 := by
  exact sub_nonpos.mpr
    (p4Q2PZ37AKW_originalFixedCoupling_budget_le_fullTop_of_le_twentyOne H hH)


end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.real_exp_le_one_add_oneSeventySixThreeFiftyOne_sq_akw
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKW_originalSingleLinkCharacter_secondMoment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKW_originalSingleLinkCharacter_mgf_le_fortyFourThreeFiftyOne
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKW_originalSingleLinkPartition_le_fortyFourThreeFiftyOneGaussian
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKW_originalCrossingPartition_le_fortyFourThreeFiftyOneGaussian
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKW_originalPlaquetteCount_le_twentyOne
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKW_originalFixedCoupling_fortyFourThreeFiftyOneBudget_le_logFour
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKW_originalFixedCoupling_partitionHaarMass_of_le_twentyOne
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKW_originalFixedCoupling_le_twentyOne_no_AJA_power_witness
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKW_originalH21_no_AJA_power_witness
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKW_originalFixedCoupling_budget_le_fullTop_of_le_twentyOne
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKW_originalFixedCoupling_topHaarResidual_nonpos_of_le_twentyOne
