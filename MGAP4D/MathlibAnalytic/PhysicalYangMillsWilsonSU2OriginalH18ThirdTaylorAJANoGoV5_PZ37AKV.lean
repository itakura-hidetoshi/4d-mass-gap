import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalH16HaarBudgetTopResidualV5_PZ37AKU
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AKV — actual original SU(2) AJA no-witness and full-top/Haar comparison through H18

The genuine SU(2) Haar second moment E[chi²]=1/4, original zero mean and
|chi|<=1 remain unchanged. The pinned Real.exp_bound with n=3 gives
|exp x - (1+x+x²/2)| <= 2|x|³/9 on |x|<=1, hence the genuine
pointwise bound exp x <=1+x+(13/18)x² and MGF <=1+13 beta²/72.
Apply the identical AIF crossing product, AKQ original Haar-budget/top
comparison and unchanged beta0=log(3/2)/64, pH=24(H+1)^3 to H<=18.

This improves an estimate of the ORIGINAL Haar law; no new Haar mass,
operator, source, margin or model is substituted. The true negative
Haar-region mass remains unmeasured. Nothing proves a strict sign of
the full-top residual, H>=19 bounds, or Hamiltonian/continuum mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4900000
set_option synthInstance.maxHeartbeats 1050000

/-- Pinned third-order exponential remainder, simplified to a positive
quadratic bound on [-1,1]. Strictly stronger than AKS's x² remainder. -/
theorem real_exp_le_one_add_thirteenEighteenths_sq_akv
    (x : ℝ) (hx : |x| ≤ 1) :
    Real.exp x ≤ 1 + x + (13 / 18 : ℝ) * x ^ 2 := by
  have hPoly :
      (∑ m ∈ Finset.range 3, x ^ m / (m.factorial : ℝ)) =
        1 + x + x ^ 2 / 2 := by
    norm_num [Finset.sum_range_succ, Nat.factorial] <;> ring
  have hBound := Real.exp_bound (x := x) hx (n := 3) (by decide)
  rw [hPoly] at hBound
  have hRem :
      |Real.exp x - (1 + x + x ^ 2 / 2)| ≤
        |x| ^ 3 * (2 / 9 : ℝ) := by
    convert hBound using 1 <;> norm_num [Nat.factorial]
  have hAbs3 : |x| ^ 3 ≤ x ^ 2 := by
    calc
      |x| ^ 3 = |x| ^ 2 * |x| := by ring
      _ ≤ |x| ^ 2 * 1 := mul_le_mul_of_nonneg_left hx (sq_nonneg _)
      _ = x ^ 2 := by simp [sq_abs]
  have hUpper := (abs_le.mp hRem).2
  nlinarith only [hUpper, hAbs3]

local notation "GK" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AKV_group : IsTopologicalGroup GK :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AKV_compact : CompactSpace GK :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AKV_countable : SecondCountableTopology GK :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AKV_measurable : MeasurableSpace GK :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AKV_borel : BorelSpace GK :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AKV_links (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

namespace GroundStatePosteriorJoint

local notation "nuK" => normalizedCompactHaar GK
local notation "chiK" => p4Q2PZ35C_originalOneLinkCharacter
local notation "zK" => p4Q2PZ37AIF_originalSingleLinkPartition
local notation "beta0" => p4Q2PZ37ADC_fixedCoupling
local instance p4Q2PZ37AKV_singleHaarProbability : IsProbabilityMeasure nuK :=
  normalizedCompactHaar_isProbabilityMeasure GK

/-- Exact genuine SU(2) Haar variance of the SAME Wilson character,
obtained from ACK's existing four-translate Gram, not a replacement law. -/
theorem p4Q2PZ37AKV_originalSingleLinkCharacter_secondMoment :
    (∫ g : GK, chiK g ^ 2 ∂nuK) = (1 / 4 : ℝ) := by
  have h := p4Q2PZ37ACK_fourModeCharacter_gram (0 : Fin 4) (0 : Fin 4)
  simpa [p4Q2PZ37ACK_fourModeCharacter_zero, pow_two] using h

/-- A variance-sensitive MGF upper bound, retaining the original Haar
integral for the genuine SU(2) one-link Wilson character. -/
theorem p4Q2PZ37AKV_originalSingleLinkCharacter_mgf_le_thirteenSeventyTwo
    (beta : ℝ) (hbeta : 0 ≤ beta) (hOne : beta ≤ 1) :
    ProbabilityTheory.mgf chiK nuK beta ≤ 1 + 13 * beta ^ 2 / 72 := by
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
  have hQuadratic : Integrable (fun g : GK => (13 / 18 : ℝ) * beta ^ 2 * chiK g ^ 2) nuK :=
    hSqInt.const_mul ((13 / 18 : ℝ) * beta ^ 2)
  have hPoly : Integrable (fun g : GK =>
      (1 : ℝ) + beta * chiK g + (13 / 18 : ℝ) * beta ^ 2 * chiK g ^ 2) nuK :=
    (hConst.add hScaled).add hQuadratic
  have hConstIntegral : (∫ g : GK, (1 : ℝ) ∂nuK) = 1 := by
    simp
  have hLinearIntegral : (∫ g : GK, beta * chiK g ∂nuK) = 0 := by
    rw [integral_const_mul, p4Q2PZ37AIQ_originalSingleLinkCharacter_mean_zero, mul_zero]
  have hQuadraticIntegral :
      (∫ g : GK, (13 / 18 : ℝ) * beta ^ 2 * chiK g ^ 2 ∂nuK) = 13 * beta ^ 2 / 72 := by
    rw [integral_const_mul,
      p4Q2PZ37AKV_originalSingleLinkCharacter_secondMoment]
    ring
  have hPolyIntegral :
      (∫ g : GK, ((1 : ℝ) + beta * chiK g + (13 / 18 : ℝ) * beta ^ 2 * chiK g ^ 2) ∂nuK) =
      1 + 13 * beta ^ 2 / 72 := by
    calc
      _ = (∫ g : GK, ((1 : ℝ) + beta * chiK g) ∂nuK) +
          (∫ g : GK, (13 / 18 : ℝ) * beta ^ 2 * chiK g ^ 2 ∂nuK) :=
        integral_add (hConst.add hScaled) hQuadratic
      _ = ((∫ g : GK, (1 : ℝ) ∂nuK) +
          (∫ g : GK, beta * chiK g ∂nuK)) +
          (∫ g : GK, (13 / 18 : ℝ) * beta ^ 2 * chiK g ^ 2 ∂nuK) := by
        exact congrArg
          (fun t : ℝ => t + (∫ g : GK, (13 / 18 : ℝ) * beta ^ 2 * chiK g ^ 2 ∂nuK))
          (integral_add hConst hScaled)
      _ = 1 + 13 * beta ^ 2 / 72 := by
        rw [hConstIntegral, hLinearIntegral, hQuadraticIntegral]
        ring
  have hExp : Integrable (fun g : GK => Real.exp (beta * chiK g)) nuK :=
    p4Q2PZ37AIQ_originalSingleLinkCharacter_subgaussian.integrable_exp_mul beta
  have hTaylor (g : GK) :
      Real.exp (beta * chiK g) ≤
        1 + beta * chiK g + (13 / 18 : ℝ) * beta ^ 2 * chiK g ^ 2 := by
    have hChi : |chiK g| ≤ (1 : ℝ) :=
      abs_le.mpr (p4Q2PZ37AIQ_originalSingleLinkCharacter_mem_interval g)
    have hBetaChi : |beta * chiK g| ≤ 1 := by
      calc
        |beta * chiK g| = beta * |chiK g| := by
          rw [abs_mul, abs_of_nonneg hbeta]
        _ ≤ beta * 1 := mul_le_mul_of_nonneg_left hChi hbeta
        _ = beta := by ring
        _ ≤ 1 := hOne
    have hRemainder :=
      real_exp_le_one_add_thirteenEighteenths_sq_akv (beta * chiK g) hBetaChi
    nlinarith only [hRemainder]
  calc
    ProbabilityTheory.mgf chiK nuK beta =
        ∫ g : GK, Real.exp (beta * chiK g) ∂nuK := rfl
    _ ≤ ∫ g : GK,
        ((1 : ℝ) + beta * chiK g + (13 / 18 : ℝ) * beta ^ 2 * chiK g ^ 2) ∂nuK :=
      integral_mono hExp hPoly hTaylor
    _ = 1 + 13 * beta ^ 2 / 72 := hPolyIntegral

/-- Refine the genuine original one-link partition at beta<=1 without
a fictitious Gaussian SU(2) law or modified Wilson factor. -/
theorem p4Q2PZ37AKV_originalSingleLinkPartition_le_thirteenSeventyTwoGaussian
    (beta : ℝ) (hbeta : 0 ≤ beta) (hOne : beta ≤ 1) :
    zK beta ≤ Real.exp (-beta + 13 * beta ^ 2 / 72) := by
  have hMGF := p4Q2PZ37AKV_originalSingleLinkCharacter_mgf_le_thirteenSeventyTwo
    beta hbeta hOne
  have hTangent := Real.add_one_le_exp (13 * beta ^ 2 / 72)
  calc
    zK beta = Real.exp (-beta) * ProbabilityTheory.mgf chiK nuK beta :=
      p4Q2PZ37AIQ_originalSingleLinkPartition_characterMGF beta
    _ ≤ Real.exp (-beta) * (1 + 13 * beta ^ 2 / 72) :=
      mul_le_mul_of_nonneg_left hMGF (Real.exp_pos _).le
    _ ≤ Real.exp (-beta) * Real.exp (13 * beta ^ 2 / 72) :=
      mul_le_mul_of_nonneg_left (by linarith only [hTangent]) (Real.exp_pos _).le
    _ = Real.exp (-beta + 13 * beta ^ 2 / 72) :=
      (Real.exp_add _ _).symm

/-- The ACTUAL original crossing partition is a finite product of the
single-link Haar factor, as already proved in AIF/AIP. -/
theorem p4Q2PZ37AKV_originalCrossingPartition_le_thirteenSeventyTwoGaussian
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (hOne : beta ≤ 1) :
    p4Q2PZ37AIF_originalCrossingPartition H beta ≤
      Real.exp (p4Q2PZ37AFZ_plaquetteCount H * (-beta + 13 * beta ^ 2 / 72)) := by
  let nH := Nat.card (PeriodicHypercubicEvenSpatialSliceLink H)
  have hPow := pow_le_pow_left₀
    (p4Q2PZ37AIF_originalSingleLinkPartition_pos beta).le
    (p4Q2PZ37AKV_originalSingleLinkPartition_le_thirteenSeventyTwoGaussian
      beta hbeta hOne) nH
  have hExp :
      Real.exp (-beta + 13 * beta ^ 2 / 72) ^ nH =
      Real.exp (p4Q2PZ37AFZ_plaquetteCount H * (-beta + 13 * beta ^ 2 / 72)) := by
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

local instance p4Q2PZ37AKV_probability : IsProbabilityMeasure muT := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- Bound the exact original plaquette count through H=18.
This is NOT a rescaled or synthetic lattice count. -/
theorem p4Q2PZ37AKV_originalPlaquetteCount_le_eighteen
    (hH : H ≤ 18) : pT ≤ 164616 := by
  have hHR : (H : ℝ) ≤ 18 := by exact_mod_cast hH
  have hCube : ((H : ℝ) + 1) ^ 3 ≤ (19 : ℝ) ^ 3 :=
    pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (H : ℝ) + 1)
      (by linarith only [hHR]) 3
  rw [p4Q2PZ37AIB_plaquetteCount_exact]
  norm_num at hCube ⊢
  nlinarith only [hCube]

/-- A fully rational certificate for AKS's *sharper* genuine SU(2)
Haar-character quarter-Gaussian partition test through H=18. -/
theorem p4Q2PZ37AKV_originalFixedCoupling_thirteenSeventyTwoBudget_le_logFour
    (hH : H ≤ 18) :
    13 * beta0 ^ 2 * pT / 72 ≤ Real.log 4 := by
  have hb0 : 0 ≤ beta0 := p4Q2PZ37ADC_fixedCoupling_pos.le
  have hb : beta0 ≤ (1 / 156 : ℝ) :=
    p4Q2PZ37AKO_originalFixedCoupling_le_oneOver156
  have hp : pT ≤ (164616 : ℝ) :=
    p4Q2PZ37AKV_originalPlaquetteCount_le_eighteen H hH
  have hbSq := pow_le_pow_left₀ hb0 hb 2
  have hMul1 := mul_le_mul_of_nonneg_right hbSq (p4Q2PZ37AHN_count_pos H).le
  have hMul2 := mul_le_mul_of_nonneg_left hp (sq_nonneg (1 / 156 : ℝ))
  have hSmall : 13 * beta0 ^ 2 * pT / 72 ≤ (11 / 8 : ℝ) := by
    nlinarith only [hMul1, hMul2]
  exact hSmall.trans p4Q2PZ37AKO_elevenEighths_le_log_four

/-- The genuine original negative-set Haar mass is bounded by one
and AKS's original SU(2) partition estimate proves AKQ's ACTUAL
partition-Haar no-go criterion, for every H<=16. -/
theorem p4Q2PZ37AKV_originalFixedCoupling_partitionHaarMass_of_le_eighteen
    (hH : H ≤ 18) :
    Measure.real muT ET * ZT beta0 ≤
      4 * Real.exp (-(beta0 * pT)) := by
  have hOne : beta0 ≤ (1 : ℝ) := by
    have h := p4Q2PZ37AKO_originalFixedCoupling_le_oneOver156
    linarith only [h]
  have hQuarter : 13 * beta0 ^ 2 * pT / 72 ≤ Real.log 4 :=
    p4Q2PZ37AKV_originalFixedCoupling_thirteenSeventyTwoBudget_le_logFour H hH
  have hExpFour : Real.exp (13 * beta0 ^ 2 * pT / 72) ≤ 4 := by
    calc
      _ ≤ Real.exp (Real.log 4) := Real.exp_le_exp.mpr hQuarter
      _ = 4 := Real.exp_log (by norm_num)
  have hZ :
      ZT beta0 ≤ Real.exp (-(beta0 * pT)) *
        Real.exp (13 * beta0 ^ 2 * pT / 72) := by
    calc
      _ ≤ Real.exp (pT * (-beta0 + beta0 ^ 2 / 4)) :=
        p4Q2PZ37AKV_originalCrossingPartition_le_thirteenSeventyTwoGaussian H
          beta0 p4Q2PZ37ADC_fixedCoupling_pos.le hOne
      _ = Real.exp (-(beta0 * pT)) * Real.exp (13 * beta0 ^ 2 * pT / 72) := by
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
    _ ≤ Real.exp (-(beta0 * pT)) * Real.exp (13 * beta0 ^ 2 * pT / 72) := hZ
    _ ≤ Real.exp (-(beta0 * pT)) * 4 :=
      mul_le_mul_of_nonneg_left hExpFour (Real.exp_pos _).le
    _ = 4 * Real.exp (-(beta0 * pT)) := by ring

/-- No strict ORIGINAL AJA finite-power witness exists at fixed beta0
for any genuine original finite volume H<=16; the result does not
use measured negative Haar masses or change the strict original budget. -/
theorem p4Q2PZ37AKV_originalFixedCoupling_le_eighteen_no_AJA_power_witness
    (hH : H ≤ 18) :
    ¬ ∃ n : ℕ,
      ‖((ST beta0 p4Q2PZ37ADC_fixedCoupling_pos.le) ^ n) fT‖ ^ 2 <
        (mT beta0 p4Q2PZ37ADC_fixedCoupling_pos.le) ^ 2 *
          Measure.real muT ET := by
  exact p4Q2PZ37AKQ_original_no_AJA_witness_of_partitionHaarMass
    H beta0 p4Q2PZ37ADC_fixedCoupling_pos
    (p4Q2PZ37AKV_originalFixedCoupling_partitionHaarMass_of_le_eighteen H hH)

/-- In particular, the unchanged original physical H=18 slab
admits no original AJA strict finite-power witness at beta0. -/
theorem p4Q2PZ37AKV_originalH18_no_AJA_power_witness :
    ¬ ∃ n : ℕ,
      ‖((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          18 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le) ^ n)
        (p4Q2PZ37ZW_originalCenteredPhysicalDirection 18)‖ ^ 2 <
      (p4Q2PZ37AIW_originalNormalizedNegativeMargin 18 beta0
        p4Q2PZ37ADC_fixedCoupling_pos.le) ^ 2 *
        Measure.real (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure 18 2)
          {A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration 18 2 |
            p4Q2PZ37AIW_originalNormalizedSourceTransfer 18 beta0
              p4Q2PZ37ADC_fixedCoupling_pos.le A <
              -(p4Q2PZ37AIW_originalNormalizedNegativeMargin 18 beta0
                p4Q2PZ37ADC_fixedCoupling_pos.le)} := by
  exact p4Q2PZ37AKV_originalFixedCoupling_le_eighteen_no_AJA_power_witness
    18 (by omega)


/-- The ACTUAL original Haar budget is bounded by the actual full-top
orthogonal projection for all original H<=18, without a mass estimate. -/
theorem p4Q2PZ37AKV_originalFixedCoupling_budget_le_fullTop_of_le_eighteen
    (hH : H ≤ 18) :
    (mT beta0 p4Q2PZ37ADC_fixedCoupling_pos.le) ^ 2 *
      Measure.real muT ET ≤
      ‖p4Q2PZ37AJD_originalSourceTopComponent H beta0
        p4Q2PZ37ADC_fixedCoupling_pos‖ ^ 2 := by
  exact p4Q2PZ37AKU_originalBudget_le_fullTop_of_partitionHaarMass
    H beta0 p4Q2PZ37ADC_fixedCoupling_pos
    (p4Q2PZ37AKV_originalFixedCoupling_partitionHaarMass_of_le_eighteen H hH)

/-- Non-strict sign only: the original Haar-minus-top residual <=0. -/
theorem p4Q2PZ37AKV_originalFixedCoupling_topHaarResidual_nonpos_of_le_eighteen
    (hH : H ≤ 18) :
    (mT beta0 p4Q2PZ37ADC_fixedCoupling_pos.le) ^ 2 *
      Measure.real muT ET -
      ‖p4Q2PZ37AJD_originalSourceTopComponent H beta0
        p4Q2PZ37ADC_fixedCoupling_pos‖ ^ 2 ≤ 0 := by
  exact sub_nonpos.mpr
    (p4Q2PZ37AKV_originalFixedCoupling_budget_le_fullTop_of_le_eighteen H hH)


end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.real_exp_le_one_add_thirteenEighteenths_sq_akv
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKV_originalSingleLinkCharacter_secondMoment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKV_originalSingleLinkCharacter_mgf_le_thirteenSeventyTwo
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKV_originalSingleLinkPartition_le_thirteenSeventyTwoGaussian
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKV_originalCrossingPartition_le_thirteenSeventyTwoGaussian
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKV_originalPlaquetteCount_le_eighteen
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKV_originalFixedCoupling_thirteenSeventyTwoBudget_le_logFour
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKV_originalFixedCoupling_partitionHaarMass_of_le_eighteen
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKV_originalFixedCoupling_le_eighteen_no_AJA_power_witness
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKV_originalH18_no_AJA_power_witness
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKV_originalFixedCoupling_budget_le_fullTop_of_le_eighteen
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKV_originalFixedCoupling_topHaarResidual_nonpos_of_le_eighteen
