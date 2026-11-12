import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalH14WeightedHaarMassThresholdV5_PZ37AKQ
import MGAP4D.MathlibAnalytic.SpecialUnitaryTwoFourModeHaarV5_PZ37ACK
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AKS — original H14 Haar-character second moment sharpens AJA no-go

Preserve ALL original SU(2) Wilson action, original Haar probabilities,
original crossing partition, physical one-slab P and normalized S,
original beta0=log(3/2)/64, genuine centered ZW source,
negative region {u<-m}, unchanged margin, full-top, AJA budget,
H and every pinned dependency.

AIQ's universal Hoeffding control of the original link character
chi=1-E is exp(beta^2/2), which ceases to prove the AKN scalar condition
at H14. But ACK ALREADY mechanically proves the exact original SU2 Haar
Gram E[chi^2]=1/4, with E[chi]=0 and |chi|<=1. For 0<=beta<=1,
the exact exp Taylor remainder |exp(x)-1-x|<=x^2 (|x|<=1)
and the genuine Haar moment give
  mgf chi beta <= 1+beta^2/4 <= exp(beta^2/4).
The original one-link and crossing partitions therefore satisfy
  z(beta)<=exp(-beta+beta^2/4),
  Zcross_H(beta)<=exp(p_H*(-beta+beta^2/4)).
The original beta0<=1/156 and original p14=81000 prove
  beta0^2*81000/4 <= 11/8 <= log 4.
Thus Zcross_14(beta0)<=4*exp(-beta0*p14); since the ACTUAL
original negative Haar mass r14<=1, AKQ's unchanged genuine
partition-mass theorem excludes the ORIGINAL strict finite-power
AJA witness at H14, with NO numerical Haar mass measurement.
Combining with AKO, this excludes every H<=14.

This is a new analytic no-witness route, not a certification of an
upper bound on r14 or a continuum Yang-Mills mass gap. The original
H14 Haar mass and delta14 remain NO_DATA.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4900000
set_option synthInstance.maxHeartbeats 1050000

/-- The pinned exact real exponential remainder gives a quadratic
pointwise upper bound on the full interval [-1,1]. -/
theorem real_exp_le_one_add_sq_of_abs_le_one_aks
    (x : ℝ) (hx : |x| ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 := by
  have h := Real.abs_exp_sub_one_sub_id_le hx
  have hUpper := (abs_le.mp h).2
  linarith only [hUpper]

local notation "GK" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AKS_group : IsTopologicalGroup GK :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AKS_compact : CompactSpace GK :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AKS_countable : SecondCountableTopology GK :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AKS_measurable : MeasurableSpace GK :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AKS_borel : BorelSpace GK :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AKS_links (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

namespace GroundStatePosteriorJoint

local notation "nuK" => normalizedCompactHaar GK
local notation "chiK" => p4Q2PZ35C_originalOneLinkCharacter
local notation "zK" => p4Q2PZ37AIF_originalSingleLinkPartition
local notation "beta0" => p4Q2PZ37ADC_fixedCoupling
local instance p4Q2PZ37AKS_singleHaarProbability : IsProbabilityMeasure nuK :=
  normalizedCompactHaar_isProbabilityMeasure GK

/-- Exact genuine SU(2) Haar variance of the SAME Wilson character,
obtained from ACK's existing four-translate Gram, not a replacement law. -/
theorem p4Q2PZ37AKS_originalSingleLinkCharacter_secondMoment :
    (∫ g : GK, chiK g ^ 2 ∂nuK) = (1 / 4 : ℝ) := by
  have h := p4Q2PZ37ACK_fourModeCharacter_gram (0 : Fin 4) (0 : Fin 4)
  simpa [p4Q2PZ37ACK_fourModeCharacter_zero, pow_two] using h

/-- A variance-sensitive MGF upper bound, retaining the original Haar
integral for the genuine SU(2) one-link Wilson character. -/
theorem p4Q2PZ37AKS_originalSingleLinkCharacter_mgf_le_quarter
    (beta : ℝ) (hbeta : 0 ≤ beta) (hOne : beta ≤ 1) :
    ProbabilityTheory.mgf chiK nuK beta ≤ 1 + beta ^ 2 / 4 := by
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
  have hQuadratic : Integrable (fun g : GK => beta ^ 2 * chiK g ^ 2) nuK :=
    hSqInt.const_mul (beta ^ 2)
  have hPoly : Integrable (fun g : GK =>
      (1 : ℝ) + beta * chiK g + beta ^ 2 * chiK g ^ 2) nuK :=
    (hConst.add hScaled).add hQuadratic
  have hPolyIntegral :
      (∫ g : GK, ((1 : ℝ) + beta * chiK g + beta ^ 2 * chiK g ^ 2) ∂nuK) =
      1 + beta ^ 2 / 4 := by
    change (∫ g : GK,
        (((fun _ : GK => (1 : ℝ)) + (fun g : GK => beta * chiK g)) +
          (fun g : GK => beta ^ 2 * chiK g ^ 2)) g ∂nuK) =
        1 + beta ^ 2 / 4
    rw [integral_add (hConst.add hScaled) hQuadratic,
      integral_add hConst hScaled, integral_const_mul, integral_const_mul,
      p4Q2PZ37AIQ_originalSingleLinkCharacter_mean_zero,
      p4Q2PZ37AKS_originalSingleLinkCharacter_secondMoment]
    simp only [integral_const, probReal_univ, one_smul, mul_zero, add_zero]
    ring
  have hExp : Integrable (fun g : GK => Real.exp (beta * chiK g)) nuK :=
    p4Q2PZ37AIQ_originalSingleLinkCharacter_subgaussian.integrable_exp_mul beta
  have hTaylor (g : GK) :
      Real.exp (beta * chiK g) ≤
        1 + beta * chiK g + beta ^ 2 * chiK g ^ 2 := by
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
      real_exp_le_one_add_sq_of_abs_le_one_aks (beta * chiK g) hBetaChi
    nlinarith only [hRemainder]
  calc
    ProbabilityTheory.mgf chiK nuK beta =
        ∫ g : GK, Real.exp (beta * chiK g) ∂nuK := rfl
    _ ≤ ∫ g : GK,
        ((1 : ℝ) + beta * chiK g + beta ^ 2 * chiK g ^ 2) ∂nuK :=
      integral_mono hExp hPoly hTaylor
    _ = 1 + beta ^ 2 / 4 := hPolyIntegral

/-- Refine the genuine original one-link partition at beta<=1 without
a fictitious Gaussian SU(2) law or modified Wilson factor. -/
theorem p4Q2PZ37AKS_originalSingleLinkPartition_le_quarterGaussian
    (beta : ℝ) (hbeta : 0 ≤ beta) (hOne : beta ≤ 1) :
    zK beta ≤ Real.exp (-beta + beta ^ 2 / 4) := by
  have hMGF := p4Q2PZ37AKS_originalSingleLinkCharacter_mgf_le_quarter
    beta hbeta hOne
  have hTangent := Real.add_one_le_exp (beta ^ 2 / 4)
  calc
    zK beta = Real.exp (-beta) * ProbabilityTheory.mgf chiK nuK beta :=
      p4Q2PZ37AIQ_originalSingleLinkPartition_characterMGF beta
    _ ≤ Real.exp (-beta) * (1 + beta ^ 2 / 4) :=
      mul_le_mul_of_nonneg_left hMGF (Real.exp_pos _).le
    _ ≤ Real.exp (-beta) * Real.exp (beta ^ 2 / 4) :=
      mul_le_mul_of_nonneg_left (by linarith only [hTangent]) (Real.exp_pos _).le
    _ = Real.exp (-beta + beta ^ 2 / 4) :=
      (Real.exp_add _ _).symm

/-- The ACTUAL original crossing partition is a finite product of the
single-link Haar factor, as already proved in AIF/AIP. -/
theorem p4Q2PZ37AKS_originalCrossingPartition_le_quarterGaussian
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta) (hOne : beta ≤ 1) :
    p4Q2PZ37AIF_originalCrossingPartition H beta ≤
      Real.exp (p4Q2PZ37AFZ_plaquetteCount H * (-beta + beta ^ 2 / 4)) := by
  let nH := Nat.card (PeriodicHypercubicEvenSpatialSliceLink H)
  have hPow := pow_le_pow_left₀
    (p4Q2PZ37AIF_originalSingleLinkPartition_pos beta).le
    (p4Q2PZ37AKS_originalSingleLinkPartition_le_quarterGaussian
      beta hbeta hOne) nH
  have hExp :
      Real.exp (-beta + beta ^ 2 / 4) ^ nH =
      Real.exp (p4Q2PZ37AFZ_plaquetteCount H * (-beta + beta ^ 2 / 4)) := by
    rw [← Real.exp_nat_mul, p4Q2PZ37AIP_originalLinkCount_eq_plaquettes H]
  rw [hExp] at hPow
  simpa only [p4Q2PZ37AIF_originalCrossingPartition, Fintype.card_eq_nat_card]
    using hPow

/-- An exact rational inequality at the genuine fixed beta0 and p14,
using existing AKO rational bounds. This does NOT estimate Haar mass. -/
theorem p4Q2PZ37AKS_originalH14_fixedCoupling_quarterBudget_le_logFour :
    beta0 ^ 2 * (81000 : ℝ) / 4 ≤ Real.log 4 := by
  have hb : beta0 ≤ (1 / 156 : ℝ) :=
    p4Q2PZ37AKO_originalFixedCoupling_le_oneOver156
  have hbSq := pow_le_pow_left₀ p4Q2PZ37ADC_fixedCoupling_pos.le hb 2
  have hFloor : (11 / 8 : ℝ) ≤ Real.log 4 :=
    p4Q2PZ37AKO_elevenEighths_le_log_four
  nlinarith only [hbSq, hFloor]

local notation "Cfg14" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration 14 2
local notation "mu14" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure 14 2
local notation "p14" => p4Q2PZ37AFZ_plaquetteCount 14
local notation "Z14" => p4Q2PZ37AIF_originalCrossingPartition 14
local notation "u14" => p4Q2PZ37AIW_originalNormalizedSourceTransfer
  14 beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "m14" => p4Q2PZ37AIW_originalNormalizedNegativeMargin
  14 beta0 p4Q2PZ37ADC_fixedCoupling_pos.le
local notation "E14" => (fun A : Cfg14 => u14 A < -(m14))

local instance p4Q2PZ37AKS_h14Probability : IsProbabilityMeasure mu14 := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- H14 meets AKQ's genuine original PARTITION-Haar test even with the
coarse but TRUE probability upper bound r14<=1: the improvement comes
from the exact SU(2) character second moment, not a new Haar mass. -/
theorem p4Q2PZ37AKS_originalH14_partitionHaarMass_unconditional :
    Measure.real mu14 E14 * Z14 beta0 ≤
      4 * Real.exp (-(beta0 * p14)) := by
  have hOne : beta0 ≤ (1 : ℝ) := by
    have h := p4Q2PZ37AKO_originalFixedCoupling_le_oneOver156
    linarith only [h]
  have hp : (p14 : ℝ) = 81000 := by
    rw [p4Q2PZ37AIB_plaquetteCount_exact]
    norm_num
  have hQuarter : beta0 ^ 2 * p14 / 4 ≤ Real.log 4 := by
    simpa only [hp] using
      p4Q2PZ37AKS_originalH14_fixedCoupling_quarterBudget_le_logFour
  have hExpFour : Real.exp (beta0 ^ 2 * p14 / 4) ≤ 4 := by
    calc
      _ ≤ Real.exp (Real.log 4) := Real.exp_le_exp.mpr hQuarter
      _ = 4 := Real.exp_log (by norm_num)
  have hZ :
      Z14 beta0 ≤ Real.exp (-(beta0 * p14)) *
        Real.exp (beta0 ^ 2 * p14 / 4) := by
    calc
      _ ≤ Real.exp (p14 * (-beta0 + beta0 ^ 2 / 4)) :=
        p4Q2PZ37AKS_originalCrossingPartition_le_quarterGaussian 14
          beta0 p4Q2PZ37ADC_fixedCoupling_pos.le hOne
      _ = Real.exp (-(beta0 * p14)) * Real.exp (beta0 ^ 2 * p14 / 4) := by
        rw [← Real.exp_add]
        congr 1
        ring
  have hr : Measure.real mu14 E14 ≤ (1 : ℝ) := measureReal_le_one
  have hZpos : 0 ≤ Z14 beta0 :=
    (p4Q2PZ37AIF_originalCrossingPartition_pos 14 beta0).le
  calc
    Measure.real mu14 E14 * Z14 beta0 ≤ 1 * Z14 beta0 :=
      mul_le_mul_of_nonneg_right hr hZpos
    _ = Z14 beta0 := one_mul _
    _ ≤ Real.exp (-(beta0 * p14)) * Real.exp (beta0 ^ 2 * p14 / 4) := hZ
    _ ≤ Real.exp (-(beta0 * p14)) * 4 :=
      mul_le_mul_of_nonneg_left hExpFour (Real.exp_pos _).le
    _ = 4 * Real.exp (-(beta0 * p14)) := by ring

/-- Unconditional exclusion of the original fixed-beta0 H14 AJA
strict finite-power witness, with ALL original physics unchanged. -/
theorem p4Q2PZ37AKS_originalH14_no_AJA_finitePower_witness :
    ¬ ∃ n : ℕ,
      ‖((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          14 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le) ^ n)
        (p4Q2PZ37ZW_originalCenteredPhysicalDirection 14)‖ ^ 2 <
      (m14) ^ 2 * Measure.real mu14 E14 := by
  exact p4Q2PZ37AKQ_original_no_AJA_witness_of_partitionHaarMass
    14 beta0 p4Q2PZ37ADC_fixedCoupling_pos
    p4Q2PZ37AKS_originalH14_partitionHaarMass_unconditional

/-- Combine the existing AKO theorem for H<=13 with the new AKS
H14 step, with no change to the strict original AJA witness. -/
theorem p4Q2PZ37AKS_originalFixedCoupling_le_fourteen_no_AJA_power_witness
    (H : ℕ) (hH : H ≤ 14) :
    ¬ ∃ n : ℕ,
      ‖((periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator
          H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le) ^ n)
        (p4Q2PZ37ZW_originalCenteredPhysicalDirection H)‖ ^ 2 <
      (p4Q2PZ37AIW_originalNormalizedNegativeMargin H beta0
        p4Q2PZ37ADC_fixedCoupling_pos.le) ^ 2 *
      Measure.real (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)
        {A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 |
          p4Q2PZ37AIW_originalNormalizedSourceTransfer H beta0
            p4Q2PZ37ADC_fixedCoupling_pos.le A <
            -(p4Q2PZ37AIW_originalNormalizedNegativeMargin H beta0
              p4Q2PZ37ADC_fixedCoupling_pos.le)} := by
  by_cases h13 : H ≤ 13
  · exact p4Q2PZ37AKO_originalFixedCoupling_le_thirteen_no_AJA_power_witness
      H h13
  · have hEq : H = 14 := by omega
    subst H
    exact p4Q2PZ37AKS_originalH14_no_AJA_finitePower_witness

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.real_exp_le_one_add_sq_of_abs_le_one_aks
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKS_originalSingleLinkCharacter_secondMoment
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKS_originalSingleLinkCharacter_mgf_le_quarter
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKS_originalSingleLinkPartition_le_quarterGaussian
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKS_originalCrossingPartition_le_quarterGaussian
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKS_originalH14_fixedCoupling_quarterBudget_le_logFour
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKS_originalH14_partitionHaarMass_unconditional
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKS_originalH14_no_AJA_finitePower_witness
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKS_originalFixedCoupling_le_fourteen_no_AJA_power_witness
