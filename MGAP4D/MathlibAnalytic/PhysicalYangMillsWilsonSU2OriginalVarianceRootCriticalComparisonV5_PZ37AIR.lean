import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalHoeffdingHalfHaarComparisonCeilingV5_PZ37AIQ
import Mathlib.Data.Real.Sqrt
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AIR — genuine variance endpoint and the exact comparison threshold

Retain the ORIGINAL complete SU(2) Wilson action, both spatial halfweights,
signed ZW physical L2 source and continuous representative, genuine normalized
product Haar, AIG's original epsilon and strict full-margin negative region,
and every previous assumption, definition, and certified result.

The SAME original one-link character chi=1-E has mean zero and actual Haar
second moment 1/4. On |beta|<=1, integrating the pinned exponential remainder
gives M(beta)<=1+beta^2/4. For 0<beta<=1 this implies the STRICT bound
M(beta)<exp(beta^2/4), hence F_H(beta)<exp(p_H*(2*beta+beta^2)/4), where
F_H is exactly AIO's original partition/margin-comparison factor.

The NEW explicit endpoint r_H=sqrt(1+4*lambda_H)-1, lambda_H=log(2)/p_H,
satisfies r_H^2+2*r_H=4*lambda_H and r_H<2*lambda_H<=1/12.
Therefore the old full-margin negative region has genuine Haar mass >=1/2
for 0<beta<=r_H, INCLUDING r_H, and AIQ's old rational endpoint q_H<r_H.

The actual centered MGF is continuous and nondecreasing for beta>=0. Genuine
Haar positivity at the original identity proves M(beta)>1 for beta>0. Thus
F_H is continuous, strictly increasing on nonnegative couplings, and has a
UNIQUE nonnegative root theta_H of F_H(theta_H)=2, with
  q_H < r_H < theta_H < 2*lambda_H.
For beta>=0, F_H(beta)<2 iff beta<theta_H. For beta>0 the unchanged identity
2*epsilon=F_H*delta gives the exact three-way comparison of the old amplitudes.

theta_H is an implicit threshold of THIS sufficient comparison, not a
physical critical coupling or the maximal physical half-Haar interval.
At theta_H the current floor proves only a non-strict amplitude comparison.
No physical failure at/beyond theta_H, arbitrary-positive-coupling full-margin
half-Haar statement, volume-uniform positive amplitude/coercivity, Hamiltonian
spectral gap, or continuum Yang-Mills mass gap is asserted.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AIR_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AIR_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AIR_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AIR_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AIR_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

local notation "nu" => normalizedCompactHaar G
local notation "z" => p4Q2PZ37AIF_originalSingleLinkPartition
local notation "chi" => p4Q2PZ35C_originalOneLinkCharacter

local instance p4Q2PZ37AIR_singleLinkProbability : IsProbabilityMeasure nu :=
  normalizedCompactHaar_isProbabilityMeasure G

/-- Continuity of the actual original-character MGF uses the all-real
integrability already proved by AIQ for the SAME Haar and character. -/
theorem p4Q2PZ37AIR_originalCharacterMGF_continuous :
    Continuous (ProbabilityTheory.mgf chi nu) :=
  ProbabilityTheory.continuous_mgf
    (fun beta =>
      p4Q2PZ37AIQ_originalSingleLinkCharacter_subgaussian.integrable_exp_mul beta)

/-- At nonnegative coupling the exponential increment dominates its
unweighted linear increment, for either sign of the original variable. -/
theorem p4Q2PZ37AIR_real_exp_increment_lower
    (a b x : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
    Real.exp (a * x) + (b - a) * x ≤ Real.exp (b * x) := by
  have hSlope : x ≤ x * Real.exp (a * x) := by
    by_cases hx : 0 ≤ x
    · have hExp : (1 : ℝ) ≤ Real.exp (a * x) :=
        Real.one_le_exp_iff.mpr (mul_nonneg ha hx)
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hExp hx
    · have hx' : x ≤ 0 := (lt_of_not_ge hx).le
      have hExp : Real.exp (a * x) ≤ (1 : ℝ) :=
        Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos ha hx')
      simpa only [mul_one] using mul_le_mul_of_nonpos_left hExp hx'
  have hExp := mul_le_mul_of_nonneg_left
    (Real.add_one_le_exp ((b - a) * x)) (Real.exp_pos (a * x)).le
  have hProduct : Real.exp (a * x) * Real.exp ((b - a) * x) =
      Real.exp (b * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hProduct] at hExp
  have hScaled := mul_le_mul_of_nonneg_left hSlope (sub_nonneg.mpr hab)
  nlinarith only [hExp, hScaled]

/-- The centered original-character MGF is nondecreasing on nonnegative
couplings. Both signs of chi are retained; its original Haar mean is zero. -/
theorem p4Q2PZ37AIR_originalCharacterMGF_monotoneOn :
    MonotoneOn (ProbabilityTheory.mgf chi nu) (Set.Ici 0) := by
  intro a ha b _ hab
  have hChi : Integrable chi nu :=
    p4Q2PZ37AIQ_originalSingleLinkCharacter_continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have haInt :=
    p4Q2PZ37AIQ_originalSingleLinkCharacter_subgaussian.integrable_exp_mul a
  have hbInt :=
    p4Q2PZ37AIQ_originalSingleLinkCharacter_subgaussian.integrable_exp_mul b
  have hIntegral := integral_mono (haInt.add (hChi.const_mul (b - a))) hbInt
    (fun g : G => p4Q2PZ37AIR_real_exp_increment_lower a b (chi g) ha hab)
  rw [integral_add' haInt (hChi.const_mul (b - a)), integral_const_mul (b - a) chi,
    p4Q2PZ37AIQ_originalSingleLinkCharacter_mean_zero, mul_zero, add_zero] at hIntegral
  exact hIntegral

local instance p4Q2PZ37AIR_singleLinkHaar : Measure.IsHaarMeasure nu := by
  dsimp [normalizedCompactHaar]
  infer_instance

/-- The same original normalized character has value one at the group identity. -/
theorem p4Q2PZ37AIR_originalCharacter_one : chi (1 : G) = 1 := by
  change (1 : ℝ) - specialUnitaryWilsonPlaquetteEnergy 2 (1 : G) = 1
  rw [specialUnitaryWilsonPlaquetteEnergy_one 2 (by norm_num), sub_zero]

/-- Strict Jensen separation at every positive coupling. Genuine Haar has
positive mass on open sets; continuity and the actual identity value provide
strictness, without replacing the measure or assuming a variance condition. -/
theorem p4Q2PZ37AIR_originalCharacterMGF_gt_one
    (beta : ℝ) (hbeta : 0 < beta) :
    1 < ProbabilityTheory.mgf chi nu beta := by
  have hChi := p4Q2PZ37AIQ_originalSingleLinkCharacter_continuous
  have hInt : Integrable chi nu :=
    hChi.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hLinear : Integrable (fun g : G => beta * chi g + 1) nu :=
    (hInt.const_mul beta).add (integrable_const (μ := nu) (1 : ℝ))
  have hMean : (∫ g : G, beta * chi g + 1 ∂nu) = 1 := by
    rw [integral_add (hInt.const_mul beta) (integrable_const (μ := nu) (1 : ℝ)),
      integral_const_mul, p4Q2PZ37AIQ_originalSingleLinkCharacter_mean_zero]
    simp only [integral_const, probReal_univ, one_smul, mul_zero, zero_add]
  have hCont : Continuous
      (fun g : G => Real.exp (beta * chi g) - (beta * chi g + 1)) :=
    (Real.continuous_exp.comp (continuous_const.mul hChi)).sub
      ((continuous_const.mul hChi).add continuous_const)
  have hNonneg : 0 ≤
      (fun g : G => Real.exp (beta * chi g) - (beta * chi g + 1)) := by
    intro g
    exact sub_nonneg.mpr (Real.add_one_le_exp (beta * chi g))
  have hAtOne :
      Real.exp (beta * chi (1 : G)) - (beta * chi (1 : G) + 1) ≠ 0 := by
    rw [p4Q2PZ37AIR_originalCharacter_one, mul_one]
    exact ne_of_gt (sub_pos.mpr (Real.add_one_lt_exp (ne_of_gt hbeta)))
  have hPositive := hCont.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (μ := nu) (x := (1 : G)) (HasCompactSupport.of_compactSpace _) hNonneg hAtOne
  rw [integral_sub
    (p4Q2PZ37AIQ_originalSingleLinkCharacter_subgaussian.integrable_exp_mul beta)
    hLinear, hMean] at hPositive
  change 1 < ∫ g : G, Real.exp (beta * chi g) ∂nu
  linarith only [hPositive]

/-- A centered real function bounded by one on a probability space satisfies
the integrated exponential-remainder bound on |beta|<=1.  The second moment
is retained explicitly; no topology or concrete physical configuration enters
this general probability lemma. -/
theorem p4Q2PZ37AIR_boundedCenteredVariance_integral_le
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (X : α → ℝ) (beta : ℝ) (hSmall : |beta| ≤ 1)
    (hBound : ∀ x : α, |X x| ≤ 1)
    (hInt : Integrable X μ)
    (hSquareInt : Integrable (fun x : α => (X x) ^ 2) μ)
    (hExpInt : Integrable (fun x : α => Real.exp (beta * X x)) μ)
    (hMean : (∫ x : α, X x ∂μ) = 0) :
    (∫ x : α, Real.exp (beta * X x) ∂μ) ≤
      1 + beta ^ 2 * (∫ x : α, (X x) ^ 2 ∂μ) := by
  have hScalar (t : ℝ) (ht : |t| ≤ 1) :
      Real.exp (beta * t) ≤ 1 + beta * t + beta ^ 2 * t ^ 2 := by
    have hArg : |beta * t| ≤ 1 := by
      calc
        |beta * t| = |beta| * |t| := abs_mul beta t
        _ ≤ 1 * 1 := mul_le_mul hSmall ht (abs_nonneg t) (by norm_num)
        _ = 1 := one_mul 1
    have hRemainder : Real.exp (beta * t) - 1 - beta * t ≤ (beta * t) ^ 2 :=
      (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hArg)).2
    calc
      Real.exp (beta * t) ≤ 1 + beta * t + (beta * t) ^ 2 := by
        linarith only [hRemainder]
      _ = 1 + beta * t + beta ^ 2 * t ^ 2 := by ring
  have hPoint (x : α) : Real.exp (beta * X x) ≤
      1 + beta * X x + beta ^ 2 * (X x) ^ 2 :=
    hScalar (X x) (hBound x)
  have hOneInt : Integrable (fun _ : α => (1 : ℝ)) μ :=
    integrable_const (μ := μ) (1 : ℝ)
  have hFirstInt : Integrable (fun x : α => beta * X x) μ :=
    hInt.const_mul beta
  have hSecondInt : Integrable (fun x : α => beta ^ 2 * (X x) ^ 2) μ :=
    hSquareInt.const_mul (beta ^ 2)
  have hLinearInt : Integrable (fun x : α => (1 : ℝ) + beta * X x) μ :=
    hOneInt.add hFirstInt
  have hOne : (∫ _ : α, (1 : ℝ) ∂μ) = 1 := by
    simp only [integral_const, probReal_univ, one_smul]
  have hFirst : (∫ x : α, beta * X x ∂μ) = 0 := by
    calc
      (∫ x : α, beta * X x ∂μ) = beta * (∫ x : α, X x ∂μ) :=
        integral_const_mul (μ := μ) beta X
      _ = beta * 0 := congrArg (fun t : ℝ => beta * t) hMean
      _ = 0 := mul_zero beta
  have hSecond : (∫ x : α, beta ^ 2 * (X x) ^ 2 ∂μ) =
      beta ^ 2 * (∫ x : α, (X x) ^ 2 ∂μ) :=
    integral_const_mul (μ := μ) (beta ^ 2) (fun x : α => (X x) ^ 2)
  have hSum : (∫ x : α, 1 + beta * X x + beta ^ 2 * (X x) ^ 2 ∂μ) =
      1 + beta ^ 2 * (∫ x : α, (X x) ^ 2 ∂μ) := by
    calc
      (∫ x : α, 1 + beta * X x + beta ^ 2 * (X x) ^ 2 ∂μ) =
          (∫ x : α, 1 + beta * X x ∂μ) +
            (∫ x : α, beta ^ 2 * (X x) ^ 2 ∂μ) :=
        integral_add (μ := μ)
          (f := fun x : α => (1 : ℝ) + beta * X x)
          (g := fun x : α => beta ^ 2 * (X x) ^ 2) hLinearInt hSecondInt
      _ = ((∫ _ : α, (1 : ℝ) ∂μ) + (∫ x : α, beta * X x ∂μ)) +
          (∫ x : α, beta ^ 2 * (X x) ^ 2 ∂μ) :=
        congrArg (fun t : ℝ => t + (∫ x : α, beta ^ 2 * (X x) ^ 2 ∂μ))
          (integral_add (μ := μ)
            (f := fun _ : α => (1 : ℝ))
            (g := fun x : α => beta * X x) hOneInt hFirstInt)
      _ = 1 + beta ^ 2 * (∫ x : α, (X x) ^ 2 ∂μ) := by
        rw [hOne, hFirst, hSecond, add_zero]
  calc
    (∫ x : α, Real.exp (beta * X x) ∂μ) ≤
        ∫ x : α, 1 + beta * X x + beta ^ 2 * (X x) ^ 2 ∂μ :=
      integral_mono (μ := μ)
        (f := fun x : α => Real.exp (beta * X x))
        (g := fun x : α => 1 + beta * X x + beta ^ 2 * (X x) ^ 2)
        hExpInt (hLinearInt.add hSecondInt) hPoint
    _ = 1 + beta ^ 2 * (∫ x : α, (X x) ^ 2 ∂μ) := hSum

/-- The actual SU(2) Haar variance is 1/4.  Apply the general integrated
remainder bound to the unchanged original character and genuine Haar; the
mean-zero, range and actual second-moment facts are supplied by existing APIs. -/
theorem p4Q2PZ37AIR_originalCharacterMGF_le_varianceQuadratic
    (beta : ℝ) (hSmall : |beta| ≤ 1) :
    ProbabilityTheory.mgf chi nu beta ≤ 1 + beta ^ 2 / 4 := by
  have hChi : Continuous chi :=
    p4Q2PZ37AIQ_originalSingleLinkCharacter_continuous
  have hInt : Integrable chi nu :=
    hChi.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hSquareInt : Integrable (fun g : G => (chi g) ^ 2) nu :=
    (hChi.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  calc
    ProbabilityTheory.mgf chi nu beta =
        ∫ g : G, Real.exp (beta * chi g) ∂nu := rfl
    _ ≤ 1 + beta ^ 2 * (∫ g : G, (chi g) ^ 2 ∂nu) :=
      p4Q2PZ37AIR_boundedCenteredVariance_integral_le (α := G) nu chi beta hSmall
        (fun g : G =>
          abs_le.mpr (p4Q2PZ37AIQ_originalSingleLinkCharacter_mem_interval g))
        hInt hSquareInt
        (p4Q2PZ37AIQ_originalSingleLinkCharacter_subgaussian.integrable_exp_mul beta)
        p4Q2PZ37AIQ_originalSingleLinkCharacter_mean_zero
    _ = 1 + beta ^ 2 * (1 / 4 : ℝ) :=
      congrArg (fun t : ℝ => 1 + beta ^ 2 * t)
        p4Q2PZ37ABN_originalTemporalCharacter_haar_secondMoment
    _ = 1 + beta ^ 2 / 4 := by ring

/-- Strict exponential improvement on 0<beta<=1. Strictness comes from
the proved positive scalar beta^2/4 in 1+x<exp(x), so a later non-strict
coupling budget can still produce a strict original margin comparison. -/
theorem p4Q2PZ37AIR_originalCharacterMGF_lt_varianceGaussian
    (beta : ℝ) (hbeta : 0 < beta) (hSmall : beta ≤ 1) :
    ProbabilityTheory.mgf chi nu beta < Real.exp (beta ^ 2 / 4) := by
  have hAbs : |beta| ≤ 1 := by rwa [abs_of_pos hbeta]
  have hArg : 0 < beta ^ 2 / 4 := div_pos (pow_pos hbeta 2) (by norm_num)
  have hStrict : 1 + beta ^ 2 / 4 < Real.exp (beta ^ 2 / 4) := by
    simpa only [add_comm] using Real.add_one_lt_exp (ne_of_gt hArg)
  exact (p4Q2PZ37AIR_originalCharacterMGF_le_varianceQuadratic beta hAbs).trans_lt hStrict

variable (H : ℕ)
local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "nH" => Nat.card Link
local notation "Cfg" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muH" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "pH" => p4Q2PZ37AFZ_plaquetteCount H
local notation "fCont" => p4Q2PZ37AFZ_originalCenteredContinuous H
local notation "Zcross" => p4Q2PZ37AIF_originalCrossingPartition H
local notation "margin" => p4Q2PZ37AIG_originalNegativeTransferMargin H
local notation "Region" => p4Q2PZ37AIG_originalNegativeTransferRegion H
local notation "delta" => p4Q2PZ37AIO_sourceNonpositiveVarianceFloor H
local notation "lambdaH" => p4Q2PZ37AIP_closedHalfHaarCouplingCutoff H
local notation "qH" => p4Q2PZ37AIQ_rationalHalfHaarCouplingCutoff H
local notation "M" => ProbabilityTheory.mgf chi nu

local instance p4Q2PZ37AIR_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- An explicit name for AIO's SAME original comparison factor. This is
not a new physical partition, source, transfer, or measure. -/
def p4Q2PZ37AIR_originalMarginComparisonFactor (beta : ℝ) : ℝ :=
  Zcross beta * Real.exp (3 * beta * pH / 2)

local notation "F" => p4Q2PZ37AIR_originalMarginComparisonFactor H

theorem p4Q2PZ37AIR_originalMarginFactor_characterMGF (beta : ℝ) :
    F beta = Real.exp (beta * pH / 2) * (M beta) ^ nH := by
  unfold p4Q2PZ37AIR_originalMarginComparisonFactor
  change (z beta) ^ Fintype.card Link * Real.exp (3 * beta * pH / 2) = _
  rw [Fintype.card_eq_nat_card,
    p4Q2PZ37AIQ_originalSingleLinkPartition_characterMGF beta, mul_pow]
  have hExp : Real.exp (-beta) ^ nH * Real.exp (3 * beta * pH / 2) =
      Real.exp (beta * pH / 2) := by
    rw [← Real.exp_nat_mul, p4Q2PZ37AIP_originalLinkCount_eq_plaquettes H,
      ← Real.exp_add]
    congr 1
    ring
  calc
    _ = (Real.exp (-beta) ^ nH * Real.exp (3 * beta * pH / 2)) * (M beta) ^ nH := by
      ring
    _ = _ := by rw [hExp]

theorem p4Q2PZ37AIR_originalMarginFactor_continuous : Continuous F := by
  change Continuous (fun beta : ℝ => F beta)
  simp_rw [p4Q2PZ37AIR_originalMarginFactor_characterMGF H]
  have hArg : Continuous (fun beta : ℝ => beta * pH / 2) :=
    (continuous_id.mul continuous_const).div_const (2 : ℝ)
  have hExp : Continuous (fun beta : ℝ => Real.exp (beta * pH / 2)) :=
    Real.continuous_exp.comp hArg
  exact hExp.mul (p4Q2PZ37AIR_originalCharacterMGF_continuous.pow nH)

/-- Strict increase is restricted to nonnegative couplings. The centered
MGF is nondecreasing and the positive exponential factor strictly increases. -/
theorem p4Q2PZ37AIR_originalMarginFactor_strictMonoOn :
    StrictMonoOn F (Set.Ici 0) := by
  intro a ha b hb hab
  rw [p4Q2PZ37AIR_originalMarginFactor_characterMGF H a,
    p4Q2PZ37AIR_originalMarginFactor_characterMGF H b]
  have hMa : 0 < M a := lt_of_lt_of_le (by norm_num)
    (p4Q2PZ37AIQ_originalSingleLinkCharacter_MGF_ge_one a)
  have hMGF : M a ≤ M b := p4Q2PZ37AIR_originalCharacterMGF_monotoneOn ha hb hab.le
  have hArg : a * pH / 2 < b * pH / 2 := by
    have hMul := mul_lt_mul_of_pos_right hab (p4Q2PZ37AHN_count_pos H)
    linarith only [hMul]
  calc
    _ < Real.exp (b * pH / 2) * (M a) ^ nH :=
      mul_lt_mul_of_pos_right (Real.exp_lt_exp.mpr hArg) (pow_pos hMa nH)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hMa.le hMGF nH) (Real.exp_pos _).le

/-- Genuine nontrivial Haar fluctuations make AIQ's exponential lower
bound STRICT at positive coupling. -/
theorem p4Q2PZ37AIR_originalMarginFactor_gt_expHalf
    (beta : ℝ) (hbeta : 0 < beta) :
    Real.exp (beta * pH / 2) < F beta := by
  have hPow : (1 : ℝ) < (M beta) ^ nH := by
    simpa only [one_pow] using pow_lt_pow_left₀
      (p4Q2PZ37AIR_originalCharacterMGF_gt_one beta hbeta)
      (by norm_num : (0 : ℝ) ≤ 1)
      (ne_of_gt (p4Q2PZ37AIP_originalLinkCount_pos H))
  rw [p4Q2PZ37AIR_originalMarginFactor_characterMGF H beta]
  simpa only [mul_one] using mul_lt_mul_of_pos_left hPow (Real.exp_pos _)

/-- Strict improvement from the actual one-link Haar variance 1/4.
The scalar restriction beta<=1 is explicit and later proved at the cutoff. -/
theorem p4Q2PZ37AIR_originalMarginFactor_lt_varianceGaussian
    (beta : ℝ) (hbeta : 0 < beta) (hSmall : beta ≤ 1) :
    F beta < Real.exp (pH * (2 * beta + beta ^ 2) / 4) := by
  have hMpos : 0 < M beta := lt_of_lt_of_le (by norm_num)
    (p4Q2PZ37AIQ_originalSingleLinkCharacter_MGF_ge_one beta)
  have hPow := pow_lt_pow_left₀
    (p4Q2PZ37AIR_originalCharacterMGF_lt_varianceGaussian beta hbeta hSmall)
    hMpos.le (ne_of_gt (p4Q2PZ37AIP_originalLinkCount_pos H))
  calc
    F beta = Real.exp (beta * pH / 2) * (M beta) ^ nH :=
      p4Q2PZ37AIR_originalMarginFactor_characterMGF H beta
    _ < Real.exp (beta * pH / 2) * Real.exp (beta ^ 2 / 4) ^ nH :=
      mul_lt_mul_of_pos_left hPow (Real.exp_pos _)
    _ = _ := by
      rw [← Real.exp_nat_mul, p4Q2PZ37AIP_originalLinkCount_eq_plaquettes H,
        ← Real.exp_add]
      congr 1
      ring

theorem p4Q2PZ37AIR_originalPartitionCondition_of_varianceBudget
    (beta : ℝ) (hbeta : 0 < beta) (hSmall : beta ≤ 1)
    (hBudget : pH * (2 * beta + beta ^ 2) / 4 ≤ Real.log 2) : F beta < 2 := by
  calc
    _ < Real.exp (pH * (2 * beta + beta ^ 2) / 4) :=
      p4Q2PZ37AIR_originalMarginFactor_lt_varianceGaussian H beta hbeta hSmall
    _ ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr hBudget
    _ = 2 := Real.exp_log (by norm_num)

/-- Integral-free INCLUDED endpoint from the genuine-variance quadratic
budget. The old AIG margin and all previous cutoff definitions are retained. -/
def p4Q2PZ37AIR_varianceRootCouplingCutoff : ℝ :=
  Real.sqrt (1 + 4 * lambdaH) - 1

local notation "rH" => p4Q2PZ37AIR_varianceRootCouplingCutoff H

theorem p4Q2PZ37AIR_varianceRootCouplingCutoff_pos : 0 < rH := by
  have hLambda := p4Q2PZ37AIP_closedHalfHaarCouplingCutoff_pos H
  have hRoot : (1 : ℝ) < Real.sqrt (1 + 4 * lambdaH) := by
    simpa only [Real.sqrt_one] using
      Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)
        (show (1 : ℝ) < 1 + 4 * lambdaH by linarith only [hLambda])
  change 0 < Real.sqrt (1 + 4 * lambdaH) - 1
  linarith only [hRoot]

theorem p4Q2PZ37AIR_varianceRoot_quadratic_identity :
    rH ^ 2 + 2 * rH = 4 * lambdaH := by
  have hLambda := p4Q2PZ37AIP_closedHalfHaarCouplingCutoff_pos H
  have hSq := Real.sq_sqrt (show (0 : ℝ) ≤ 1 + 4 * lambdaH by positivity)
  unfold p4Q2PZ37AIR_varianceRootCouplingCutoff
  nlinarith only [hSq]

theorem p4Q2PZ37AIR_varianceRoot_lt_twice_previous : rH < 2 * lambdaH := by
  have hEq := p4Q2PZ37AIR_varianceRoot_quadratic_identity H
  have hSq : 0 < rH ^ 2 := sq_pos_of_pos (p4Q2PZ37AIR_varianceRootCouplingCutoff_pos H)
  nlinarith only [hEq, hSq]

theorem p4Q2PZ37AIR_varianceRoot_lt_oneDivTwelve : rH < (1 / 12 : ℝ) := by
  have hRoot := p4Q2PZ37AIR_varianceRoot_lt_twice_previous H
  have hLambda := p4Q2PZ37AIP_closedCutoff_le_oneDiv24 H
  linarith only [hRoot, hLambda]

/-- A genuine extension of AIQ's already certified rational endpoint. -/
theorem p4Q2PZ37AIR_previousRational_lt_varianceRoot : qH < rH := by
  have hq := p4Q2PZ37AIQ_rationalHalfHaarCouplingCutoff_pos H
  have hr := p4Q2PZ37AIR_varianceRootCouplingCutoff_pos H
  have hp := p4Q2PZ37AHN_count_pos H
  have hCount := p4Q2PZ37AIQ_originalCount_mul_previousCutoff H
  have hBudget := p4Q2PZ37AIQ_quadraticBudget_of_le_rationalCutoff H qH hq le_rfl
  have hqBudget : qH ^ 2 + qH < 2 * lambdaH := by
    by_contra hNot
    have hScaled := mul_le_mul_of_nonneg_left (le_of_not_gt hNot) hp.le
    nlinarith only [hScaled, hCount, hBudget]
  have hRootEq := p4Q2PZ37AIR_varianceRoot_quadratic_identity H
  by_contra hNot
  have hle : rH ≤ qH := le_of_not_gt hNot
  have hSquare : rH ^ 2 ≤ qH ^ 2 := pow_le_pow_left₀ hr.le hle 2
  nlinarith only [hSquare, hle, hRootEq, hqBudget, sq_nonneg qH]

theorem p4Q2PZ37AIR_varianceBudget_of_le_root
    (beta : ℝ) (hbeta : 0 < beta) (hSmall : beta ≤ rH) :
    pH * (2 * beta + beta ^ 2) / 4 ≤ Real.log 2 := by
  have hSquare : beta ^ 2 ≤ rH ^ 2 := pow_le_pow_left₀ hbeta.le hSmall 2
  have hRootEq := p4Q2PZ37AIR_varianceRoot_quadratic_identity H
  have hCount := p4Q2PZ37AIQ_originalCount_mul_previousCutoff H
  have hPoly : 2 * beta + beta ^ 2 ≤ 4 * lambdaH := by
    nlinarith only [hSquare, hSmall, hRootEq]
  have hScaled := mul_le_mul_of_nonneg_left hPoly (p4Q2PZ37AHN_count_pos H).le
  nlinarith only [hScaled, hCount]

theorem p4Q2PZ37AIR_originalPartitionCondition_of_le_root
    (beta : ℝ) (hbeta : 0 < beta) (hSmall : beta ≤ rH) : F beta < 2 := by
  have hCap := p4Q2PZ37AIR_varianceRoot_lt_oneDivTwelve H
  exact p4Q2PZ37AIR_originalPartitionCondition_of_varianceBudget H beta hbeta
    (by linarith only [hSmall, hCap])
    (p4Q2PZ37AIR_varianceBudget_of_le_root H beta hbeta hSmall)

theorem p4Q2PZ37AIR_originalFullNegativeRegion_realHaar_half_of_le_root
    (beta : ℝ) (hbeta : 0 < beta) (hSmall : beta ≤ rH) :
    (1 / 2 : ℝ) ≤ Measure.real muH (Region beta) :=
  p4Q2PZ37AIO_originalFullNegativeRegion_realHaar_half_of_partition H beta hbeta
    (p4Q2PZ37AIR_originalPartitionCondition_of_le_root H beta hbeta hSmall)

/-- The previous comparison ceiling lies STRICTLY above level two.
This assertion is about the comparison factor, not physical sign failure. -/
theorem p4Q2PZ37AIR_originalMarginFactor_at_ceiling_gt_two :
    2 < F (2 * lambdaH) := by
  have hPositive : 0 < 2 * lambdaH := mul_pos (by norm_num)
    (p4Q2PZ37AIP_closedHalfHaarCouplingCutoff_pos H)
  have hCount := p4Q2PZ37AIQ_originalCount_mul_previousCutoff H
  have hArg : (2 * lambdaH) * pH / 2 = Real.log 2 := by
    nlinarith only [hCount]
  have hStrict := p4Q2PZ37AIR_originalMarginFactor_gt_expHalf H (2 * lambdaH) hPositive
  rw [hArg, Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hStrict
  exact hStrict

/-- Existence for the actual original comparison factor, with strict
brackets proved from the genuine-variance bound and nontrivial Haar. -/
theorem p4Q2PZ37AIR_exists_criticalComparisonCoupling :
    ∃ beta : ℝ, rH < beta ∧ beta < 2 * lambdaH ∧ F beta = 2 := by
  have hLow := p4Q2PZ37AIR_originalPartitionCondition_of_le_root H rH
    (p4Q2PZ37AIR_varianceRootCouplingCutoff_pos H) le_rfl
  have hHigh := p4Q2PZ37AIR_originalMarginFactor_at_ceiling_gt_two H
  obtain ⟨beta, hInterval, hEq⟩ := intermediate_value_Icc
    (p4Q2PZ37AIR_varianceRoot_lt_twice_previous H).le
    (p4Q2PZ37AIR_originalMarginFactor_continuous H).continuousOn
    (show (2 : ℝ) ∈ Set.Icc (F rH) (F (2 * lambdaH)) from ⟨hLow.le, hHigh.le⟩)
  refine ⟨beta, ?_, ?_, hEq⟩
  · by_contra hNot
    have hEqual : beta = rH := le_antisymm (le_of_not_gt hNot) hInterval.1
    rw [hEqual] at hEq
    linarith only [hLow, hEq]
  · by_contra hNot
    have hEqual : beta = 2 * lambdaH := le_antisymm hInterval.2 (le_of_not_gt hNot)
    rw [hEqual] at hEq
    linarith only [hHigh, hEq]

/-- The UNIQUE nonnegative root of the SAME factor F=2. This implicit
quantity is a threshold of this comparison method, not a physical critical
coupling or an elementary closed-form evaluation of the Haar integral. -/
def p4Q2PZ37AIR_criticalComparisonCoupling : ℝ :=
  Classical.choose (p4Q2PZ37AIR_exists_criticalComparisonCoupling H)

local notation "thetaH" => p4Q2PZ37AIR_criticalComparisonCoupling H

theorem p4Q2PZ37AIR_criticalComparisonCoupling_spec :
    rH < thetaH ∧ thetaH < 2 * lambdaH ∧ F thetaH = 2 :=
  Classical.choose_spec (p4Q2PZ37AIR_exists_criticalComparisonCoupling H)

theorem p4Q2PZ37AIR_criticalComparisonCoupling_pos : 0 < thetaH :=
  lt_trans (p4Q2PZ37AIR_varianceRootCouplingCutoff_pos H)
    (p4Q2PZ37AIR_criticalComparisonCoupling_spec H).1

theorem p4Q2PZ37AIR_originalMarginFactor_eq_two_iff
    (beta : ℝ) (hbeta : 0 ≤ beta) : F beta = 2 ↔ beta = thetaH := by
  constructor
  · intro hEq
    exact (p4Q2PZ37AIR_originalMarginFactor_strictMonoOn H).injOn hbeta
      (p4Q2PZ37AIR_criticalComparisonCoupling_pos H).le
      (hEq.trans (p4Q2PZ37AIR_criticalComparisonCoupling_spec H).2.2.symm)
  · rintro rfl
    exact (p4Q2PZ37AIR_criticalComparisonCoupling_spec H).2.2

theorem p4Q2PZ37AIR_originalPartitionCondition_iff_below_critical
    (beta : ℝ) (hbeta : 0 ≤ beta) : F beta < 2 ↔ beta < thetaH := by
  have hTheta := (p4Q2PZ37AIR_criticalComparisonCoupling_pos H).le
  have hEq := (p4Q2PZ37AIR_criticalComparisonCoupling_spec H).2.2
  constructor
  · intro hF
    by_contra hNot
    have hMono := (p4Q2PZ37AIR_originalMarginFactor_strictMonoOn H).monotoneOn
      hTheta hbeta (le_of_not_gt hNot)
    rw [hEq] at hMono
    exact (not_lt_of_ge hMono) hF
  · intro hLt
    have hMono := p4Q2PZ37AIR_originalMarginFactor_strictMonoOn H hbeta hTheta hLt
    rwa [hEq] at hMono

theorem p4Q2PZ37AIR_originalMarginFactor_gt_two_iff
    (beta : ℝ) (hbeta : 0 ≤ beta) : 2 < F beta ↔ thetaH < beta := by
  have hTheta := (p4Q2PZ37AIR_criticalComparisonCoupling_pos H).le
  have hEq := (p4Q2PZ37AIR_criticalComparisonCoupling_spec H).2.2
  constructor
  · intro hF
    by_contra hNot
    have hMono := (p4Q2PZ37AIR_originalMarginFactor_strictMonoOn H).monotoneOn
      hbeta hTheta (le_of_not_gt hNot)
    rw [hEq] at hMono
    exact (not_lt_of_ge hMono) hF
  · intro hLt
    have hMono := p4Q2PZ37AIR_originalMarginFactor_strictMonoOn H hTheta hbeta hLt
    rwa [hEq] at hMono

/-- The original epsilon/delta comparison is characterized exactly for
positive beta. At beta=0 both amplitudes vanish, so positivity is essential. -/
theorem p4Q2PZ37AIR_originalNegativeMargin_lt_floor_iff
    (beta : ℝ) (hbeta : 0 < beta) : margin beta < delta beta ↔ beta < thetaH := by
  have hDelta := p4Q2PZ37AIO_sourceNonpositiveVarianceFloor_pos H beta hbeta
  have hIdentity : 2 * margin beta = F beta * delta beta :=
    p4Q2PZ37AIO_originalNegativeMargin_ratio_identity H beta
  constructor
  · intro hMargin
    apply (p4Q2PZ37AIR_originalPartitionCondition_iff_below_critical H beta hbeta.le).mp
    by_contra hNot
    have hScaled := mul_le_mul_of_nonneg_right (le_of_not_gt hNot) hDelta.le
    nlinarith only [hScaled, hIdentity, hMargin]
  · intro hBelow
    exact p4Q2PZ37AIO_originalNegativeMargin_lt_varianceFloor H beta hbeta
      ((p4Q2PZ37AIR_originalPartitionCondition_iff_below_critical H beta hbeta.le).mpr hBelow)

theorem p4Q2PZ37AIR_originalNegativeMargin_eq_floor_iff
    (beta : ℝ) (hbeta : 0 < beta) : margin beta = delta beta ↔ beta = thetaH := by
  have hDelta := p4Q2PZ37AIO_sourceNonpositiveVarianceFloor_pos H beta hbeta
  have hIdentity : 2 * margin beta = F beta * delta beta :=
    p4Q2PZ37AIO_originalNegativeMargin_ratio_identity H beta
  constructor
  · intro hMargin
    apply (p4Q2PZ37AIR_originalMarginFactor_eq_two_iff H beta hbeta.le).mp
    have hProduct : F beta * delta beta = 2 * delta beta := by
      rw [← hIdentity, hMargin]
    exact mul_right_cancel₀ (ne_of_gt hDelta) hProduct
  · rintro rfl
    rw [(p4Q2PZ37AIR_criticalComparisonCoupling_spec H).2.2] at hIdentity
    linarith only [hIdentity]

theorem p4Q2PZ37AIR_originalFloor_lt_negativeMargin_iff
    (beta : ℝ) (hbeta : 0 < beta) : delta beta < margin beta ↔ thetaH < beta := by
  have hDelta := p4Q2PZ37AIO_sourceNonpositiveVarianceFloor_pos H beta hbeta
  have hIdentity : 2 * margin beta = F beta * delta beta :=
    p4Q2PZ37AIO_originalNegativeMargin_ratio_identity H beta
  constructor
  · intro hMargin
    apply (p4Q2PZ37AIR_originalMarginFactor_gt_two_iff H beta hbeta.le).mp
    by_contra hNot
    have hScaled := mul_le_mul_of_nonneg_right (le_of_not_gt hNot) hDelta.le
    nlinarith only [hScaled, hIdentity, hMargin]
  · intro hAbove
    have hF := (p4Q2PZ37AIR_originalMarginFactor_gt_two_iff H beta hbeta.le).mpr hAbove
    have hScaled := mul_lt_mul_of_pos_right hF hDelta
    nlinarith only [hScaled, hIdentity]

theorem p4Q2PZ37AIR_originalSource_nonpos_subset_fullNegativeRegion
    (beta : ℝ) (hbeta : 0 < beta) (hBelow : beta < thetaH) :
    {B : Cfg | fCont B ≤ 0} ⊆ Region beta :=
  p4Q2PZ37AIO_originalSource_nonpos_subset_fullNegativeRegion H beta hbeta
    ((p4Q2PZ37AIR_originalPartitionCondition_iff_below_critical H beta hbeta.le).mpr hBelow)

theorem p4Q2PZ37AIR_originalFullNegativeRegion_Haar_half
    (beta : ℝ) (hbeta : 0 < beta) (hBelow : beta < thetaH) :
    (1 / 2 : ℝ≥0∞) ≤ muH (Region beta) :=
  p4Q2PZ37AIO_originalFullNegativeRegion_Haar_half_of_partition H beta hbeta
    ((p4Q2PZ37AIR_originalPartitionCondition_iff_below_critical H beta hbeta.le).mpr hBelow)

theorem p4Q2PZ37AIR_originalFullNegativeRegion_realHaar_half
    (beta : ℝ) (hbeta : 0 < beta) (hBelow : beta < thetaH) :
    (1 / 2 : ℝ) ≤ Measure.real muH (Region beta) :=
  p4Q2PZ37AIO_originalFullNegativeRegion_realHaar_half_of_partition H beta hbeta
    ((p4Q2PZ37AIR_originalPartitionCondition_iff_below_critical H beta hbeta.le).mpr hBelow)

theorem p4Q2PZ37AIR_expandedClosedEndpoint_certificate :
    qH < rH ∧ rH < thetaH ∧ thetaH < 2 * lambdaH ∧
      F rH < 2 ∧ (1 / 2 : ℝ) ≤ Measure.real muH (Region rH) :=
  ⟨p4Q2PZ37AIR_previousRational_lt_varianceRoot H,
    (p4Q2PZ37AIR_criticalComparisonCoupling_spec H).1,
    (p4Q2PZ37AIR_criticalComparisonCoupling_spec H).2.1,
    p4Q2PZ37AIR_originalPartitionCondition_of_le_root H rH
      (p4Q2PZ37AIR_varianceRootCouplingCutoff_pos H) le_rfl,
    p4Q2PZ37AIR_originalFullNegativeRegion_realHaar_half_of_le_root H rH
      (p4Q2PZ37AIR_varianceRootCouplingCutoff_pos H) le_rfl⟩

/-- Exact boundary of this sufficient comparison. Equality of the old
amplitudes does NOT establish failure of the actual strict negative region. -/
theorem p4Q2PZ37AIR_comparisonBoundary_certificate :
    F thetaH = 2 ∧ margin thetaH = delta thetaH ∧ ¬ F thetaH < 2 := by
  have hEq := (p4Q2PZ37AIR_criticalComparisonCoupling_spec H).2.2
  refine ⟨hEq, ?_, ?_⟩
  · exact (p4Q2PZ37AIR_originalNegativeMargin_eq_floor_iff H thetaH
      (p4Q2PZ37AIR_criticalComparisonCoupling_pos H)).mpr rfl
  · rw [hEq]
    exact lt_irrefl 2

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIR_originalCharacterMGF_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIR_real_exp_increment_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIR_originalCharacterMGF_monotoneOn
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIR_originalCharacter_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIR_originalCharacterMGF_gt_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIR_boundedCenteredVariance_integral_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIR_originalCharacterMGF_le_varianceQuadratic
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIR_originalCharacterMGF_lt_varianceGaussian
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIR_originalMarginComparisonFactor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIR_originalMarginFactor_characterMGF
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIR_originalMarginFactor_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIR_originalMarginFactor_strictMonoOn
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIR_originalMarginFactor_gt_expHalf
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIR_originalMarginFactor_lt_varianceGaussian
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIR_originalPartitionCondition_of_varianceBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIR_varianceRootCouplingCutoff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIR_varianceRootCouplingCutoff_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIR_varianceRoot_quadratic_identity
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIR_varianceRoot_lt_twice_previous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIR_varianceRoot_lt_oneDivTwelve
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIR_previousRational_lt_varianceRoot
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIR_varianceBudget_of_le_root
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIR_originalPartitionCondition_of_le_root
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIR_originalFullNegativeRegion_realHaar_half_of_le_root
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIR_originalMarginFactor_at_ceiling_gt_two
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIR_exists_criticalComparisonCoupling
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIR_criticalComparisonCoupling
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIR_criticalComparisonCoupling_spec
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIR_criticalComparisonCoupling_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIR_originalMarginFactor_eq_two_iff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIR_originalPartitionCondition_iff_below_critical
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIR_originalMarginFactor_gt_two_iff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIR_originalNegativeMargin_lt_floor_iff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIR_originalNegativeMargin_eq_floor_iff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIR_originalFloor_lt_negativeMargin_iff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIR_originalSource_nonpos_subset_fullNegativeRegion
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIR_originalFullNegativeRegion_Haar_half
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIR_originalFullNegativeRegion_realHaar_half
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIR_expandedClosedEndpoint_certificate
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIR_comparisonBoundary_certificate
