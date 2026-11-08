import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalStrictPartitionClosedHalfHaarV5_PZ37AIP
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AIQ — original Haar Hoeffding bounds and a comparison ceiling

Retain the ORIGINAL complete SU(2) Wilson action, both spatial halfweights,
signed ZW physical L2 source and continuous representative, genuine normalized
product Haar, AIG's original epsilon and strict full-margin negative region,
and AIO/AIP's previous definitions and assumptions.

The actual original one-link character chi=1-E has range [-1,1] and genuine
Haar mean zero. The pinned Hoeffding lemma applies to that variable and measure,
yielding z(beta)<=exp(-beta+beta^2/2) for ALL real couplings. The supporting-line
inequality for exp gives the matching lower bound exp(-beta)<=z(beta).
Using the actual original product exponent n_H=p_H gives
  exp(beta*p_H/2) <= Zcross_H(beta)*exp(3*beta*p_H/2)
                  <= exp(p_H*(beta+beta^2)/2).

For the NEW rational endpoint q_H=2*log(2)/(p_H+2*log(2)), the quadratic budget
is STRICT throughout 0<beta<=q_H, including the upper endpoint. Thus the SAME
old full-margin region has genuine Haar mass at least 1/2 on that interval.
The endpoint is at least 24/13 times AIP's previous endpoint lambda_H=log(2)/p_H.

At beta>=2*lambda_H, AIO's particular strict comparison factor<2 is impossible,
and its SAME auxiliary floor delta is no larger than the SAME AIG epsilon.
This is an obstruction to that comparison method, NOT a proof that physical
half-Haar mass or actual transfer negativity fails at those couplings.

No replacement measure, plaquette-independence assumption, modified physical
source, optimality claim, volume-uniform positive amplitude/coercivity,
Hamiltonian spectral gap, or continuum mass-gap conclusion is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped Topology Classical BigOperators InnerProductSpace ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

local notation "G" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AIQ_group : IsTopologicalGroup G :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AIQ_compact : CompactSpace G :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AIQ_countable : SecondCountableTopology G :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AIQ_measurable : MeasurableSpace G :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AIQ_borel : BorelSpace G :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

local notation "nu" => normalizedCompactHaar G
local notation "E" => specialUnitaryWilsonPlaquetteEnergy 2
local notation "z" => p4Q2PZ37AIF_originalSingleLinkPartition
local notation "chi" => p4Q2PZ35C_originalOneLinkCharacter

local instance p4Q2PZ37AIQ_singleLinkProbability : IsProbabilityMeasure nu :=
  normalizedCompactHaar_isProbabilityMeasure G

/-- The actual original SU(2) character is the continuous function 1-E. -/
theorem p4Q2PZ37AIQ_originalSingleLinkCharacter_continuous : Continuous chi := by
  change Continuous (fun g : G => (1 : ℝ) - E g)
  exact continuous_const.sub (continuous_specialUnitaryWilsonPlaquetteEnergy 2)

/-- The existing genuine Haar character-zero theorem is retained literally. -/
theorem p4Q2PZ37AIQ_originalSingleLinkCharacter_mean_zero :
    (∫ g : G, chi g ∂nu) = 0 :=
  p4Q2PZ35D4_originalOneLinkHaar_characterZero

theorem p4Q2PZ37AIQ_originalSingleLinkCharacter_mem_interval (g : G) :
    chi g ∈ Set.Icc (-1 : ℝ) 1 := by
  change -1 ≤ (1 : ℝ) - E g ∧ (1 : ℝ) - E g ≤ 1
  have hLower := specialUnitaryWilsonPlaquetteEnergy_nonneg
    (by norm_num : 0 < (2 : ℕ)) g
  have hUpper := specialUnitaryWilsonPlaquetteEnergy_le_two
    (by norm_num : 0 < (2 : ℕ)) g
  constructor <;> linarith only [hLower, hUpper]

/-- Hoeffding's lemma is applied to the actual single-link variable and
the original probability Haar, with its range and mean proved above. -/
theorem p4Q2PZ37AIQ_originalSingleLinkCharacter_subgaussian :
    ProbabilityTheory.HasSubgaussianMGF chi (1 : NNReal) nu := by
  have h := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (X := chi) (μ := nu) (a := (-1 : ℝ)) (b := (1 : ℝ))
    p4Q2PZ37AIQ_originalSingleLinkCharacter_continuous.measurable.aemeasurable
    (ae_of_all _ p4Q2PZ37AIQ_originalSingleLinkCharacter_mem_interval)
    p4Q2PZ37AIQ_originalSingleLinkCharacter_mean_zero
  norm_num at h
  exact h

/-- Exact factorization of the unchanged AIF partition, for every real
coupling. The normalized character MGF is only an auxiliary expression. -/
theorem p4Q2PZ37AIQ_originalSingleLinkPartition_characterMGF (beta : ℝ) :
    z beta = Real.exp (-beta) * ProbabilityTheory.mgf chi nu beta := by
  unfold p4Q2PZ37AIF_originalSingleLinkPartition ProbabilityTheory.mgf
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with g
  change Real.exp (-beta * E g) =
    Real.exp (-beta) * Real.exp (beta * ((1 : ℝ) - E g))
  rw [← Real.exp_add]
  congr 1
  ring

/-- Gaussian upper bound for the actual one-link Wilson partition at
every real coupling, without a scalar smallness assumption. -/
theorem p4Q2PZ37AIQ_originalSingleLinkPartition_le_gaussian (beta : ℝ) :
    z beta ≤ Real.exp (-beta + beta ^ 2 / 2) := by
  have hMGF : ProbabilityTheory.mgf chi nu beta ≤ Real.exp (beta ^ 2 / 2) := by
    simpa using p4Q2PZ37AIQ_originalSingleLinkCharacter_subgaussian.mgf_le beta
  calc
    z beta = Real.exp (-beta) * ProbabilityTheory.mgf chi nu beta :=
      p4Q2PZ37AIQ_originalSingleLinkPartition_characterMGF beta
    _ ≤ Real.exp (-beta) * Real.exp (beta ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left hMGF (Real.exp_pos _).le
    _ = Real.exp (-beta + beta ^ 2 / 2) :=
      (Real.exp_add (-beta) (beta ^ 2 / 2)).symm

/-- The supporting-line inequality for exp, integrated against the SAME
original probability Haar, gives the matching Jensen lower bound. -/
theorem p4Q2PZ37AIQ_originalSingleLinkCharacter_MGF_ge_one (beta : ℝ) :
    1 ≤ ProbabilityTheory.mgf chi nu beta := by
  have hInt : Integrable chi nu :=
    p4Q2PZ37AIQ_originalSingleLinkCharacter_continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hMean : (∫ g : G, beta * chi g + 1 ∂nu) = 1 := by
    rw [integral_add (hInt.const_mul beta) (integrable_const (μ := nu) (1 : ℝ)),
      integral_const_mul, p4Q2PZ37AIQ_originalSingleLinkCharacter_mean_zero]
    simp only [integral_const, probReal_univ, one_smul, mul_zero, zero_add]
  calc
    1 = ∫ g : G, beta * chi g + 1 ∂nu := hMean.symm
    _ ≤ ∫ g : G, Real.exp (beta * chi g) ∂nu :=
      integral_mono ((hInt.const_mul beta).add (integrable_const (μ := nu) (1 : ℝ)))
        (p4Q2PZ37AIQ_originalSingleLinkCharacter_subgaussian.integrable_exp_mul beta)
        (fun g => Real.add_one_le_exp (beta * chi g))
    _ = ProbabilityTheory.mgf chi nu beta := rfl

theorem p4Q2PZ37AIQ_originalSingleLinkPartition_ge_expMean (beta : ℝ) :
    Real.exp (-beta) ≤ z beta := by
  calc
    Real.exp (-beta) = Real.exp (-beta) * 1 := (mul_one _).symm
    _ ≤ Real.exp (-beta) * ProbabilityTheory.mgf chi nu beta :=
      mul_le_mul_of_nonneg_left (p4Q2PZ37AIQ_originalSingleLinkCharacter_MGF_ge_one beta)
        (Real.exp_pos _).le
    _ = z beta := (p4Q2PZ37AIQ_originalSingleLinkPartition_characterMGF beta).symm

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
local notation "previousCutoff" => p4Q2PZ37AIP_closedHalfHaarCouplingCutoff H

local instance p4Q2PZ37AIQ_probability : IsProbabilityMeasure muH := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- The actual product partition uses the original link count n_H=p_H.
The bound is valid for ALL real couplings, without plaquette independence. -/
theorem p4Q2PZ37AIQ_originalCrossingPartition_le_gaussian (beta : ℝ) :
    Zcross beta ≤ Real.exp (pH * (-beta + beta ^ 2 / 2)) := by
  have hPow := pow_le_pow_left₀
    (p4Q2PZ37AIF_originalSingleLinkPartition_pos beta).le
    (p4Q2PZ37AIQ_originalSingleLinkPartition_le_gaussian beta) nH
  have hExp : Real.exp (-beta + beta ^ 2 / 2) ^ nH =
      Real.exp (pH * (-beta + beta ^ 2 / 2)) := by
    rw [← Real.exp_nat_mul, p4Q2PZ37AIP_originalLinkCount_eq_plaquettes H]
  rw [hExp] at hPow
  simpa only [p4Q2PZ37AIF_originalCrossingPartition, Fintype.card_eq_nat_card] using hPow

theorem p4Q2PZ37AIQ_originalCrossingPartition_ge_expMean (beta : ℝ) :
    Real.exp (-beta * pH) ≤ Zcross beta := by
  have hPow := pow_le_pow_left₀ (Real.exp_pos (-beta)).le
    (p4Q2PZ37AIQ_originalSingleLinkPartition_ge_expMean beta) nH
  have hExp : Real.exp (-beta) ^ nH = Real.exp (-beta * pH) := by
    rw [← Real.exp_nat_mul, p4Q2PZ37AIP_originalLinkCount_eq_plaquettes H]
    congr 1
    ring
  rw [hExp] at hPow
  simpa only [p4Q2PZ37AIF_originalCrossingPartition, Fintype.card_eq_nat_card] using hPow

/-- Upper bound for AIO's unchanged exact margin-comparison factor. -/
theorem p4Q2PZ37AIQ_originalMarginFactor_le_gaussian (beta : ℝ) :
    Zcross beta * Real.exp (3 * beta * pH / 2) ≤
      Real.exp (pH * (beta + beta ^ 2) / 2) := by
  calc
    _ ≤ Real.exp (pH * (-beta + beta ^ 2 / 2)) * Real.exp (3 * beta * pH / 2) :=
      mul_le_mul_of_nonneg_right
        (p4Q2PZ37AIQ_originalCrossingPartition_le_gaussian H beta) (Real.exp_pos _).le
    _ = Real.exp (pH * (beta + beta ^ 2) / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Lower bound for that SAME comparison factor, also at all real couplings. -/
theorem p4Q2PZ37AIQ_originalMarginFactor_ge_expHalf (beta : ℝ) :
    Real.exp (beta * pH / 2) ≤ Zcross beta * Real.exp (3 * beta * pH / 2) := by
  calc
    Real.exp (beta * pH / 2) =
        Real.exp (-beta * pH) * Real.exp (3 * beta * pH / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Zcross beta * Real.exp (3 * beta * pH / 2) :=
      mul_le_mul_of_nonneg_right
        (p4Q2PZ37AIQ_originalCrossingPartition_ge_expMean H beta) (Real.exp_pos _).le

/-- An integral-free quadratic sufficient condition. Its strictness is
required here and is proved, including the rational endpoint, below. -/
theorem p4Q2PZ37AIQ_originalPartitionCondition_of_quadraticBudget
    (beta : ℝ) (hBudget : pH * (beta + beta ^ 2) / 2 < Real.log 2) :
    Zcross beta * Real.exp (3 * beta * pH / 2) < 2 := by
  calc
    _ ≤ Real.exp (pH * (beta + beta ^ 2) / 2) :=
      p4Q2PZ37AIQ_originalMarginFactor_le_gaussian H beta
    _ < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr hBudget
    _ = 2 := Real.exp_log (by norm_num)

theorem p4Q2PZ37AIQ_originalFullNegativeRegion_realHaar_half_of_quadraticBudget
    (beta : ℝ) (hbeta : 0 < beta)
    (hBudget : pH * (beta + beta ^ 2) / 2 < Real.log 2) :
    (1 / 2 : ℝ) ≤ Measure.real muH (Region beta) :=
  p4Q2PZ37AIO_originalFullNegativeRegion_realHaar_half_of_partition H beta hbeta
    (p4Q2PZ37AIQ_originalPartitionCondition_of_quadraticBudget H beta hBudget)

/-- A new rational endpoint. AIG epsilon and all previous cutoff definitions
remain unchanged. The upper endpoint itself is included in the theorem. -/
def p4Q2PZ37AIQ_rationalHalfHaarCouplingCutoff : ℝ :=
  2 * Real.log 2 / (pH + 2 * Real.log 2)

local notation "cutoff" => p4Q2PZ37AIQ_rationalHalfHaarCouplingCutoff H

theorem p4Q2PZ37AIQ_rationalHalfHaarCouplingCutoff_pos : 0 < cutoff := by
  have hLog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact div_pos (mul_pos (by norm_num) hLog)
    (add_pos (p4Q2PZ37AHN_count_pos H) (mul_pos (by norm_num) hLog))

theorem p4Q2PZ37AIQ_originalCount_mul_previousCutoff :
    pH * previousCutoff = Real.log 2 := by
  have hp : pH ≠ 0 := ne_of_gt (p4Q2PZ37AHN_count_pos H)
  unfold p4Q2PZ37AIP_closedHalfHaarCouplingCutoff
  field_simp [hp]

theorem p4Q2PZ37AIQ_rationalCutoff_relative_identity :
    cutoff = (2 * pH / (pH + 2 * Real.log 2)) * previousCutoff := by
  unfold p4Q2PZ37AIQ_rationalHalfHaarCouplingCutoff
  calc
    _ = 2 * (pH * previousCutoff) / (pH + 2 * Real.log 2) := by
      rw [p4Q2PZ37AIQ_originalCount_mul_previousCutoff H]
    _ = (2 * pH / (pH + 2 * Real.log 2)) * previousCutoff := by ring

/-- A uniform relative enlargement, not a volume-uniform coupling interval
or a volume-uniform negative amplitude. -/
theorem p4Q2PZ37AIQ_rationalCutoff_ge_twentyFourThirteenths_previous :
    (24 / 13 : ℝ) * previousCutoff ≤ cutoff := by
  have hLog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hd : 0 < pH + 2 * Real.log 2 := by
    have hp := p4Q2PZ37AHN_count_pos H
    positivity
  change (24 / 13 : ℝ) * previousCutoff ≤ 2 * Real.log 2 / (pH + 2 * Real.log 2)
  apply (le_div_iff₀ hd).mpr
  have hScaled := mul_le_mul_of_nonneg_right
    (p4Q2PZ37AIP_closedCutoff_le_oneDiv24 H) hLog.le
  have hCount := p4Q2PZ37AIQ_originalCount_mul_previousCutoff H
  nlinarith only [hScaled, hCount]

theorem p4Q2PZ37AIQ_previousCutoff_lt_rationalCutoff : previousCutoff < cutoff := by
  have hLower := p4Q2PZ37AIQ_rationalCutoff_ge_twentyFourThirteenths_previous H
  have hPos := p4Q2PZ37AIP_closedHalfHaarCouplingCutoff_pos H
  linarith only [hLower, hPos]

theorem p4Q2PZ37AIQ_rationalCutoff_lt_twice_previous : cutoff < 2 * previousCutoff := by
  have hLog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hPos := p4Q2PZ37AIP_closedHalfHaarCouplingCutoff_pos H
  have hd : 0 < pH + 2 * Real.log 2 := by
    have hp := p4Q2PZ37AHN_count_pos H
    positivity
  change 2 * Real.log 2 / (pH + 2 * Real.log 2) < 2 * previousCutoff
  apply (div_lt_iff₀ hd).mpr
  have hCount := p4Q2PZ37AIQ_originalCount_mul_previousCutoff H
  have hStrict : 0 < Real.log 2 * previousCutoff := mul_pos hLog hPos
  nlinarith only [hCount, hStrict]

/-- Strict quadratic budget, including beta=cutoff. The strict step follows
from beta>0 and log(2)>0, not from replacing <= by < at the endpoint. -/
theorem p4Q2PZ37AIQ_quadraticBudget_of_le_rationalCutoff
    (beta : ℝ) (hbeta : 0 < beta) (hSmall : beta ≤ cutoff) :
    pH * (beta + beta ^ 2) / 2 < Real.log 2 := by
  have hLog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hd : 0 < pH + 2 * Real.log 2 := by
    have hp := p4Q2PZ37AHN_count_pos H
    positivity
  have hEnd : beta * (pH + 2 * Real.log 2) ≤ 2 * Real.log 2 :=
    (le_div_iff₀ hd).mp hSmall
  have hPositive : 0 < beta * Real.log 2 := mul_pos hbeta hLog
  have hLinear : beta * pH < 2 * Real.log 2 := by
    nlinarith only [hEnd, hPositive]
  have hQuadratic := mul_lt_mul_of_pos_left hLinear hbeta
  nlinarith only [hEnd, hQuadratic]

theorem p4Q2PZ37AIQ_originalPartitionCondition_of_le_rationalCutoff
    (beta : ℝ) (hbeta : 0 < beta) (hSmall : beta ≤ cutoff) :
    Zcross beta * Real.exp (3 * beta * pH / 2) < 2 :=
  p4Q2PZ37AIQ_originalPartitionCondition_of_quadraticBudget H beta
    (p4Q2PZ37AIQ_quadraticBudget_of_le_rationalCutoff H beta hbeta hSmall)

theorem p4Q2PZ37AIQ_originalNegativeMargin_lt_varianceFloor
    (beta : ℝ) (hbeta : 0 < beta) (hSmall : beta ≤ cutoff) :
    margin beta < delta beta :=
  p4Q2PZ37AIO_originalNegativeMargin_lt_varianceFloor H beta hbeta
    (p4Q2PZ37AIQ_originalPartitionCondition_of_le_rationalCutoff H beta hbeta hSmall)

theorem p4Q2PZ37AIQ_originalSource_nonpos_subset_fullNegativeRegion
    (beta : ℝ) (hbeta : 0 < beta) (hSmall : beta ≤ cutoff) :
    {B : Cfg | fCont B ≤ 0} ⊆ Region beta :=
  p4Q2PZ37AIO_originalSource_nonpos_subset_fullNegativeRegion H beta hbeta
    (p4Q2PZ37AIQ_originalPartitionCondition_of_le_rationalCutoff H beta hbeta hSmall)

theorem p4Q2PZ37AIQ_originalFullNegativeRegion_Haar_half
    (beta : ℝ) (hbeta : 0 < beta) (hSmall : beta ≤ cutoff) :
    (1 / 2 : ℝ≥0∞) ≤ muH (Region beta) :=
  p4Q2PZ37AIO_originalFullNegativeRegion_Haar_half_of_partition H beta hbeta
    (p4Q2PZ37AIQ_originalPartitionCondition_of_le_rationalCutoff H beta hbeta hSmall)

theorem p4Q2PZ37AIQ_originalFullNegativeRegion_realHaar_half
    (beta : ℝ) (hbeta : 0 < beta) (hSmall : beta ≤ cutoff) :
    (1 / 2 : ℝ) ≤ Measure.real muH (Region beta) :=
  p4Q2PZ37AIO_originalFullNegativeRegion_realHaar_half_of_partition H beta hbeta
    (p4Q2PZ37AIQ_originalPartitionCondition_of_le_rationalCutoff H beta hbeta hSmall)

theorem p4Q2PZ37AIQ_expandedEndpoint_certificate :
    previousCutoff < cutoff ∧ 0 < cutoff ∧
      Zcross cutoff * Real.exp (3 * cutoff * pH / 2) < 2 ∧
      (1 / 2 : ℝ) ≤ Measure.real muH (Region cutoff) :=
  ⟨p4Q2PZ37AIQ_previousCutoff_lt_rationalCutoff H,
    p4Q2PZ37AIQ_rationalHalfHaarCouplingCutoff_pos H,
    p4Q2PZ37AIQ_originalPartitionCondition_of_le_rationalCutoff H cutoff
      (p4Q2PZ37AIQ_rationalHalfHaarCouplingCutoff_pos H) le_rfl,
    p4Q2PZ37AIQ_originalFullNegativeRegion_realHaar_half H cutoff
      (p4Q2PZ37AIQ_rationalHalfHaarCouplingCutoff_pos H) le_rfl⟩

/-- A rigorous obstruction for AIO's particular sufficient comparison.
This does NOT say the physical half-Haar conclusion fails at such couplings. -/
theorem p4Q2PZ37AIQ_originalMarginFactor_ge_two_of_large
    (beta : ℝ) (hLarge : 2 * previousCutoff ≤ beta) :
    2 ≤ Zcross beta * Real.exp (3 * beta * pH / 2) := by
  have hScaled := mul_le_mul_of_nonneg_right hLarge (p4Q2PZ37AHN_count_pos H).le
  have hCount := p4Q2PZ37AIQ_originalCount_mul_previousCutoff H
  have hArg : Real.log 2 ≤ beta * pH / 2 := by
    nlinarith only [hScaled, hCount]
  calc
    2 = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
    _ ≤ Real.exp (beta * pH / 2) := Real.exp_le_exp.mpr hArg
    _ ≤ Zcross beta * Real.exp (3 * beta * pH / 2) :=
      p4Q2PZ37AIQ_originalMarginFactor_ge_expHalf H beta

theorem p4Q2PZ37AIQ_originalPartitionCondition_implies_lt_twice_previous
    (beta : ℝ) (hCondition : Zcross beta * Real.exp (3 * beta * pH / 2) < 2) :
    beta < 2 * previousCutoff := by
  by_contra hNot
  exact (not_lt_of_ge (p4Q2PZ37AIQ_originalMarginFactor_ge_two_of_large H beta
    (le_of_not_gt hNot))) hCondition

theorem p4Q2PZ37AIQ_originalPartitionCondition_obstructed_of_large
    (beta : ℝ) (hLarge : 2 * previousCutoff ≤ beta) :
    ¬ Zcross beta * Real.exp (3 * beta * pH / 2) < 2 :=
  not_lt_of_ge (p4Q2PZ37AIQ_originalMarginFactor_ge_two_of_large H beta hLarge)

/-- At and beyond the proved comparison ceiling, the SAME AIO floor is
no larger than the SAME original AIG margin. No sign claim is inferred. -/
theorem p4Q2PZ37AIQ_varianceFloor_le_originalNegativeMargin_of_large
    (beta : ℝ) (hLarge : 2 * previousCutoff ≤ beta) :
    delta beta ≤ margin beta := by
  have hbeta : 0 < beta := lt_of_lt_of_le
    (mul_pos (by norm_num) (p4Q2PZ37AIP_closedHalfHaarCouplingCutoff_pos H)) hLarge
  have hScaled := mul_le_mul_of_nonneg_right
    (p4Q2PZ37AIQ_originalMarginFactor_ge_two_of_large H beta hLarge)
    (p4Q2PZ37AIO_sourceNonpositiveVarianceFloor_pos H beta hbeta).le
  have hIdentity := p4Q2PZ37AIO_originalNegativeMargin_ratio_identity H beta
  nlinarith only [hScaled, hIdentity]

theorem p4Q2PZ37AIQ_comparisonCeiling_certificate :
    cutoff < 2 * previousCutoff ∧
      2 ≤ Zcross (2 * previousCutoff) * Real.exp (3 * (2 * previousCutoff) * pH / 2) ∧
      delta (2 * previousCutoff) ≤ margin (2 * previousCutoff) :=
  ⟨p4Q2PZ37AIQ_rationalCutoff_lt_twice_previous H,
    p4Q2PZ37AIQ_originalMarginFactor_ge_two_of_large H (2 * previousCutoff) le_rfl,
    p4Q2PZ37AIQ_varianceFloor_le_originalNegativeMargin_of_large H
      (2 * previousCutoff) le_rfl⟩

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIQ_originalSingleLinkCharacter_continuous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIQ_originalSingleLinkCharacter_mean_zero
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIQ_originalSingleLinkCharacter_mem_interval
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIQ_originalSingleLinkCharacter_subgaussian
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIQ_originalSingleLinkPartition_characterMGF
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIQ_originalSingleLinkPartition_le_gaussian
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIQ_originalSingleLinkCharacter_MGF_ge_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIQ_originalSingleLinkPartition_ge_expMean
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIQ_originalCrossingPartition_le_gaussian
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIQ_originalCrossingPartition_ge_expMean
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIQ_originalMarginFactor_le_gaussian
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIQ_originalMarginFactor_ge_expHalf
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIQ_originalPartitionCondition_of_quadraticBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIQ_originalFullNegativeRegion_realHaar_half_of_quadraticBudget
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIQ_rationalHalfHaarCouplingCutoff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIQ_rationalHalfHaarCouplingCutoff_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIQ_originalCount_mul_previousCutoff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIQ_rationalCutoff_relative_identity
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIQ_rationalCutoff_ge_twentyFourThirteenths_previous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIQ_previousCutoff_lt_rationalCutoff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIQ_rationalCutoff_lt_twice_previous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIQ_quadraticBudget_of_le_rationalCutoff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIQ_originalPartitionCondition_of_le_rationalCutoff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIQ_originalNegativeMargin_lt_varianceFloor
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIQ_originalSource_nonpos_subset_fullNegativeRegion
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIQ_originalFullNegativeRegion_Haar_half
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIQ_originalFullNegativeRegion_realHaar_half
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIQ_expandedEndpoint_certificate
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIQ_originalMarginFactor_ge_two_of_large
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIQ_originalPartitionCondition_implies_lt_twice_previous
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIQ_originalPartitionCondition_obstructed_of_large
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIQ_varianceFloor_le_originalNegativeMargin_of_large
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AIQ_comparisonCeiling_certificate
