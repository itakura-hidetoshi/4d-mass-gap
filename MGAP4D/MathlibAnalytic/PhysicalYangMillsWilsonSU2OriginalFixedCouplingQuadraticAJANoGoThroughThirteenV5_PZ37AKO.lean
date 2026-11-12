import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalHalfWeightedTopQuadraticAJANoGoV5_PZ37AKN
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-!
# P4-Q2-PZ37AKO: strengthen original fixed-coupling AJA no-witness to H <= 13

The AKN ORIGINAL weighted Haar/top no-witness theorem already covers beta>0
when beta^2*p_H/2 <= log 4. We improve ONLY the fixed numerical beta0
and exact original plaquette-count estimate, keeping P, S, f0, Haar,
negative region, margin, top Q, pinned Lean/mathlib and root unchanged.

The rational power comparison (3/2) <= (79/78)^32 gives
  log(3/2) <= 16/39, hence beta0=log(3/2)/64 <= 1/156.
The pinned Mathlib analytic log bound gives log 4 >= 11/8.
For all H <= 13, the genuine original plaquette count p_H <= 65856, so
  beta0^2*p_H/2 <= 65856/(2*156^2) < 11/8 <= log 4.
AKN then forbids the genuine strict original AJA Haar-budget witness
for every natural power n at every H <= 13, including H=11,12,13.

This is no claim for H >= 14, for other beta outside AKN's criterion,
or for the Yang--Mills Hamiltonian/continuum mass gap.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace Topology Classical ENNReal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option synthInstance.maxHeartbeats 1050000

/-- A rational 32nd-power majorant yields a certified numerical upper bound
for the actual logarithm appearing in the unchanged original coupling. -/
theorem p4Q2PZ37AKO_log_threeHalves_le_sixteenOverThirtyNine :
    Real.log (3 / 2 : ℝ) ≤ (16 / 39 : ℝ) := by
  have hp : (3 / 2 : ℝ) ≤ (79 / 78 : ℝ) ^ (32 : ℕ) := by norm_num
  have hlog : Real.log (3 / 2 : ℝ) ≤
      Real.log ((79 / 78 : ℝ) ^ (32 : ℕ)) :=
    Real.log_le_log (by norm_num) hp
  have hq : Real.log (79 / 78 : ℝ) ≤ (1 / 78 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos
      (show (0 : ℝ) < (79 / 78 : ℝ) by norm_num)
    linarith only [h]
  calc
    Real.log (3 / 2 : ℝ) ≤ Real.log ((79 / 78 : ℝ) ^ (32 : ℕ)) := hlog
    _ = (32 : ℝ) * Real.log (79 / 78 : ℝ) := Real.log_pow _ _
    _ ≤ (32 : ℝ) * (1 / 78 : ℝ) :=
      mul_le_mul_of_nonneg_left hq (by norm_num)
    _ = (16 / 39 : ℝ) := by norm_num

/-- Exact fixed beta0 from the original physical model, not a new coupling. -/
theorem p4Q2PZ37AKO_originalFixedCoupling_le_oneOver156 :
    GroundStatePosteriorJoint.p4Q2PZ37ADC_fixedCoupling ≤ (1 / 156 : ℝ) := by
  have h := p4Q2PZ37AKO_log_threeHalves_le_sixteenOverThirtyNine
  change Real.log (3 / 2 : ℝ) / 64 ≤ (1 / 156 : ℝ)
  linarith only [h]

/-- The pinned Mathlib accurate logarithm bound gives a rational floor on
log 4, stronger than the one-unit bound used in AKN's H<=10 example. -/
theorem p4Q2PZ37AKO_elevenEighths_le_log_four :
    (11 / 8 : ℝ) ≤ Real.log 4 := by
  have h : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have heq : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  linarith only [h, heq]

local notation "GO" => Matrix.specialUnitaryGroup (Fin 2) ℂ
local instance p4Q2PZ37AKO_group : IsTopologicalGroup GO :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2PZ37AKO_compact : CompactSpace GO :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2PZ37AKO_countable : SecondCountableTopology GO :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2PZ37AKO_measurable : MeasurableSpace GO :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2PZ37AKO_borel : BorelSpace GO :=
  specialUnitaryGroupBorelSpace 2
local instance p4Q2PZ37AKO_links (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) := Fintype.ofFinite _

namespace GroundStatePosteriorJoint

variable (H : ℕ)
local notation "CfgO" => PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2
local notation "muO" => periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2
local notation "fO" => p4Q2PZ37ZW_originalCenteredPhysicalDirection H
local notation "SO" =>
  periodicHypercubicEvenSpecialUnitaryNormalizedPhysicalOneSlabTransferOperator H 2 (by norm_num)
local notation "uO" => p4Q2PZ37AIW_originalNormalizedSourceTransfer H
local notation "mO" => p4Q2PZ37AIW_originalNormalizedNegativeMargin H
local notation "pO" => p4Q2PZ37AFZ_plaquetteCount H
local notation "beta0" => p4Q2PZ37ADC_fixedCoupling

local instance p4Q2PZ37AKO_probability : IsProbabilityMeasure muO := by
  dsimp [periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure]
  infer_instance

/-- Exact original plaquette count bound for all finite H through 13. -/
theorem p4Q2PZ37AKO_originalPlaquetteCount_le_thirteen
    (hH : H ≤ 13) : pO ≤ 65856 := by
  have hHR : (H : ℝ) ≤ 13 := by exact_mod_cast hH
  have hCube : ((H : ℝ) + 1) ^ 3 ≤ (14 : ℝ) ^ 3 :=
    pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (H : ℝ) + 1)
      (by linarith only [hHR]) 3
  rw [p4Q2PZ37AIB_plaquetteCount_exact]
  norm_num at hCube ⊢
  nlinarith only [hCube]

/-- The actual unchanged beta0 satisfies the exact AKN quadratic criterion
for every H <= 13 (the new H=11,12,13 cases require stronger log bounds). -/
theorem p4Q2PZ37AKO_originalFixedCoupling_quadratic_at_le_thirteen
    (hH : H ≤ 13) :
    beta0 ^ 2 * pO / 2 ≤ Real.log 4 := by
  have hb0 : 0 ≤ beta0 := p4Q2PZ37ADC_fixedCoupling_pos.le
  have hb : beta0 ≤ (1 / 156 : ℝ) :=
    p4Q2PZ37AKO_originalFixedCoupling_le_oneOver156
  have hp : pO ≤ 65856 :=
    p4Q2PZ37AKO_originalPlaquetteCount_le_thirteen H hH
  have hbSq := pow_le_pow_left₀ hb0 hb 2
  have hMul1 := mul_le_mul_of_nonneg_right hbSq (p4Q2PZ37AHN_count_pos H).le
  have hMul2 := mul_le_mul_of_nonneg_left hp (sq_nonneg (1 / 156 : ℝ))
  have hSmall : beta0 ^ 2 * pO / 2 ≤ (11 / 8 : ℝ) := by
    nlinarith only [hMul1, hMul2]
  exact hSmall.trans p4Q2PZ37AKO_elevenEighths_le_log_four

/-- Genuine ORIGINAL Haar-budget witness nonexistence at the fixed beta0
for all H <= 13, retaining the source, operator, top and negative region. -/
theorem p4Q2PZ37AKO_originalFixedCoupling_le_thirteen_no_AJA_power_witness
    (hH : H ≤ 13) :
    ¬ ∃ n : ℕ,
      ‖((SO beta0 p4Q2PZ37ADC_fixedCoupling_pos.le) ^ n) fO‖ ^ 2 <
        (mO beta0 p4Q2PZ37ADC_fixedCoupling_pos.le) ^ 2 *
          Measure.real muO {A : CfgO |
            uO beta0 p4Q2PZ37ADC_fixedCoupling_pos.le A <
              -(mO beta0 p4Q2PZ37ADC_fixedCoupling_pos.le)} :=
  p4Q2PZ37AKN_originalQuadratic_no_AJA_power_witness H
    beta0 p4Q2PZ37ADC_fixedCoupling_pos
    (p4Q2PZ37AKO_originalFixedCoupling_quadratic_at_le_thirteen H hH)

/-- In particular, the boundary case H=13 is now ruled out without any
assumption about the unknown original full-top versus Haar-budget sign. -/
theorem p4Q2PZ37AKO_originalFixedCoupling_at_thirteen_no_AJA_power_witness :
    ¬ ∃ n : ℕ,
      ‖((SO beta0 p4Q2PZ37ADC_fixedCoupling_pos.le) ^ n)
        (p4Q2PZ37ZW_originalCenteredPhysicalDirection 13)‖ ^ 2 <
        (p4Q2PZ37AIW_originalNormalizedNegativeMargin 13
          beta0 p4Q2PZ37ADC_fixedCoupling_pos.le) ^ 2 *
          Measure.real
            (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure 13 2)
              {A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration 13 2 |
                p4Q2PZ37AIW_originalNormalizedSourceTransfer 13
                  beta0 p4Q2PZ37ADC_fixedCoupling_pos.le A <
                  -(p4Q2PZ37AIW_originalNormalizedNegativeMargin 13
                    beta0 p4Q2PZ37ADC_fixedCoupling_pos.le)} := by
  exact p4Q2PZ37AKO_originalFixedCoupling_le_thirteen_no_AJA_power_witness
    13 (by norm_num)

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AKO_log_threeHalves_le_sixteenOverThirtyNine
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AKO_originalFixedCoupling_le_oneOver156
#print axioms MGAP4D.MathlibAnalytic.p4Q2PZ37AKO_elevenEighths_le_log_four
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKO_originalPlaquetteCount_le_thirteen
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKO_originalFixedCoupling_quadratic_at_le_thirteen
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKO_originalFixedCoupling_le_thirteen_no_AJA_power_witness
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37AKO_originalFixedCoupling_at_thirteen_no_AJA_power_witness
