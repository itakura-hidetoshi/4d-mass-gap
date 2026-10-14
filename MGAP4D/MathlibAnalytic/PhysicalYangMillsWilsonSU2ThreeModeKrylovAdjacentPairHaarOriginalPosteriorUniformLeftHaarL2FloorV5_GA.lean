import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalSU2TemporalWilsonContrastHaarVarianceV5_FZ
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalNormalizedPosteriorTemporalLogCrossingV5_FR
import Mathlib.Tactic

/-!
# P4-Q2-GA: quantitative TRUE Wilson posterior left sensitivity in Haar L²

FZ proves the nonzero SU(2) Haar variance V_SU2 of the EXACT original
temporal crossing energy contrast D(g) = E_W(g) - E_W(Rpi^-1 g).
FR identifies, after TRUE Wilson-posterior normalization cancels,
  (log p0(g)-log p1(g)) - (log p0(h)-log p1(h))
    = -beta*(D(g)-D(h)).
Hence the centered logarithmic posterior density-row difference has
variance EXACTLY beta^2 * V_SU2 under compact Haar.

FK gives p0,p1 >= m_beta = exp(-16 beta) pointwise. Elementary log
Lipschitz and the best-centered L² inequality then imply the genuinely
UNIFORM (in H, e and right environment) integrated bound

  beta^2 * exp(-32 beta) * V_SU2
    <= integral_SU2 (p0(g)-p1(g))^2 dHaar(g).

This is a source-independent, genuine normalized-WILSON-posterior
left-boundary sensitivity lower bound in integrated Haar L². Unlike FY,
it does NOT infer an integral bound from two Haar-null test points:
the proof exploits the EXACT temporal one-link log-ratio functional
identity at EVERY SU(2) g, and a proved strictly positive Haar variance.

This is not yet the original FF/FG source-dependent signed receiver
RMS coercive floor nor H1-C3 or a continuum Yang--Mills mass gap.
The true physical posterior is unchanged; normalized Haar is ONLY
the specified analytic comparison measure.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped ENNReal InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 700000

local instance p4Q2GA_topologicalGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup 2
local instance p4Q2GA_compactSpace :
    CompactSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupCompactSpace 2
local instance p4Q2GA_secondCountable :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupSecondCountableTopology 2
local instance p4Q2GA_measurableSpace :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupMeasurableSpace 2
local instance p4Q2GA_borelSpace :
    BorelSpace (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  specialUnitaryGroupBorelSpace 2

namespace GroundStatePosteriorJoint

/-- Scalar logarithmic Lipschitz bound on the two positive density rows,
with the exact common density floor retained. -/
private theorem p4Q2GA_abs_log_sub_log_le_abs_sub_div_lower
    {x y m : ℝ}
    (hm : 0 < m)
    (hmx : m ≤ x)
    (hmy : m ≤ y) :
    |Real.log x - Real.log y| ≤ |x - y| / m := by
  have hx : 0 < x := lt_of_lt_of_le hm hmx
  have hy : 0 < y := lt_of_lt_of_le hm hmy
  have hUpper :
      Real.log x - Real.log y ≤ |x - y| / m := by
    rw [← Real.log_div hx.ne' hy.ne']
    calc
      Real.log (x / y) ≤ x / y - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hx hy)
      _ = (x - y) / y := by
        field_simp [hy.ne']
      _ ≤ |x - y| / m := by
        apply (div_le_div_iff₀ hy hm).2
        calc
          (x - y) * m ≤ |x - y| * m :=
            mul_le_mul_of_nonneg_right (le_abs_self (x - y)) hm.le
          _ ≤ |x - y| * y :=
            mul_le_mul_of_nonneg_left hmy (abs_nonneg (x - y))
  have hReverse :
      Real.log y - Real.log x ≤ |y - x| / m := by
    rw [← Real.log_div hy.ne' hx.ne']
    calc
      Real.log (y / x) ≤ y / x - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hy hx)
      _ = (y - x) / x := by
        field_simp [hx.ne']
      _ ≤ |y - x| / m := by
        apply (div_le_div_iff₀ hx hm).2
        calc
          (y - x) * m ≤ |y - x| * m :=
            mul_le_mul_of_nonneg_right (le_abs_self (y - x)) hm.le
          _ ≤ |y - x| * x :=
            mul_le_mul_of_nonneg_left hmx (abs_nonneg (y - x))
  apply abs_le.mpr
  constructor
  · rw [abs_sub_comm] at hReverse
    linarith
  · exact hUpper

/-- For any compact probability measure, the original L² second
moment is at least the squared centered deviation. This exact
best-constant Pythagorean fact is proved rather than assumed. -/
theorem p4Q2GA_continuousProbability_centeredSecondMoment_le_uncentered
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (F : X → ℝ) (hF : Continuous F) :
    (∫ x, (F x - ∫ y, F y ∂μ) ^ 2 ∂μ) ≤
      ∫ x, (F x) ^ 2 ∂μ := by
  let m : ℝ := ∫ x, F x ∂μ
  have hFInt : Integrable F μ :=
    hF.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hCenteredContinuous : Continuous (fun x => F x - m) :=
    hF.sub continuous_const
  have hCenteredInt : Integrable (fun x => F x - m) μ :=
    hCenteredContinuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hSquareInt : Integrable (fun x => (F x - m) ^ 2) μ :=
    (hCenteredContinuous.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hCrossInt : Integrable (fun x => 2 * m * (F x - m)) μ :=
    (continuous_const.mul hCenteredContinuous).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hMeanZero : (∫ x, F x - m ∂μ) = 0 := by
    rw [integral_sub hFInt (integrable_const _)]
    simp [m]
  have hAdd1 :
      (∫ x, (F x - m) ^ 2 + 2 * m * (F x - m) ∂μ) =
        (∫ x, (F x - m) ^ 2 ∂μ) +
          (∫ x, 2 * m * (F x - m) ∂μ) := by
    simpa only [Pi.add_apply] using
      (integral_add hSquareInt hCrossInt)
  have hAdd2 :
      (∫ x, ((F x - m) ^ 2 + 2 * m * (F x - m)) + m ^ 2 ∂μ) =
        (∫ x, (F x - m) ^ 2 + 2 * m * (F x - m) ∂μ) + m ^ 2 := by
    simpa only [Pi.add_apply, integral_const] using
      (integral_add (hSquareInt.add hCrossInt) (integrable_const (m ^ 2)))
  have hExpand :
      (∫ x, (F x) ^ 2 ∂μ) =
        (∫ x, (F x - m) ^ 2 ∂μ) +
          2 * m * (∫ x, F x - m ∂μ) + m ^ 2 := by
    calc
      (∫ x, (F x) ^ 2 ∂μ) =
          ∫ x, ((F x - m) ^ 2 + 2 * m * (F x - m) + m ^ 2) ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        ring
      _ = (∫ x, (F x - m) ^ 2 + 2 * m * (F x - m) ∂μ) + m ^ 2 := hAdd2
      _ = (∫ x, (F x - m) ^ 2 ∂μ) +
            (∫ x, 2 * m * (F x - m) ∂μ) + m ^ 2 := by
        rw [hAdd1]
      _ = (∫ x, (F x - m) ^ 2 ∂μ) +
            2 * m * (∫ x, F x - m ∂μ) + m ^ 2 := by
        rw [integral_const_mul]
  have hIdentity : (∫ x, (F x) ^ 2 ∂μ) =
      (∫ x, (F x - m) ^ 2 ∂μ) + m ^ 2 := by
    rw [hMeanZero] at hExpand
    nlinarith [hExpand]
  have hMNonneg : 0 ≤ m ^ 2 := sq_nonneg m
  change (∫ x, (F x - m) ^ 2 ∂μ) ≤ ∫ x, (F x) ^ 2 ∂μ
  linarith

/-- Difference of the true left-row normalized Wilson-posterior log
densities. The ORIGINAL two physical left boundaries are used. -/
noncomputable def p4Q2GA_originalSU2WilsonPosteriorLeftLogDensityContrast
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) : ℝ :=
  Real.log
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
      H 2 (by norm_num) beta hbeta
      (originalWilsonExplicitIdentityBoundary H) right e g) -
  Real.log
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
      H 2 (by norm_num) beta hbeta
      (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e g)

/-- The exact TRUE normalized Wilson posterior log row-difference
is a constant shift of -beta times the one-link ORIGINAL SU(2) Wilson
energy contrast. Every unknown physical vacuum/partition factor cancels. -/
theorem p4Q2GA_originalSU2WilsonPosteriorLogContrast_relative_exact
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H)
    (g h : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    p4Q2GA_originalSU2WilsonPosteriorLeftLogDensityContrast
        H beta hbeta right e g -
      p4Q2GA_originalSU2WilsonPosteriorLeftLogDensityContrast
        H beta hbeta right e h =
      -beta *
        (p4Q2FZ_originalSU2TemporalWilsonContrast g -
          p4Q2FZ_originalSU2TemporalWilsonContrast h) := by
  have hIdentity :
      (originalWilsonExplicitIdentityBoundary H e) =
        (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) := rfl
  have hPi :
      p4Q2FQ_originalSU2LeftPiRotationAtLink H e e =
        specialUnitaryTwoRotation Real.pi :=
    p4Q2FQ_originalSU2LeftPiRotationAtLink_value H e
  have hCross :=
    p4Q2FR_originalWilsonNormalizedPosteriorLogCrossing_eq_temporalEnergy
      H 2 (by norm_num) beta hbeta
      (originalWilsonExplicitIdentityBoundary H)
      (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e g h
  rw [hIdentity, hPi] at hCross
  simp only [inv_one, one_mul] at hCross
  unfold p4Q2GA_originalSU2WilsonPosteriorLeftLogDensityContrast
    p4Q2FZ_originalSU2TemporalWilsonContrast
  nlinarith [hCross]

/-- Quantitative uniform Haar L² lower bound for the ORIGINAL interacting
SU(2) Wilson normalized posterior left-boundary density sensitivity, for
every true physical link and right environment. The universal variance
is the exact FZ original Wilson Haar contrast, independent of H/e/right. -/
theorem p4Q2GA_originalSU2WilsonPosteriorLeftSensitivityHaarSq_uniform_lower
    (H : ℕ) (beta : ℝ) (hbeta : 0 ≤ beta)
    (right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    Real.exp (-32 * beta) * (beta ^ 2 *
        p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance) ≤
      p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
        H beta hbeta right e := by
  let μ : Measure (Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
    normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin 2) ℂ)
  let P0 : Matrix.specialUnitaryGroup (Fin 2) ℂ → ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
      H 2 (by norm_num) beta hbeta
      (originalWilsonExplicitIdentityBoundary H) right e
  let P1 : Matrix.specialUnitaryGroup (Fin 2) ℂ → ℝ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkConditionalDensity
      H 2 (by norm_num) beta hbeta
      (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e
  let L := p4Q2GA_originalSU2WilsonPosteriorLeftLogDensityContrast
    H beta hbeta right e
  let D := p4Q2FZ_originalSU2TemporalWilsonContrast
  let m : ℝ := Real.exp (-16 * beta)
  let k : ℝ :=
    L (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ) +
      beta * D (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)
  have hP0Cont : Continuous P0 := by
    change Continuous
      (continuousNormalizedExp μ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
          H 2 (by norm_num) beta hbeta
          (originalWilsonExplicitIdentityBoundary H) right e))
    exact continuous_continuousNormalizedExp μ _
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_continuous
        H 2 (by norm_num) beta hbeta
        (originalWilsonExplicitIdentityBoundary H) right e)
  have hP1Cont : Continuous P1 := by
    change Continuous
      (continuousNormalizedExp μ
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight
          H 2 (by norm_num) beta hbeta
          (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e))
    exact continuous_continuousNormalizedExp μ _
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumPosteriorSpatialLinkFiberLogWeight_continuous
        H 2 (by norm_num) beta hbeta
        (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e)
  have hm : 0 < m := Real.exp_pos _
  have hDensityLower (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
      m ≤ P0 g ∧ m ≤ P1 g := by
    exact ⟨
      (p4Q2FK_originalWilsonPosteriorConditionalDensity_twoSided
        H 2 (by norm_num) beta hbeta
        (originalWilsonExplicitIdentityBoundary H) right e g).1,
      (p4Q2FK_originalWilsonPosteriorConditionalDensity_twoSided
        H 2 (by norm_num) beta hbeta
        (p4Q2FQ_originalSU2LeftPiRotationAtLink H e) right e g).1⟩
  have hP0Pos (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
      P0 g ≠ 0 := (hm.trans_le (hDensityLower g).1).ne'
  have hP1Pos (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
      P1 g ≠ 0 := (hm.trans_le (hDensityLower g).2).ne'
  have hLCont : Continuous L := by
    change Continuous (fun g => Real.log (P0 g) - Real.log (P1 g))
    exact (hP0Cont.log hP0Pos).sub (hP1Cont.log hP1Pos)
  have hDCont : Continuous D := p4Q2FZ_originalSU2TemporalWilsonContrast_continuous
  have hLInt : Integrable L μ :=
    hLCont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hDInt : Integrable D μ :=
    hDCont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hFormula (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
      L g = -beta * D g + k := by
    have hRel :=
      p4Q2GA_originalSU2WilsonPosteriorLogContrast_relative_exact
        H beta hbeta right e g (1 : Matrix.specialUnitaryGroup (Fin 2) ℂ)
    dsimp [L, D, k] at hRel ⊢
    nlinarith [hRel]
  have hIntegral :
      (∫ g, L g ∂μ) = -beta * (∫ g, D g ∂μ) + k := by
    calc
      (∫ g, L g ∂μ) =
          ∫ g, (-beta * D g + k) ∂μ := by
        apply integral_congr_ae
        filter_upwards with g
        exact hFormula g
      _ = -beta * (∫ g, D g ∂μ) + k := by
        rw [integral_add (hDInt.const_mul _) (integrable_const _)]
        rw [integral_const_mul]
        simp
  have hCentered (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
      L g - (∫ x, L x ∂μ) =
        -beta * (D g - (∫ x, D x ∂μ)) := by
    rw [hFormula g, hIntegral]
    ring
  have hVariance :
      (∫ g, (L g - ∫ x, L x ∂μ) ^ 2 ∂μ) =
        beta ^ 2 * p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance := by
    calc
      (∫ g, (L g - ∫ x, L x ∂μ) ^ 2 ∂μ) =
          ∫ g, (-beta * (D g - ∫ x, D x ∂μ)) ^ 2 ∂μ := by
        apply integral_congr_ae
        filter_upwards with g
        rw [hCentered g]
      _ = beta ^ 2 * (∫ g, (D g - ∫ x, D x ∂μ) ^ 2 ∂μ) := by
        calc
          (∫ g, (-beta * (D g - ∫ x, D x ∂μ)) ^ 2 ∂μ) =
            ∫ g, beta ^ 2 * (D g - ∫ x, D x ∂μ) ^ 2 ∂μ := by
              apply integral_congr_ae
              filter_upwards with g
              ring
          _ = beta ^ 2 * (∫ g, (D g - ∫ x, D x ∂μ) ^ 2 ∂μ) := by
              rw [integral_const_mul]
      _ = beta ^ 2 * p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance := rfl
  have hLogVarianceLower :
      beta ^ 2 * p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance ≤
        ∫ g, (L g) ^ 2 ∂μ := by
    calc
      beta ^ 2 * p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance =
          (∫ g, (L g - ∫ x, L x ∂μ) ^ 2 ∂μ) := hVariance.symm
      _ ≤ ∫ g, (L g) ^ 2 ∂μ :=
        p4Q2GA_continuousProbability_centeredSecondMoment_le_uncentered μ L hLCont
  have hPoint (g : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
      m ^ 2 * (L g) ^ 2 ≤ (P0 g - P1 g) ^ 2 := by
    have hAbs :=
      p4Q2GA_abs_log_sub_log_le_abs_sub_div_lower
        hm (hDensityLower g).1 (hDensityLower g).2
    have hMul : m * |L g| ≤ |P0 g - P1 g| := by
      have h := (le_div_iff₀ hm).mp hAbs
      simpa only [L, p4Q2GA_originalSU2WilsonPosteriorLeftLogDensityContrast,
        mul_comm] using h
    have hSq :=
      pow_le_pow_left₀
        (mul_nonneg hm.le (abs_nonneg (L g))) hMul 2
    simpa only [mul_pow, sq_abs] using hSq
  have hLsqInt : Integrable (fun g => (L g) ^ 2) μ :=
    (hLCont.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hPdiffInt : Integrable (fun g => (P0 g - P1 g) ^ 2) μ :=
    ((hP0Cont.sub hP1Cont).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hIntegralBound :
      m ^ 2 * (∫ g, (L g) ^ 2 ∂μ) ≤
      ∫ g, (P0 g - P1 g) ^ 2 ∂μ := by
    calc
      m ^ 2 * (∫ g, (L g) ^ 2 ∂μ) =
          ∫ g, m ^ 2 * (L g) ^ 2 ∂μ := by
        rw [integral_const_mul]
      _ ≤ ∫ g, (P0 g - P1 g) ^ 2 ∂μ := by
        apply integral_mono (hLsqInt.const_mul _) hPdiffInt
        intro g
        exact hPoint g
  have hExp : m ^ 2 = Real.exp (-32 * beta) := by
    dsimp [m]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hScaled :=
    mul_le_mul_of_nonneg_left hLogVarianceLower (sq_nonneg m)
  calc
    Real.exp (-32 * beta) *
        (beta ^ 2 * p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance) =
      m ^ 2 *
        (beta ^ 2 * p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance) := by
        rw [hExp]
    _ ≤ m ^ 2 * (∫ g, (L g) ^ 2 ∂μ) := hScaled
    _ ≤ ∫ g, (P0 g - P1 g) ^ 2 ∂μ := hIntegralBound
    _ = p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
          H beta hbeta right e := rfl

/-- At beta>0, the density-left-sensitivity Haar L² norm has a common
STRICTLY POSITIVE explicit expression for ALL finite H, physical
links and right environments. This is a genuine integrated posterior
statement, not a two-point Haar-atom fallacy. -/
theorem p4Q2GA_originalSU2WilsonPosteriorLeftSensitivityHaarSq_uniform_pos
    (H : ℕ) (beta : ℝ) (hbeta : 0 < beta)
    (right : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 <
      Real.exp (-32 * beta) * (beta ^ 2 *
        p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance) ∧
    Real.exp (-32 * beta) * (beta ^ 2 *
        p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance) ≤
      p4Q2FX_originalSU2WilsonPosteriorLeftSensitivityHaarSq
        H beta (le_of_lt hbeta) right e := by
  constructor
  · exact mul_pos (Real.exp_pos _)
      (mul_pos (pow_pos hbeta 2)
        p4Q2FZ_originalSU2TemporalWilsonContrastHaarVariance_pos)
  · exact p4Q2GA_originalSU2WilsonPosteriorLeftSensitivityHaarSq_uniform_lower
      H beta (le_of_lt hbeta) right e

end GroundStatePosteriorJoint
end
end MathlibAnalytic
end MGAP4D

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GA_continuousProbability_centeredSecondMoment_le_uncentered
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GA_originalSU2WilsonPosteriorLogContrast_relative_exact
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GA_originalSU2WilsonPosteriorLeftSensitivityHaarSq_uniform_lower
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2GA_originalSU2WilsonPosteriorLeftSensitivityHaarSq_uniform_pos
