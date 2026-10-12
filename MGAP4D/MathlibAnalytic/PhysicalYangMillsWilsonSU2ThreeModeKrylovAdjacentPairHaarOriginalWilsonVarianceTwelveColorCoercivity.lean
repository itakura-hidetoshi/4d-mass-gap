import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTwelveColorGlobalHilbertFloor
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalPhysicalVarianceSandwich
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2ThreeModeKrylovAdjacentPairHaarOriginalTwelveColorRelativeFrameBridge
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-!
# P4-Q2-DR: positive finite-volume physical Wilson variance coercivity

DQ bounds the literal original Wilson Haar twelve-color reference below
by a STRICTLY POSITIVE finite-volume multiple of the unnormalized true
independent pair-Haar all-coordinate L² residual sum. DC identifies
the genuine pair-Haar global-mean Poincare bound. DF separately bounds
the genuine physical Wilson variance by a finite-volume multiple of the
pair-Haar variance. Finally BC bounds the original Haar reference ABOVE
by the genuine physical Wilson twelve-color conditional-expectation
Hilbert residual energy.

The missing concrete bridge is proved here, not postulated: the genuine
pair-Haar L² global-mean centered norm squared equals the actual variance
of any representative, using L2.inner_def, Lp.coeFn_sub/const and the
AE-invariance of variance.

Consequently there is ONE strictly positive finite-volume coefficient,
independent of the bounded observable, for which the ACTUAL physical
twelve-color energy bounds genuine physical Wilson probability variance.

The coefficient can depend on H,N,beta. This proves neither a
volume-uniform/continuum spectral gap nor an interacting Wilson link
projection commutation theorem. No replacement physical law enters.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators InnerProductSpace

noncomputable section

set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 850000

attribute [local instance]
  groundStateJointOneLinkCenteredResidualSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkCenteredResidualSpecialUnitaryCompactSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkCenteredResidualSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkCenteredResidualSpecialUnitaryBorelSpace
  groundStateJointOneLinkCenteredResidualSpatialLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkFintype
  groundStateJointOneLinkCenteredResidualTargetLinkUnique
  p4Q2BAColorLinksFintype

section OriginalWilson

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Cfg" =>
  PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N
local notation "Joint" => Cfg × Cfg
local notation "I" => PeriodicHypercubicEvenGroundStateJointSpatialCoordinate H
local notation "muPair" =>
  periodicHypercubicEvenSpecialUnitarySpatialSlicePairHaarMeasure H N
local notation "muWilson" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointMeasure
    H N hN beta hbeta
local notation "JH" => Lp ℝ 2 muPair
local notation "P" => p4Q2CR_actualPairHaarCoordinateProjection H N

/-- The EXACT probability variance of a genuine pair-Haar L² class equals
the squared Hilbert distance to its TRUE pair-Haar global-mean constant.
The proof uses actual Lp representatives, not an unproved identification
of two distinct physical probability means. -/
theorem p4Q2DR_actualPairHaarVariance_eq_globalMeanCenteredNormSq
    (f : JH) :
    variance (f : Joint → ℝ) muPair =
      ‖f - Lp.const 2 muPair
        (∫ z : Joint, (f : Joint → ℝ) z ∂muPair)‖ ^ 2 := by
  let c : ℝ := ∫ z : Joint, (f : Joint → ℝ) z ∂muPair
  let g : JH := f - Lp.const 2 muPair c
  have hConst :
      ((Lp.const 2 muPair c : JH) : Joint → ℝ) =ᵐ[muPair]
        (fun _ : Joint => c) := by
    simpa only [Function.const_apply] using
      (Lp.coeFn_const (p := (2 : ℝ≥0∞)) (μ := muPair) (c := c))
  have hSub :
      (g : Joint → ℝ) =ᵐ[muPair]
        (fun z : Joint => (f : Joint → ℝ) z - c) := by
    filter_upwards [Lp.coeFn_sub f (Lp.const 2 muPair c), hConst]
      with z hz hc
    simpa only [Pi.sub_apply, hc] using hz
  have hSquaredIntegrals :
      (∫ z : Joint, ((f : Joint → ℝ) z - c) ^ 2 ∂muPair) =
        ∫ z : Joint, ((g : Joint → ℝ) z) ^ 2 ∂muPair := by
    apply integral_congr_ae
    filter_upwards [hSub] with z hz
    rw [hz]
  have hL2Squared :
      (∫ z : Joint, ((g : Joint → ℝ) z) ^ 2 ∂muPair) = ‖g‖ ^ 2 := by
    calc
      (∫ z : Joint, ((g : Joint → ℝ) z) ^ 2 ∂muPair) =
          ∫ z : Joint, inner ℝ ((g : Joint → ℝ) z) ((g : Joint → ℝ) z)
            ∂muPair := by
        congr 1
        funext z
        rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
      _ = inner ℝ g g := (L2.inner_def g g).symm
      _ = ‖g‖ ^ 2 := real_inner_self_eq_norm_sq g
  calc
    variance (f : Joint → ℝ) muPair =
        ∫ z : Joint,
          ((f : Joint → ℝ) z - c) ^ 2 ∂muPair := by
      simpa only [c] using
        (variance_eq_integral (Lp.aestronglyMeasurable f).aemeasurable)
    _ = ‖g‖ ^ 2 := hSquaredIntegrals.trans hL2Squared
    _ = ‖f - Lp.const 2 muPair
        (∫ z : Joint, (f : Joint → ℝ) z ∂muPair)‖ ^ 2 := rfl

/-- DC's TRUE pair-Haar global-mean Poincare theorem is converted to
the ENNReal-valued full coordinate residual sum used by genuine DQ. -/
theorem p4Q2DR_actualPairHaarVariance_le_allCoordinateENNRealDefects
    (f : JH) :
    ENNReal.ofReal (variance (f : Joint → ℝ) muPair) ≤
      ∑ i : I, ENNReal.ofReal (‖f - P i f‖ ^ 2) := by
  classical
  have hDC :
      ‖f - Lp.const 2 muPair
        (∫ z : Joint, (f : Joint → ℝ) z ∂muPair)‖ ^ 2 ≤
          ∑ i : I, ‖f - P i f‖ ^ 2 := by
    simpa only [Finset.sum_univ] using
      (p4Q2DC_actualPairHaar_globalMeanPoincare H N f)
  have hSum :
      ENNReal.ofReal (∑ i : I, ‖f - P i f‖ ^ 2) =
        ∑ i : I, ENNReal.ofReal (‖f - P i f‖ ^ 2) :=
    ENNReal.ofReal_sum_of_nonneg
      (s := (Finset.univ : Finset I))
      (f := fun i => ‖f - P i f‖ ^ 2)
      (by intro i hi; positivity)
  calc
    ENNReal.ofReal (variance (f : Joint → ℝ) muPair) =
        ENNReal.ofReal
          (‖f - Lp.const 2 muPair
            (∫ z : Joint, (f : Joint → ℝ) z ∂muPair)‖ ^ 2) := by
      rw [p4Q2DR_actualPairHaarVariance_eq_globalMeanCenteredNormSq H N f]
    _ ≤ ENNReal.ofReal (∑ i : I, ‖f - P i f‖ ^ 2) :=
      ENNReal.ofReal_le_ofReal hDC
    _ = ∑ i : I, ENNReal.ofReal (‖f - P i f‖ ^ 2) := hSum

/-- ACTUAL Wilson 12-color physical Hilbert residual controls the
ACTUAL Wilson probability variance with one uniform-in-F positive
finite-volume coefficient, with no positive-beta commutation assumption.
The coefficient depends on the physical lattice and coupling. -/
theorem p4Q2DR_originalWilsonPhysicalTwelveColor_coercive_bounded :
    ∃ κ : ENNReal, 0 < κ ∧
      ∀ (F : Joint → ℝ), StronglyMeasurable F →
        ∀ (B : ℝ), (∀ z, ‖F z‖ ≤ B) →
          ∀ (f : JH), F =ᵐ[muPair] (f : Joint → ℝ) →
            κ * ENNReal.ofReal (variance F muWilson) ≤
              ENNReal.ofReal
                (p4Q2BC_originalPhysicalTwelveColorResidual
                  H N hN beta hbeta F ‹StronglyMeasurable F›
                  B ‹∀ z, ‖F z‖ ≤ B›) := by
  obtain ⟨m, hm, hReference⟩ :=
    p4Q2DQ_originalWilsonTwelveReference_ge_allCoordinateHilbertDefects
      H N hN beta hbeta
  obtain ⟨mW, M, hmW, hM, hVariance⟩ :=
    p4Q2DF_originalWilsonJoint_allBoundedVariance_uniform_sandwich
      H N hN beta hbeta
  let a : ENNReal := p4Q2DQ_allLinkHilbertFloorCoefficient H beta m
  let b : ENNReal := ENNReal.ofReal (M + 1)
  let κ : ENNReal := a * b⁻¹
  have ha : 0 < a :=
    p4Q2DQ_allLinkHilbertFloorCoefficient_pos H beta m hm
  have hplus : 0 < M + 1 := by linarith
  have hb0 : b ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hplus)
  have hbTop : b ≠ ∞ := ENNReal.ofReal_ne_top
  have hκ : 0 < κ :=
    (ENNReal.mul_pos_iff).2 ⟨ha, ENNReal.inv_pos.mpr hbTop⟩
  refine ⟨κ, hκ, ?_⟩
  intro F hF B hB f hEq
  have hVarianceUpper : variance F muWilson ≤ M * variance F muPair :=
    (hVariance F hF B hB).2
  have hPairNonneg : 0 ≤ variance F muPair :=
    variance_nonneg F muPair
  have hVariancePlus :
      variance F muWilson ≤ (M + 1) * variance F muPair := by
    calc
      variance F muWilson ≤ M * variance F muPair := hVarianceUpper
      _ ≤ M * variance F muPair + variance F muPair :=
        le_add_of_nonneg_right hPairNonneg
      _ = (M + 1) * variance F muPair := by ring
  have hVarianceENN :
      ENNReal.ofReal (variance F muWilson) ≤
        b * ENNReal.ofReal (variance F muPair) := by
    change ENNReal.ofReal (variance F muWilson) ≤
      ENNReal.ofReal (M + 1) * ENNReal.ofReal (variance F muPair)
    calc
      ENNReal.ofReal (variance F muWilson) ≤
        ENNReal.ofReal ((M + 1) * variance F muPair) :=
          ENNReal.ofReal_le_ofReal hVariancePlus
      _ = ENNReal.ofReal (M + 1) *
            ENNReal.ofReal (variance F muPair) :=
          ENNReal.ofReal_mul hplus.le
  have hPairDefects :
      ENNReal.ofReal (variance F muPair) ≤
        ∑ i : I, ENNReal.ofReal (‖f - P i f‖ ^ 2) := by
    calc
      ENNReal.ofReal (variance F muPair) =
        ENNReal.ofReal (variance (f : Joint → ℝ) muPair) :=
          congrArg ENNReal.ofReal (variance_congr hEq)
      _ ≤ ∑ i : I, ENNReal.ofReal (‖f - P i f‖ ^ 2) :=
          p4Q2DR_actualPairHaarVariance_le_allCoordinateENNRealDefects
            H N f
  have hPairReference :
      a * ENNReal.ofReal (variance F muPair) ≤
        p4Q2BC_originalPhysicalTwelveColorHaarReference
          H N hN beta hbeta F := by
    calc
      a * ENNReal.ofReal (variance F muPair) ≤
        a * (∑ i : I, ENNReal.ofReal (‖f - P i f‖ ^ 2)) :=
          mul_le_mul_left hPairDefects a
      _ ≤ p4Q2BC_originalPhysicalTwelveColorHaarReference
            H N hN beta hbeta F :=
        hReference f F hF B hB hEq
  have hCancel :
      κ * (b * ENNReal.ofReal (variance F muPair)) =
        a * ENNReal.ofReal (variance F muPair) := by
    change (a * b⁻¹) * (b * ENNReal.ofReal (variance F muPair)) =
      a * ENNReal.ofReal (variance F muPair)
    calc
      (a * b⁻¹) * (b * ENNReal.ofReal (variance F muPair)) =
        a * ((b⁻¹ * b) * ENNReal.ofReal (variance F muPair)) := by ac_rfl
      _ = a * ENNReal.ofReal (variance F muPair) := by
        rw [ENNReal.inv_mul_cancel hb0 hbTop, one_mul]
  have hRefVariance :
      κ * ENNReal.ofReal (variance F muWilson) ≤
        p4Q2BC_originalPhysicalTwelveColorHaarReference
          H N hN beta hbeta F := by
    calc
      κ * ENNReal.ofReal (variance F muWilson) ≤
        κ * (b * ENNReal.ofReal (variance F muPair)) :=
          mul_le_mul_left hVarianceENN κ
      _ = a * ENNReal.ofReal (variance F muPair) := hCancel
      _ ≤ p4Q2BC_originalPhysicalTwelveColorHaarReference
            H N hN beta hbeta F := hPairReference
  exact hRefVariance.trans
    (p4Q2BC_originalWilsonHaarReference_le_physicalTwelveResidual
      H N hN beta hbeta F hF B hB)

end OriginalWilson
end

end MathlibAnalytic
end MGAP4D
