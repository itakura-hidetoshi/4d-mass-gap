import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFixedWilsonConcreteGroundStateSharpSqrtGapV5_PZ37ALR
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalUniformTopOrthogonalCoercivityV5_PZ37AKL
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalFixedCouplingSchurFrameBridgeV5_PZ37ALK
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTwoSidedTwelveSpatialUniformGap
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateTwelveSpatialPoincareSixSpatialGap
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateSixSpatialFrameGap
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ALS — actual high-temperature six/eight-color frame construction

The original (unmodified) physical Wilson SU(2) one-slab transfer already has
an unconditional volume-independent *small-coupling* conventional twelve-spatial
Poincare inequality on the full top-orthogonal right-boundary lifts.

The existing concrete 6+2 identity temporal-color projections are on the same
ground-state joint Hilbert space as those genuine twelve spatial conditional
expectations. On physical right lifts, all six LEFT spatial updates fix the
vector. This gives the EXACT carrier-safe identities

  E12(R U x) = 1/2 * E6(U x),
  E8(U x)    = 3/4 * E6(U x) = 3/2 * E12(R U x).

Consequently the *certified existing* 1/2304 lower bound for E12 gives the
new actual concrete eight-color frame 1/1536 on the genuine physical K_H,
uniformly in H under the existing chosen high-temperature cutoff.

The original fixed numerical beta0 is ALREADY PROVED *outside* that AKL
cutoff by certified PZ37ALK; no inference at beta0 is made here. The
sharp ALR squared-defect theorem yields, for every finite H and beta
under the same cutoff,

  ||R_H|| <= sqrt(1 - 1/1536),
  gap_H >= 1 - sqrt(1 - 1/1536) > 1/3072.

This is a genuine physical frame construction, NOT merely a new abstract
frame assumption, but its scope is the already-established high-temperature
interval. PZ37ALK already proves the original prescribed numerical beta0 DOES NOT
lie inside that particular high-temperature cutoff. This is an obstruction
to THIS proof route, not a counterexample to an original Wilson gap.

One concrete positive coupling betaSmall <= beta0 is selected before all H
using min(beta0, cutoff/2). This changes NO original beta0 definition;
PZ37ALK proves betaStar < beta0; hence betaSmall = betaStar/2 < beta0.
We also construct the full frame at the stronger certified betaSafe=betaStar.

Only additions, unchanged Wilson SU(2)/Haar/AJA source/root.
All newly introduced declarations are inspected with #print axioms.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace InnerProduct
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace HighTemperatureEightColor

section FinitePhysicalWilson

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "HaarL2" =>
  Lp ℝ 2 (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H N)
local notation "G" =>
  periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule H N
local notation "K" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonal
    H N hN beta hbeta
local notation "U" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabHaarToVacuumL2LinearIsometry
    H N hN beta hbeta
local notation "JRight" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateRightBoundaryLift
    H N hN beta hbeta
local notation "E12" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
    H N hN beta hbeta
local notation "E6" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialResidualEnergy
    H N hN beta hbeta
local notation "P8" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateConcreteEightColorCondExpL2
    H N hN beta hbeta
local notation "E8" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateEightColorResidualEnergy
    H N hN beta hbeta

/-- EXACT normalization bridge, with no gauge/Gibbs carrier identification and
no model-specific estimate beyond the two previously proved identities. -/
theorem p4Q2PZ37ALS_conventionalTwelveFrame_implies_concreteEightFrame
    (κ : ℝ)
    (h12 : ∀ x : K, κ * ‖(x : G)‖ ^ 2 ≤
      E12 (JRight (U ((x : G) : HaarL2)))) :
    ∀ x : K, ((3 / 2 : ℝ) * κ) * ‖(x : G)‖ ^ 2 ≤
      E8 P8 (U ((x : G) : HaarL2)) := by
  intro x
  let u := U ((x : G) : HaarL2)
  have hP : κ * ‖(x : G)‖ ^ 2 ≤ E12 (JRight u) := by
    simpa [u] using h12 x
  have h12Six :
      E12 (JRight u) = (1 / 2 : ℝ) * E6 u :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy_rightBoundary_eq_half_sixSpatial
      H N hN beta hbeta u
  have h8Six :
      E8 P8 u = (3 / 4 : ℝ) * E6 u :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateConcreteEightColorResidual_eq_three_fourths_sixSpatial
      H N hN beta hbeta u
  rw [h12Six] at hP
  have hSix : (2 * κ) * ‖(x : G)‖ ^ 2 ≤ E6 u := by
    nlinarith
  calc
    ((3 / 2 : ℝ) * κ) * ‖(x : G)‖ ^ 2 =
        (3 / 4 : ℝ) * ((2 * κ) * ‖(x : G)‖ ^ 2) := by ring
    _ ≤ (3 / 4 : ℝ) * E6 u :=
      mul_le_mul_of_nonneg_left hSix (by norm_num)
    _ = E8 P8 (U ((x : G) : HaarL2)) := by
      simpa [u] using h8Six.symm

/-- Native physical E8 frame, no hframe premise: all H, N and beta within
the SAME proved volume-independent high-temperature cutoff have 1/1536. -/
theorem p4Q2PZ37ALS_highTemperatureConcreteEightFrame
    (s : ℝ) (hs : 8 < s)
    (hcut : beta ≤
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
        s hs) :
    ∀ x : K, (1 / 1536 : ℝ) * ‖(x : G)‖ ^ 2 ≤
      E8 P8 (U ((x : G) : HaarL2)) := by
  have hframeCut :
      beta ≤ GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialFrameCutoff
        s hs :=
    hcut.trans
      (GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff_le_frameCutoff
        s hs)
  have hκ :
      (1 / 2304 : ℝ) ≤
        GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialRelativeFrameCoefficient
          s beta := by
    simpa [GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformPoincareCoefficient]
      using
        GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformPoincareCoefficient_le_relativeFrameCoefficient
          s hs beta hbeta hcut
  have hPoincare :
      ∀ x : K, (1 / 2304 : ℝ) * ‖(x : G)‖ ^ 2 ≤
        E12 (JRight (U ((x : G) : HaarL2))) := by
    intro x
    have hPoint :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedTwelveSpatialPoincare_on_topOrthogonal
        H N hN beta hbeta s hs hframeCut x
    have hScaled :=
      mul_le_mul_of_nonneg_right hκ (sq_nonneg ‖(x : G)‖)
    exact hScaled.trans hPoint
  have h8 :=
    p4Q2PZ37ALS_conventionalTwelveFrame_implies_concreteEightFrame
      H N hN beta hbeta (1 / 2304 : ℝ) hPoincare
  simpa only [show (3 / 2 : ℝ) * (1 / 2304) = (1 / 1536 : ℝ)
    by norm_num] using h8

/-- Improved sharp gap from the ALR genuine-Wilson squared defect, with
NO assumed 8-color frame on this certified high-temperature interval. -/
theorem p4Q2PZ37ALS_highTemperature_sharpPhysicalGap
    (s : ℝ) (hs : 8 < s)
    (hcut : beta ≤
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
        s hs) :
    1 - Real.sqrt (1 - (1 / 1536 : ℝ)) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
        H N hN beta hbeta := by
  apply GroundStatePosteriorJoint.p4Q2PZ37ALR_concreteFrame_implies_sharpSqrtGap
    H N hN beta hbeta (1 / 1536 : ℝ) (by norm_num) (by norm_num)
  exact p4Q2PZ37ALS_highTemperatureConcreteEightFrame
    H N hN beta hbeta s hs hcut

/-- The actual native-frame gap is strictly above the earlier 1/3072
linear loss bound, with the SAME physical beta and same K_H. -/
theorem p4Q2PZ37ALS_highTemperature_sharpGap_gt_one3072
    (s : ℝ) (hs : 8 < s)
    (hcut : beta ≤
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
        s hs) :
    (1 / 3072 : ℝ) <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
        H N hN beta hbeta := by
  have hgap :=
    p4Q2PZ37ALS_highTemperature_sharpPhysicalGap
      H N hN beta hbeta s hs hcut
  have hstrict :
      (1 / 3072 : ℝ) < 1 - Real.sqrt (1 - (1 / 1536 : ℝ)) := by
    have h := GroundStatePosteriorJoint.p4Q2PZ37ALR_sqrt_gap_strictly_improves_half_linear
      (κ := (1 / 1536 : ℝ)) (by norm_num) (by norm_num)
    norm_num at h ⊢
    exact h
  exact hstrict.trans_le hgap

end FinitePhysicalWilson

/-- One ACTUAL full-top-sector 8-color frame for all volumes at ONE
same coupling; this is a property of unchanged original SU(2) Wilson T. -/
def p4Q2PZ37ALS_hasUniformConcreteEightFrameAt
    (beta : ℝ) (hbeta : 0 ≤ beta) : Prop :=
  PeriodicHypercubicEvenSpecialUnitaryHasUniformGroundStateConcreteEightColorFrame
    (fun H : ℕ => H) 2 (by norm_num)
    (fun _ : ℕ => beta) (fun _ : ℕ => hbeta)

/-- The certified original AKL cutoff produces a uniform concrete frame,
not an abstract uniform frame postulate, for EVERY beta below that cutoff. -/
theorem p4Q2PZ37ALS_originalSU2UniformEightFrame_of_cutoff
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut : beta ≤ p4Q2PZ37AKL_originalUniformCoercivityCutoff) :
    p4Q2PZ37ALS_hasUniformConcreteEightFrameAt beta hbeta := by
  unfold p4Q2PZ37ALS_hasUniformConcreteEightFrameAt
  refine ⟨(1 / 1536 : ℝ), by norm_num, by norm_num, ?_⟩
  intro H x
  exact p4Q2PZ37ALS_highTemperatureConcreteEightFrame
    H 2 (by norm_num) beta hbeta 9 (by norm_num)
    (show beta ≤
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
        9 (by norm_num) from hcut) x

/-- Uniform sharp physical gap at all H, under the EXISTING nonconstructive
AKL cutoff. No claim that original prescribed beta0 belongs to the interval. -/
theorem p4Q2PZ37ALS_originalSU2UniformSharpGap_of_cutoff
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut : beta ≤ p4Q2PZ37AKL_originalUniformCoercivityCutoff) :
    ∀ H : ℕ,
      1 - Real.sqrt (1 - (1 / 1536 : ℝ)) ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
          H 2 (by norm_num) beta hbeta := by
  intro H
  exact p4Q2PZ37ALS_highTemperature_sharpPhysicalGap
    H 2 (by norm_num) beta hbeta 9 (by norm_num)
    (show beta ≤
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
        9 (by norm_num) from hcut)

/-- A selected strictly positive fixed coupling no greater than the ORIGINAL
beta0 but not asserted to equal it. Choice is independent of all H. -/
noncomputable def p4Q2PZ37ALS_smallPositiveCouplingBelowOriginalBeta0 : ℝ :=
  min p4Q2PZ37ADC_fixedCoupling
    (p4Q2PZ37AKL_originalUniformCoercivityCutoff / 2)

theorem p4Q2PZ37ALS_smallPositiveCouplingBelowOriginalBeta0_pos :
    0 < p4Q2PZ37ALS_smallPositiveCouplingBelowOriginalBeta0 := by
  unfold p4Q2PZ37ALS_smallPositiveCouplingBelowOriginalBeta0
  apply lt_min
  · exact p4Q2PZ37ADC_fixedCoupling_pos
  · have h := p4Q2PZ37AKL_originalUniformCoercivityCutoff_pos
    positivity

theorem p4Q2PZ37ALS_smallPositiveCouplingBelowOriginalBeta0_le_original :
    p4Q2PZ37ALS_smallPositiveCouplingBelowOriginalBeta0 ≤
      p4Q2PZ37ADC_fixedCoupling := by
  unfold p4Q2PZ37ALS_smallPositiveCouplingBelowOriginalBeta0
  exact min_le_left _ _

theorem p4Q2PZ37ALS_smallPositiveCouplingBelowOriginalBeta0_le_cutoff :
    p4Q2PZ37ALS_smallPositiveCouplingBelowOriginalBeta0 ≤
      p4Q2PZ37AKL_originalUniformCoercivityCutoff := by
  unfold p4Q2PZ37ALS_smallPositiveCouplingBelowOriginalBeta0
  have hhalf :
      min p4Q2PZ37ADC_fixedCoupling
        (p4Q2PZ37AKL_originalUniformCoercivityCutoff / 2) ≤
          p4Q2PZ37AKL_originalUniformCoercivityCutoff / 2 :=
    min_le_right _ _
  have hCutPos := p4Q2PZ37AKL_originalUniformCoercivityCutoff_pos
  linarith

/-- Nonvacuous original-Wilson positive physical coupling at most beta0;
the 8-color frame is now a PROVED all-H condition for that fixed coupling. -/
theorem p4Q2PZ37ALS_selectedPositiveOriginalSU2HasUniformEightFrame :
    p4Q2PZ37ALS_hasUniformConcreteEightFrameAt
      p4Q2PZ37ALS_smallPositiveCouplingBelowOriginalBeta0
      p4Q2PZ37ALS_smallPositiveCouplingBelowOriginalBeta0_pos.le := by
  exact p4Q2PZ37ALS_originalSU2UniformEightFrame_of_cutoff
    p4Q2PZ37ALS_smallPositiveCouplingBelowOriginalBeta0
    p4Q2PZ37ALS_smallPositiveCouplingBelowOriginalBeta0_pos.le
    p4Q2PZ37ALS_smallPositiveCouplingBelowOriginalBeta0_le_cutoff

/-- Uniform positive and strictly sharpened spectral transfer gap, for a
concrete fixed positive original-Wilson coupling <= beta0 selected before H. -/
theorem p4Q2PZ37ALS_selectedPositiveOriginalSU2UniformSharpGap :
    ∀ H : ℕ,
      1 - Real.sqrt (1 - (1 / 1536 : ℝ)) ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
          H 2 (by norm_num)
          p4Q2PZ37ALS_smallPositiveCouplingBelowOriginalBeta0
          p4Q2PZ37ALS_smallPositiveCouplingBelowOriginalBeta0_pos.le := by
  exact p4Q2PZ37ALS_originalSU2UniformSharpGap_of_cutoff
    p4Q2PZ37ALS_smallPositiveCouplingBelowOriginalBeta0
    p4Q2PZ37ALS_smallPositiveCouplingBelowOriginalBeta0_pos.le
    p4Q2PZ37ALS_smallPositiveCouplingBelowOriginalBeta0_le_cutoff

/-- Exact ORIGINAL prescribed beta0 (unmodified): the only missing input here
is its inclusion in the already-certified high-temperature interval.
This theorem neither asserts nor hides that presently unproved comparison. -/
theorem p4Q2PZ37ALS_originalFixedBeta0UniformSharpGap_if_cutoff
    (hcut : p4Q2PZ37ADC_fixedCoupling ≤
      p4Q2PZ37AKL_originalUniformCoercivityCutoff) :
    ∀ H : ℕ,
      1 - Real.sqrt (1 - (1 / 1536 : ℝ)) ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
          H 2 (by norm_num)
          p4Q2PZ37ADC_fixedCoupling
          p4Q2PZ37ADC_fixedCoupling_pos.le := by
  exact p4Q2PZ37ALS_originalSU2UniformSharpGap_of_cutoff
    p4Q2PZ37ADC_fixedCoupling p4Q2PZ37ADC_fixedCoupling_pos.le hcut


/-- Existing PZ37ALK proves the *actual original prescribed beta0* lies
STRICTLY outside the selected AKL high-temperature interval. -/
theorem p4Q2PZ37ALS_originalBeta0_not_in_AKLHighTemperatureInterval :
    ¬ p4Q2PZ37ADC_fixedCoupling ≤
      p4Q2PZ37AKL_originalUniformCoercivityCutoff :=
  GroundStatePosteriorJoint.p4Q2PZ37ALK_originalFixedCoupling_not_le_AKLcutoff

/-- The auxiliary selected betaSmall is provably exactly betaStar/2,
not the prescribed beta0; no unproved numerical comparison remains. -/
theorem p4Q2PZ37ALS_smallPositiveCoupling_eq_half_AKLcutoff :
    p4Q2PZ37ALS_smallPositiveCouplingBelowOriginalBeta0 =
      p4Q2PZ37AKL_originalUniformCoercivityCutoff / 2 := by
  unfold p4Q2PZ37ALS_smallPositiveCouplingBelowOriginalBeta0
  apply min_eq_right
  have hCut := p4Q2PZ37AKL_originalUniformCoercivityCutoff_pos
  have hBound :=
    GroundStatePosteriorJoint.p4Q2PZ37ALK_AKLuniformCutoff_lt_originalFixedCoupling
  linarith

theorem p4Q2PZ37ALS_smallPositiveCoupling_strictly_lt_originalBeta0 :
    p4Q2PZ37ALS_smallPositiveCouplingBelowOriginalBeta0 <
      p4Q2PZ37ADC_fixedCoupling := by
  exact lt_of_le_of_lt
    p4Q2PZ37ALS_smallPositiveCouplingBelowOriginalBeta0_le_cutoff
    GroundStatePosteriorJoint.p4Q2PZ37ALK_AKLuniformCutoff_lt_originalFixedCoupling

/-- The *maximal currently selected* safe physical coupling betaSafe of ALK
has an unconditionally constructed concrete eight-color frame, at every H.
It is exactly betaStar, strictly smaller than original beta0. -/
theorem p4Q2PZ37ALS_existingALKSafeCoupling_hasUniformConcreteEightFrame :
    p4Q2PZ37ALS_hasUniformConcreteEightFrameAt
      GroundStatePosteriorJoint.p4Q2PZ37ALK_originalFixedCouplingUniformClip
      GroundStatePosteriorJoint.p4Q2PZ37ALK_originalFixedCouplingUniformClip_pos.le := by
  exact p4Q2PZ37ALS_originalSU2UniformEightFrame_of_cutoff
    GroundStatePosteriorJoint.p4Q2PZ37ALK_originalFixedCouplingUniformClip
    GroundStatePosteriorJoint.p4Q2PZ37ALK_originalFixedCouplingUniformClip_pos.le
    GroundStatePosteriorJoint.p4Q2PZ37ALK_originalFixedCouplingUniformClip_le_cutoff

/-- The SAME exact ALK safe coupling, not betaSmall or beta0, carries an
unconditional physical SU(2) all-H sharp sqrt gap. -/
theorem p4Q2PZ37ALS_existingALKSafeCoupling_uniformSharpGap :
    ∀ H : ℕ,
      1 - Real.sqrt (1 - (1 / 1536 : ℝ)) ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
          H 2 (by norm_num)
          GroundStatePosteriorJoint.p4Q2PZ37ALK_originalFixedCouplingUniformClip
          GroundStatePosteriorJoint.p4Q2PZ37ALK_originalFixedCouplingUniformClip_pos.le := by
  exact p4Q2PZ37ALS_originalSU2UniformSharpGap_of_cutoff
    GroundStatePosteriorJoint.p4Q2PZ37ALK_originalFixedCouplingUniformClip
    GroundStatePosteriorJoint.p4Q2PZ37ALK_originalFixedCouplingUniformClip_pos.le
    GroundStatePosteriorJoint.p4Q2PZ37ALK_originalFixedCouplingUniformClip_le_cutoff

end HighTemperatureEightColor
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.HighTemperatureEightColor.p4Q2PZ37ALS_conventionalTwelveFrame_implies_concreteEightFrame
#print axioms MGAP4D.MathlibAnalytic.HighTemperatureEightColor.p4Q2PZ37ALS_highTemperatureConcreteEightFrame
#print axioms MGAP4D.MathlibAnalytic.HighTemperatureEightColor.p4Q2PZ37ALS_highTemperature_sharpPhysicalGap
#print axioms MGAP4D.MathlibAnalytic.HighTemperatureEightColor.p4Q2PZ37ALS_highTemperature_sharpGap_gt_one3072
#print axioms MGAP4D.MathlibAnalytic.HighTemperatureEightColor.p4Q2PZ37ALS_hasUniformConcreteEightFrameAt
#print axioms MGAP4D.MathlibAnalytic.HighTemperatureEightColor.p4Q2PZ37ALS_originalSU2UniformEightFrame_of_cutoff
#print axioms MGAP4D.MathlibAnalytic.HighTemperatureEightColor.p4Q2PZ37ALS_originalSU2UniformSharpGap_of_cutoff
#print axioms MGAP4D.MathlibAnalytic.HighTemperatureEightColor.p4Q2PZ37ALS_smallPositiveCouplingBelowOriginalBeta0
#print axioms MGAP4D.MathlibAnalytic.HighTemperatureEightColor.p4Q2PZ37ALS_smallPositiveCouplingBelowOriginalBeta0_pos
#print axioms MGAP4D.MathlibAnalytic.HighTemperatureEightColor.p4Q2PZ37ALS_smallPositiveCouplingBelowOriginalBeta0_le_original
#print axioms MGAP4D.MathlibAnalytic.HighTemperatureEightColor.p4Q2PZ37ALS_smallPositiveCouplingBelowOriginalBeta0_le_cutoff
#print axioms MGAP4D.MathlibAnalytic.HighTemperatureEightColor.p4Q2PZ37ALS_selectedPositiveOriginalSU2HasUniformEightFrame
#print axioms MGAP4D.MathlibAnalytic.HighTemperatureEightColor.p4Q2PZ37ALS_selectedPositiveOriginalSU2UniformSharpGap
#print axioms MGAP4D.MathlibAnalytic.HighTemperatureEightColor.p4Q2PZ37ALS_originalFixedBeta0UniformSharpGap_if_cutoff

#print axioms MGAP4D.MathlibAnalytic.HighTemperatureEightColor.p4Q2PZ37ALS_originalBeta0_not_in_AKLHighTemperatureInterval
#print axioms MGAP4D.MathlibAnalytic.HighTemperatureEightColor.p4Q2PZ37ALS_smallPositiveCoupling_eq_half_AKLcutoff
#print axioms MGAP4D.MathlibAnalytic.HighTemperatureEightColor.p4Q2PZ37ALS_smallPositiveCoupling_strictly_lt_originalBeta0
#print axioms MGAP4D.MathlibAnalytic.HighTemperatureEightColor.p4Q2PZ37ALS_existingALKSafeCoupling_hasUniformConcreteEightFrame
#print axioms MGAP4D.MathlibAnalytic.HighTemperatureEightColor.p4Q2PZ37ALS_existingALKSafeCoupling_uniformSharpGap
