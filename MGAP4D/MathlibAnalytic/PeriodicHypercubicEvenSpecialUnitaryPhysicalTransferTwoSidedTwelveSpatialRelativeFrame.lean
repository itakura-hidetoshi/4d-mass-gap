import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTwoSidedCompleteOrderConstantLineConvergence
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTwoSidedTwelveSpatialGroupedLinkSweep
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointLeftSixSpatialSwapDisplacement
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferWilsonGroundStateTwelveSpatialPoincareSixSpatialGap
import MGAP4D.MathlibAnalytic.RealHilbertGroupedProjectionSweep
import Mathlib.Tactic

/-!
# Volume-free genuine two-sided twelve-spatial relative frame

This is G1.

The complete tagged right/left one-link carrier is grouped into the fixed
twelve canonical spatial colors constructed in #4977.  The grouped order is
kept literally; no permutation of noncommuting projections is used.

Inputs:

* #4976/#4978: every complete duplicate-free tagged-link order contracts
  constant-centered squared norm by the two-boundary loss ratio;
* #4943: each whole right spatial-color sweep has a volume-free displacement
  bound by its color residual;
* #4979: endpoint swap transports that whole-color estimate to the left six
  colors with exactly the same coefficient.

The only Cauchy--Schwarz step is over the fixed twelve-color type.  Therefore
the resulting coefficient has no lattice-link, volume, or rank factor.

For a conservative coefficient we only use that the one-sided square-root loss
ratio is < 1, so each group displacement costs at most twice its color residual.
This avoids any unproved identification between the one-sided and two-sided
Schur coefficients.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators InnerProductSpace InnerProduct

noncomputable section

set_option maxHeartbeats 2000000

local instance twoSidedTwelveSpatialRelativeFrameSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance twoSidedTwelveSpatialRelativeFrameSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance twoSidedTwelveSpatialRelativeFrameSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance twoSidedTwelveSpatialRelativeFrameSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance twoSidedTwelveSpatialRelativeFrameSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance twoSidedTwelveSpatialRelativeFrameSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance twoSidedTwelveSpatialRelativeFrameConstantLineHasOrthogonalProjection
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
      H N hN beta hbeta).HasOrthogonalProjection := by
  let C :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
      H N hN beta hbeta
  change C.HasOrthogonalProjection
  letI : FiniteDimensional ℝ C := by
    unfold C
    unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantLine
    infer_instance
  letI : CompleteSpace C := FiniteDimensional.complete ℝ C
  exact Submodule.HasOrthogonalProjection.ofCompleteSpace C

namespace GroundStateSourceFixedPairEnergy

/-- Common positive interval on which both the one-sided whole-color
displacement estimate and the genuine two-sided complete-order contraction are
available.  Both constituent cutoffs are already volume/rank independent. -/
def twoSidedTwelveSpatialFrameCutoff
    (s : ℝ) (hs : 8 < s) : ℝ :=
  min
    (twoBoundaryOrderedLossContractionCutoff s hs)
    (jointLeakageLossContractionCutoff s hs)

theorem twoSidedTwelveSpatialFrameCutoff_pos
    (s : ℝ) (hs : 8 < s) :
    0 < twoSidedTwelveSpatialFrameCutoff s hs := by
  unfold twoSidedTwelveSpatialFrameCutoff
  exact lt_min
    (twoBoundaryOrderedLossContractionCutoff_pos s hs)
    (jointLeakageLossContractionCutoff_pos s hs)

theorem twoSidedTwelveSpatialFrameCutoff_le_twoBoundary
    (s : ℝ) (hs : 8 < s) :
    twoSidedTwelveSpatialFrameCutoff s hs ≤
      twoBoundaryOrderedLossContractionCutoff s hs := by
  unfold twoSidedTwelveSpatialFrameCutoff
  exact min_le_left _ _

theorem twoSidedTwelveSpatialFrameCutoff_le_jointLeakage
    (s : ℝ) (hs : 8 < s) :
    twoSidedTwelveSpatialFrameCutoff s hs ≤
      jointLeakageLossContractionCutoff s hs := by
  unfold twoSidedTwelveSpatialFrameCutoff
  exact min_le_right _ _

/-- Conservative volume-free twelve-color relative-frame coefficient.
The factor 576 = 4 * 12^2 consists only of the fixed factor two used to bound
one whole-color displacement and fixed twelve-color Cauchy--Schwarz. -/
def twoSidedTwelveSpatialRelativeFrameCoefficient
    (s beta : ℝ) : ℝ :=
  (1 - Real.sqrt (twoBoundaryOrderedLossRatio s beta)) ^ 2 / 576

theorem twoSidedTwelveSpatialRelativeFrameCoefficient_pos
    (s : ℝ) (hs : 8 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut : beta ≤ twoSidedTwelveSpatialFrameCutoff s hs) :
    0 < twoSidedTwelveSpatialRelativeFrameCoefficient s beta := by
  have hcutTwo :
      beta ≤ twoBoundaryOrderedLossContractionCutoff s hs :=
    hcut.trans (twoSidedTwelveSpatialFrameCutoff_le_twoBoundary s hs)
  have hEta :=
    twoBoundaryOrderedLossRatio_nonneg_lt_one
      s hs beta hbeta hcutTwo
  let r := Real.sqrt (twoBoundaryOrderedLossRatio s beta)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrSq : r ^ 2 = twoBoundaryOrderedLossRatio s beta := by
    dsimp [r]
    exact Real.sq_sqrt hEta.1
  have hr1 : r < 1 := by
    nlinarith
  unfold twoSidedTwelveSpatialRelativeFrameCoefficient
  have hnum : 0 < (1 - Real.sqrt (twoBoundaryOrderedLossRatio s beta)) ^ 2 := by
    exact sq_pos_of_pos (by simpa [r] using sub_pos.mpr hr1)
  exact div_pos hnum (by norm_num)

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

abbrev TwoSidedLink :=
  PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H

abbrev TwoSidedColor :=
  PeriodicHypercubicEvenGroundStateTwoSidedSpatialColor

abbrev JL2 :=
  PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
    H N hN beta hbeta

local notation "PLink" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
    H N hN beta hbeta

local notation "P12" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialCondExpL2
    H N hN beta hbeta

local notation "Bconst" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection
    H N hN beta hbeta

local notation "E12" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy
    H N hN beta hbeta

private theorem twoSidedSpatialLink_projection_norm_le
    (e : TwoSidedLink H) (f : JL2 H N hN beta hbeta) :
    ‖PLink e f‖ ≤ ‖f‖ := by
  have hResidual :=
    realHilbertProjection_residual_norm_sq
      (PLink e)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2_idempotent
        H N hN beta hbeta e)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2_symmetric
        H N hN beta hbeta e)
      f
  have hSquare : ‖PLink e f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    nlinarith [sq_nonneg ‖f - PLink e f‖]
  exact
    (sq_le_sq₀ (norm_nonneg (PLink e f)) (norm_nonneg f)).mp hSquare

/-- G1: volume-free normalized genuine two-sided twelve-spatial relative
Poincare inequality around the intrinsic joint constant line.

The only finite-cardinality loss is the fixed twelve-color Cauchy--Schwarz
factor.  In particular there is no dependence on the number of lattice links,
finite volume, or gauge rank. -/
theorem twoSidedTwelveSpatial_ordered_relativePoincare
    (s : ℝ) (hs : 8 < s)
    (hcut : beta ≤ twoSidedTwelveSpatialFrameCutoff s hs)
    (f : JL2 H N hN beta hbeta) :
    twoSidedTwelveSpatialRelativeFrameCoefficient s beta *
        ‖f - Bconst f‖ ^ 2 ≤
      E12 f := by
  classical
  have hcutTwo :
      beta ≤ twoBoundaryOrderedLossContractionCutoff s hs :=
    hcut.trans (twoSidedTwelveSpatialFrameCutoff_le_twoBoundary s hs)
  have hcutOne :
      beta ≤ jointLeakageLossContractionCutoff s hs :=
    hcut.trans (twoSidedTwelveSpatialFrameCutoff_le_jointLeakage s hs)
  let eta2 := twoBoundaryOrderedLossRatio s beta
  let eta1 := jointLeakageLossRatio s beta
  let r2 := Real.sqrt eta2
  let r1 := Real.sqrt eta1
  let V := ‖f - Bconst f‖
  let colors : List (TwoSidedColor) :=
    (Finset.univ : Finset (TwoSidedColor)).toList
  let groups : TwoSidedColor → List (TwoSidedLink H) :=
    twoSidedTwelveSpatialColorLinkList H
  let T : TwoSidedColor → JL2 H N hN beta hbeta →L[ℝ] JL2 H N hN beta hbeta :=
    fun c => realHilbertProjectionSweep PLink (groups c)
  let sources : List (TwoSidedLink H) :=
    twoSidedTwelveSpatialGroupedLinkList H
  let S : JL2 H N hN beta hbeta →L[ℝ] JL2 H N hN beta hbeta :=
    realHilbertProjectionSweep PLink sources
  let a : TwoSidedColor → ℝ :=
    fun c => ‖f - P12 c f‖
  let A := ∑ c : TwoSidedColor, a c
  have hEta2 : 0 ≤ eta2 ∧ eta2 < 1 := by
    simpa [eta2] using
      twoBoundaryOrderedLossRatio_nonneg_lt_one
        s hs beta hbeta hcutTwo
  have hEta1 : 0 ≤ eta1 ∧ eta1 < 1 := by
    simpa [eta1] using
      jointLeakageLossRatio_nonneg_lt_one
        s hs beta hbeta hcutOne
  have hr20 : 0 ≤ r2 := Real.sqrt_nonneg _
  have hr10 : 0 ≤ r1 := Real.sqrt_nonneg _
  have hr2Sq : r2 ^ 2 = eta2 := by
    dsimp [r2]
    exact Real.sq_sqrt (twoBoundaryOrderedLossRatio_nonneg s beta)
  have hr1Sq : r1 ^ 2 = eta1 := by
    dsimp [r1]
    exact Real.sq_sqrt (jointLeakageLossRatio_nonneg s beta)
  have hr2lt : r2 < 1 := by
    nlinarith [hEta2.2, hr2Sq]
  have hr1lt : r1 < 1 := by
    nlinarith [hEta1.2, hr1Sq]
  have hV0 : 0 ≤ V := norm_nonneg _
  have hA0 : 0 ≤ A :=
    Finset.sum_nonneg (fun c _ => norm_nonneg _)
  have hFull :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_constantVariance_le_lossRatio_mul_of_completeOrder
      H N hN s hs beta hbeta hcutTwo
      sources
      (by
        simpa [sources] using
          twoSidedTwelveSpatialGroupedLinkList_nodup H)
      (by
        intro e
        simpa [sources] using
          twoSidedTwelveSpatialGroupedLinkList_complete H e)
      f
  have hAbsorb :
      Bconst (S f) = Bconst f := by
    simpa [S, sources] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointConstantProjection_absorb_twoSidedSpatialLinkOrder
        H N hN beta hbeta sources f
  have hFull' :
      ‖S f - Bconst f‖ ^ 2 ≤ eta2 * V ^ 2 := by
    simpa [S, sources, eta2, V, hAbsorb] using hFull
  have hTailSquare :
      ‖S f - Bconst f‖ ^ 2 ≤ (r2 * V) ^ 2 := by
    rw [mul_pow, hr2Sq]
    exact hFull'
  have hTail :
      ‖S f - Bconst f‖ ≤ r2 * V :=
    (sq_le_sq₀
      (norm_nonneg _)
      (mul_nonneg hr20 hV0)).mp hTailSquare
  have hT :
      ∀ c x, ‖T c x‖ ≤ ‖x‖ := by
    intro c x
    exact
      GroupedProjectionSweep.norm_le
        PLink
        (twoSidedSpatialLink_projection_norm_le H N hN beta hbeta)
        (groups c) x
  have hGroupIdentity :
      S f = realHilbertProjectionSweep T colors f := by
    simpa [S, sources, T, groups, colors] using
      twoSidedTwelveSpatialGroupedLinkList_sweep_eq_groupSweep
        H N hN beta hbeta f
  have hTelescope :
      ‖f - S f‖ ≤
        ∑ c : TwoSidedColor, ‖f - T c f‖ := by
    rw [hGroupIdentity]
    simpa only [colors, Finset.sum_map_toList] using
      GroupedProjectionSweep.displacement_le_sum_initial
        T hT colors f
  have hGroupBound :
      ∀ c : TwoSidedColor,
        ‖f - T c f‖ ≤ (1 + r1) * a c := by
    intro c
    cases c with
    | inl c =>
        have h :=
          fixedColor_sweep_displacement_le_one_add_sqrt_lossRatio_mul_colorResidual
            H N hN beta hbeta s hs hcutOne
            (periodicHypercubicEvenGroundStateSpatialColorEquivFin.symm c) f
        have hSweep :=
          twoSidedTwelveSpatialColorLinkList_right_sweep_eq
            H N hN beta hbeta c f
        change
          ‖f -
              realHilbertProjectionSweep PLink
                (twoSidedTwelveSpatialColorLinkList H (Sum.inl c)) f‖ ≤
            (1 + r1) *
              ‖f -
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2
                  H N hN beta hbeta c f‖
        rw [hSweep]
        simpa [
          r1, eta1,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialCondExpL2] using h
    | inr c =>
        have h :=
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftFixedColor_sweep_displacement_le_one_add_sqrt_lossRatio_mul_colorResidual
            H N hN beta hbeta s hs hcutOne c f
        have hSweep :=
          twoSidedTwelveSpatialColorLinkList_left_sweep_eq
            H N hN beta hbeta c f
        change
          ‖f -
              realHilbertProjectionSweep PLink
                (twoSidedTwelveSpatialColorLinkList H (Sum.inr c)) f‖ ≤
            (1 + r1) *
              ‖f -
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixSpatialCondExpL2
                  H N hN beta hbeta c f‖
        rw [hSweep]
        simpa [
          r1, eta1,
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateLeftSixSpatialCondExpL2] using h
  have hDisplacement :
      ‖f - S f‖ ≤ (1 + r1) * A := by
    calc
      ‖f - S f‖ ≤
          ∑ c : TwoSidedColor, ‖f - T c f‖ :=
        hTelescope
      _ ≤
          ∑ c : TwoSidedColor, (1 + r1) * a c :=
        Finset.sum_le_sum (fun c _ => hGroupBound c)
      _ = (1 + r1) * A := by
        rw [← Finset.mul_sum]
  have hTriangle :
      V ≤ ‖f - S f‖ + ‖S f - Bconst f‖ := by
    simpa only [V, dist_eq_norm] using
      dist_triangle f (S f) (Bconst f)
  have hRelative :
      (1 - r2) * V ≤ (1 + r1) * A := by
    nlinarith [hTriangle, hDisplacement, hTail]
  have hOnePlus : 1 + r1 ≤ 2 := by
    linarith
  have hGroupFactor :
      (1 + r1) * A ≤ 2 * A :=
    mul_le_mul_of_nonneg_right hOnePlus hA0
  have hLinear :
      (1 - r2) * V ≤ 2 * A :=
    hRelative.trans hGroupFactor
  have hCoeff0 : 0 ≤ 1 - r2 := by
    linarith
  have hSquare :
      ((1 - r2) * V) ^ 2 ≤ (2 * A) ^ 2 :=
    (sq_le_sq₀
      (mul_nonneg hCoeff0 hV0)
      (mul_nonneg (by norm_num) hA0)).mpr hLinear
  have hCauchy :
      A ^ 2 ≤
        12 * ∑ c : TwoSidedColor, a c ^ 2 := by
    simpa [
      A,
      periodicHypercubicEvenGroundStateTwoSidedSpatialColor_card] using
      Finset.sum_mul_sq_le_sq_mul_sq
        (Finset.univ : Finset (TwoSidedColor))
        (fun _ => (1 : ℝ)) a
  have hEnergy :
      E12 f =
        (1 / 12 : ℝ) *
          ∑ c : TwoSidedColor, a c ^ 2 := by
    simp only [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwelveSpatialResidualEnergy,
      groundStateJointColorNormalizedResidualEnergy,
      periodicHypercubicEvenGroundStateTwoSidedSpatialColor_card,
      one_div,
      a]
    norm_num
  rw [hEnergy]
  unfold twoSidedTwelveSpatialRelativeFrameCoefficient
  change
    ((1 - r2) ^ 2 / 576) * V ^ 2 ≤
      (1 / 12 : ℝ) *
        ∑ c : TwoSidedColor, a c ^ 2
  rw [mul_pow] at hSquare
  have hCombined :
      (1 - r2) ^ 2 * V ^ 2 ≤
        48 * ∑ c : TwoSidedColor, a c ^ 2 := by
    nlinarith [hSquare, hCauchy]
  nlinarith [hCombined]

end GroundStateSourceFixedPairEnergy

end

end MathlibAnalytic
end MGAP4D
