import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTwoSidedTwelveSpatialPhysicalTopOrthogonalGap
import Mathlib.Tactic

/-!
# Scale-uniform positive-beta twelve-spatial transfer gap

PR #4981 closes the finite-volume physical transfer gap on the positive
volume/rank-independent G1 interval.  Positivity at each beta is not yet by
itself a single scale-independent numerical lower bound.

This file closes G4 by shrinking the already-positive interval once more,
still independently of lattice volume and gauge rank.  Continuity at beta=0
gives a cutoff on which the two-boundary Schur coefficient satisfies

  Q(s,beta) < 1/3.

Since Q >= 0 there,

  sqrt(eta) = Q / (1-Q) < 1/2,

so the #4980 twelve-spatial coefficient obeys the explicit common bound

  1/2304 <= kappa_12(s,beta).

Consequently every finite scale has the common physical transfer-gap lower
bound

  1/3072 <= gap_n,

and the repository's existing scale-uniform twelve-spatial receiver applies
directly.

No lattice-volume, link-count, rank, or scale dependent coefficient appears.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set Filter
open scoped InnerProductSpace InnerProduct BigOperators

noncomputable section

namespace GroundStateSourceFixedPairEnergy

local notation "crossCoefficient" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient

private theorem twoSidedTwelveUniformContinuousAt_crossCoefficient :
    ContinuousAt crossCoefficient 0 := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
  have hExp : ContinuousAt (fun beta : ℝ => Real.exp (8 * beta)) 0 := by
    fun_prop
  have hDen :
      (Real.exp (8 * (0 : ℝ))) ^ 2 + 1 ≠ 0 := by
    norm_num
  exact
    continuousAt_const.mul
      (((hExp.pow 2).sub continuousAt_const).div
        ((hExp.pow 2).add continuousAt_const) hDen)

/-- A strictly positive volume/rank-independent subinterval of the G1 frame
interval on which the two-boundary Schur coefficient is uniformly below one
third. -/
theorem exists_twoSidedTwelveSpatialUniformGapCutoff
    (s : ℝ) (hs : 8 < s) :
    ∃ cutoff : ℝ,
      0 < cutoff ∧
      cutoff ≤ twoSidedTwelveSpatialFrameCutoff s hs ∧
      ∀ beta : ℝ, 0 ≤ beta → beta ≤ cutoff →
        twoBoundaryOrderedSchurCoefficient s beta < 1 / 3 := by
  let qReal : ℝ → ℝ := fun beta =>
    jointLeakageRMSMultiplierRealFormula s beta *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCoefficient
        s beta
  let totalReal : ℝ → ℝ := fun beta => qReal beta + crossCoefficient beta
  have hQContinuous : ContinuousAt qReal 0 :=
    (continuousAt_jointLeakageRMSMultiplierRealFormula s).mul
      (continuousAt_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCoefficient
        s)
  have hContinuous : ContinuousAt totalReal 0 :=
    hQContinuous.add twoSidedTwelveUniformContinuousAt_crossCoefficient
  rw [Metric.continuousAt_iff] at hContinuous
  obtain ⟨delta, hDelta, hControl⟩ :=
    hContinuous (1 / 3) (by norm_num)
  let cutoff :=
    min (delta / 2) (twoSidedTwelveSpatialFrameCutoff s hs)
  have hPos : 0 < cutoff := by
    dsimp [cutoff]
    exact lt_min
      (by positivity)
      (twoSidedTwelveSpatialFrameCutoff_pos s hs)
  have hFrame :
      cutoff ≤ twoSidedTwelveSpatialFrameCutoff s hs := by
    dsimp [cutoff]
    exact min_le_right _ _
  refine ⟨cutoff, hPos, hFrame, ?_⟩
  intro beta hbeta hbetaCut
  have hHalf : beta ≤ delta / 2 := by
    exact hbetaCut.trans (by
      dsimp [cutoff]
      exact min_le_left _ _)
  have hDistance : dist beta 0 < delta := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hbeta]
    linarith
  have hAbs : |totalReal beta - totalReal 0| < 1 / 3 := by
    simpa only [Real.dist_eq] using hControl hDistance
  have hUpper : totalReal beta - totalReal 0 < 1 / 3 :=
    lt_of_le_of_lt (le_abs_self _) hAbs
  have hZero : totalReal 0 = 0 := by
    simp [
      totalReal, qReal,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient]
  rw [hZero, sub_zero] at hUpper
  have hFrameBeta :
      beta ≤ twoSidedTwelveSpatialFrameCutoff s hs :=
    hbetaCut.trans hFrame
  have hTwo :
      beta ≤ twoBoundaryOrderedLossContractionCutoff s hs :=
    hFrameBeta.trans
      (twoSidedTwelveSpatialFrameCutoff_le_twoBoundary s hs)
  have hSchur :
      beta ≤ twoBoundaryOrderedSchurCutoff s hs :=
    hTwo.trans
      (twoBoundaryOrderedLossContractionCutoff_le_schurCutoff s hs)
  have hJoint :
      beta ≤ jointLeakageSchurCutoff s hs :=
    hSchur.trans
      (twoBoundaryOrderedSchurCutoff_le_jointLeakageSchurCutoff s hs)
  have hStrict :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s :=
    hJoint.trans
      (jointLeakageSchurCutoff_le_strictPhysicalSweepCutoff s hs)
  simpa only [
    totalReal, qReal, twoBoundaryOrderedSchurCoefficient,
    jointLeakageSchurCoefficient,
    jointLeakageRMSMultiplier_eq_realFormula s beta hbeta hStrict] using
    hUpper

/-- Chosen scale-uniform high-temperature cutoff for the final finite-volume
physical gap package. -/
def twoSidedTwelveSpatialUniformGapCutoff
    (s : ℝ) (hs : 8 < s) : ℝ :=
  Classical.choose (exists_twoSidedTwelveSpatialUniformGapCutoff s hs)

theorem twoSidedTwelveSpatialUniformGapCutoff_pos
    (s : ℝ) (hs : 8 < s) :
    0 < twoSidedTwelveSpatialUniformGapCutoff s hs :=
  (Classical.choose_spec
    (exists_twoSidedTwelveSpatialUniformGapCutoff s hs)).1

theorem twoSidedTwelveSpatialUniformGapCutoff_le_frameCutoff
    (s : ℝ) (hs : 8 < s) :
    twoSidedTwelveSpatialUniformGapCutoff s hs ≤
      twoSidedTwelveSpatialFrameCutoff s hs :=
  (Classical.choose_spec
    (exists_twoSidedTwelveSpatialUniformGapCutoff s hs)).2.1

theorem twoBoundaryOrderedSchurCoefficient_lt_third_of_le_uniformGapCutoff
    (s : ℝ) (hs : 8 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut : beta ≤ twoSidedTwelveSpatialUniformGapCutoff s hs) :
    twoBoundaryOrderedSchurCoefficient s beta < 1 / 3 :=
  (Classical.choose_spec
    (exists_twoSidedTwelveSpatialUniformGapCutoff s hs)).2.2
      beta hbeta hcut

/-- Explicit common conventional twelve-spatial Poincare coefficient. -/
def twoSidedTwelveSpatialUniformPoincareCoefficient : ℝ :=
  1 / 2304

theorem twoSidedTwelveSpatialUniformPoincareCoefficient_pos :
    0 < twoSidedTwelveSpatialUniformPoincareCoefficient := by
  norm_num [twoSidedTwelveSpatialUniformPoincareCoefficient]

theorem twoSidedTwelveSpatialUniformPoincareCoefficient_le_half :
    twoSidedTwelveSpatialUniformPoincareCoefficient ≤ 1 / 2 := by
  norm_num [twoSidedTwelveSpatialUniformPoincareCoefficient]

/-- On the stricter common cutoff, the pointwise G1 coefficient is bounded
below by the explicit scale-independent value 1/2304. -/
theorem twoSidedTwelveSpatialUniformPoincareCoefficient_le_relativeFrameCoefficient
    (s : ℝ) (hs : 8 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut : beta ≤ twoSidedTwelveSpatialUniformGapCutoff s hs) :
    twoSidedTwelveSpatialUniformPoincareCoefficient ≤
      twoSidedTwelveSpatialRelativeFrameCoefficient s beta := by
  have hFrame :
      beta ≤ twoSidedTwelveSpatialFrameCutoff s hs :=
    hcut.trans
      (twoSidedTwelveSpatialUniformGapCutoff_le_frameCutoff s hs)
  have hTwo :
      beta ≤ twoBoundaryOrderedLossContractionCutoff s hs :=
    hFrame.trans
      (twoSidedTwelveSpatialFrameCutoff_le_twoBoundary s hs)
  have hQ :=
    twoBoundaryOrderedSchurCoefficient_nonneg_lt_half
      s hs beta hbeta hTwo
  have hQThird :=
    twoBoundaryOrderedSchurCoefficient_lt_third_of_le_uniformGapCutoff
      s hs beta hbeta hcut
  let q := twoBoundaryOrderedSchurCoefficient s beta
  have hDen : 0 < 1 - q := by
    dsimp [q]
    linarith [hQThird]
  have hRatio0 : 0 ≤ q / (1 - q) := by
    exact div_nonneg hQ.1 hDen.le
  have hRatioHalf : q / (1 - q) < 1 / 2 := by
    apply (div_lt_iff₀ hDen).2
    dsimp [q] at hQThird ⊢
    nlinarith
  have hSqrt :
      Real.sqrt (twoBoundaryOrderedLossRatio s beta) =
        q / (1 - q) := by
    rw [twoBoundaryOrderedLossRatio]
    exact Real.sqrt_sq hRatio0
  have hOneMinus :
      1 / 2 < 1 - Real.sqrt (twoBoundaryOrderedLossRatio s beta) := by
    rw [hSqrt]
    linarith
  have hSquare :
      1 / 4 <
        (1 - Real.sqrt (twoBoundaryOrderedLossRatio s beta)) ^ 2 := by
    nlinarith
  unfold
    twoSidedTwelveSpatialUniformPoincareCoefficient
    twoSidedTwelveSpatialRelativeFrameCoefficient
  nlinarith

end GroundStateSourceFixedPairEnergy

section ScalingFamily

variable
    (halfExtent : ℕ → ℕ)
    (N : ℕ) (hN : 0 < N)
    (beta : ℕ → ℝ) (hbeta : ∀ n, 0 ≤ beta n)

/-- G4 quantitative frame package: one explicit positive conventional
twelve-spatial Poincare coefficient works at every scale whenever the whole
beta family lies in the common certified interval. -/
theorem
    periodicHypercubicEvenSpecialUnitary_hasUniformGroundStateTwelveSpatialPoincareOnPhysicalRightLifts_of_uniformGapCutoff
    (s : ℝ) (hs : 8 < s)
    (hcut :
      ∀ n : ℕ,
        beta n ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
            s hs) :
    PeriodicHypercubicEvenSpecialUnitaryHasUniformGroundStateTwelveSpatialPoincareOnPhysicalRightLifts
      halfExtent N hN beta hbeta := by
  let kappa :=
    GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformPoincareCoefficient
  refine ⟨
    kappa,
    GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformPoincareCoefficient_pos,
    GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformPoincareCoefficient_le_half,
    ?_⟩
  intro n x
  have hFrameCut :
      beta n ≤
        GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialFrameCutoff
          s hs :=
    (hcut n).trans
      (GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff_le_frameCutoff
        s hs)
  have hPoint :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedTwelveSpatialPoincare_on_topOrthogonal
      (halfExtent n) N hN (beta n) (hbeta n)
      s hs hFrameCut x
  have hkappa :
      kappa ≤
        GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialRelativeFrameCoefficient
          s (beta n) := by
    dsimp [kappa]
    exact
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformPoincareCoefficient_le_relativeFrameCoefficient
        s hs (beta n) (hbeta n) (hcut n)
  have hNorm0 :
      0 ≤
        ‖(x :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
            (halfExtent n) N)‖ ^ 2 :=
    sq_nonneg _
  calc
    kappa *
        ‖(x :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
            (halfExtent n) N)‖ ^ 2 ≤
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialRelativeFrameCoefficient
          s (beta n) *
        ‖(x :
          periodicHypercubicEvenSpecialUnitarySpatialSliceGaugeInvariantL2Submodule
            (halfExtent n) N)‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hkappa hNorm0
    _ ≤ _ := hPoint

/-- G4 closes the repository's existing scale-uniform physical transfer-gap
target by feeding the explicit common twelve-spatial Poincare package to the
already-proved receiver. -/
theorem
    periodicHypercubicEvenSpecialUnitary_hasUniformTopEigenspaceTransferGap_of_twoSidedTwelveSpatialUniformGapCutoff
    (s : ℝ) (hs : 8 < s)
    (hcut :
      ∀ n : ℕ,
        beta n ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
            s hs) :
    PeriodicHypercubicEvenSpecialUnitaryHasUniformTopEigenspaceTransferGap
      halfExtent N hN beta hbeta := by
  apply
    periodicHypercubicEvenSpecialUnitary_uniformGroundStateTwelveSpatialPoincareOnPhysicalRightLifts_implies_uniformTransferGap
      halfExtent N hN beta hbeta
  exact
    periodicHypercubicEvenSpecialUnitary_hasUniformGroundStateTwelveSpatialPoincareOnPhysicalRightLifts_of_uniformGapCutoff
      halfExtent N hN beta hbeta s hs hcut

/-- Explicit version of the G4 endpoint: every scale has physical transfer gap
at least 1/3072. -/
theorem
    periodicHypercubicEvenSpecialUnitary_uniformTopEigenspaceTransferGap_ge_one_div_3072
    (s : ℝ) (hs : 8 < s)
    (hcut :
      ∀ n : ℕ,
        beta n ≤
          GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
            s hs) :
    ∀ n : ℕ,
      (1 / 3072 : ℝ) ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceTransferGap
          (halfExtent n) N hN (beta n) (hbeta n) := by
  intro n
  have hFrameCut :
      beta n ≤
        GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialFrameCutoff
          s hs :=
    (hcut n).trans
      (GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff_le_frameCutoff
        s hs)
  have hGap :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedTwelveSpatialRelativeFrame_implies_transferGap
      (halfExtent n) N hN (beta n) (hbeta n)
      s hs hFrameCut
  have hkappa :=
    GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformPoincareCoefficient_le_relativeFrameCoefficient
      s hs (beta n) (hbeta n) (hcut n)
  unfold
    GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformPoincareCoefficient
      at hkappa
  nlinarith

end ScalingFamily

end

end MathlibAnalytic
end MGAP4D
