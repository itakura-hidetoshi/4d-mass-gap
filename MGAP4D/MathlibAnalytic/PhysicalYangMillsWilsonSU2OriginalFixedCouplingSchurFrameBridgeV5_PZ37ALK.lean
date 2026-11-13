import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalNormalizedAJABudgetRefinedV5_PZ37ALJ
import MGAP4D.MathlibAnalytic.PhysicalYangMillsWilsonSU2OriginalUniformTopOrthogonalCoercivityV5_PZ37AKL
import Mathlib.Tactic

/-!
# P4-Q2-PZ37ALK — original fixed coupling, the genuine Schur/frame obstruction,
and simultaneous physical Wilson normalization plus uniform coercivity

The AKL cutoff at s=9 is a Classical.choose of a positive continuity witness.
Its positivity does NOT prove that the unchanged original
beta0 = log(3/2)/64 lies below it.

This append-only leaf extracts two necessary, quantitative, model-specific
conditions for applying AKL at beta0:
  beta0 <= the actual two-sided twelve-spatial frame cutoff at s=9, and
  the actual two-boundary ordered Schur coefficient Q(9,beta0) < 1/3.
It also records their exact contrapositives. Neither condition is
asserted true or false at beta0 without an independent estimate.

For an unconditional common coupling define betaSafe = min(beta0,beta_*).
This is strictly positive, never exceeds the original beta0, and belongs
to the existing H-independent AKL interval. At this *same* coupling every
finite-H original Wilson transfer has the AKL full-top-orthogonal
contraction AND ALJ's strictly improved true physical normalization.
The original AJA strict negative-event budget is retained verbatim.

No Wilson action, Haar, physical transfer, original fixed beta0, top
projection, AJA event, pinned dependencies, root or existing Lean files
are modified. Neither a result at beta0 nor a continuum mass gap follows
unless the missing cutoff comparison is independently established.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped InnerProductSpace

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4900000

namespace GroundStatePosteriorJoint

local notation "beta0" => p4Q2PZ37ADC_fixedCoupling
local notation "betaStar" => p4Q2PZ37AKL_originalUniformCoercivityCutoff

/-- A single positive finite-volume-uniform coupling no larger than the
unchanged original physical beta0. This is a derived research value,
not a redefinition of beta0. -/
def p4Q2PZ37ALK_originalFixedCouplingUniformClip : ℝ :=
  min beta0 betaStar

local notation "betaSafe" => p4Q2PZ37ALK_originalFixedCouplingUniformClip

theorem p4Q2PZ37ALK_originalFixedCouplingUniformClip_pos :
    0 < betaSafe := by
  unfold p4Q2PZ37ALK_originalFixedCouplingUniformClip
  exact lt_min p4Q2PZ37ADC_fixedCoupling_pos
    p4Q2PZ37AKL_originalUniformCoercivityCutoff_pos

theorem p4Q2PZ37ALK_originalFixedCouplingUniformClip_le_original :
    betaSafe ≤ beta0 := by
  exact min_le_left _ _

theorem p4Q2PZ37ALK_originalFixedCouplingUniformClip_le_cutoff :
    betaSafe ≤ betaStar := by
  exact min_le_right _ _

/-- The safe coupling coincides with the original beta0 precisely in
the as-yet unverified direction beta0 <= beta_*. -/
theorem p4Q2PZ37ALK_originalFixedCouplingUniformClip_eq_original_of_cutoff
    (hcut : beta0 ≤ betaStar) :
    betaSafe = beta0 := by
  exact min_eq_left hcut

theorem p4Q2PZ37ALK_originalFixedCouplingUniformClip_eq_cutoff_of_lt
    (hcut : betaStar < beta0) :
    betaSafe = betaStar := by
  exact min_eq_right hcut.le

/-- Necessary actual original two-sided frame condition for transferring
AKL's H-uniform result to beta0. The condition is not yet discharged. -/
theorem p4Q2PZ37ALK_originalFixedCoupling_frameNecessary
    (hcut : beta0 ≤ betaStar) :
    beta0 ≤
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialFrameCutoff
        9 (by norm_num) := by
  change beta0 ≤
    GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
      9 (by norm_num) at hcut
  exact hcut.trans
    (GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff_le_frameCutoff
      9 (by norm_num))

/-- Necessary strict Schur coefficient test, with the exact 1/3 threshold
and unchanged two-boundary kernel (not a Gaussian substitute). -/
theorem p4Q2PZ37ALK_originalFixedCoupling_schurNecessary
    (hcut : beta0 ≤ betaStar) :
    GroundStateSourceFixedPairEnergy.twoBoundaryOrderedSchurCoefficient
      9 beta0 < (1 / 3 : ℝ) := by
  change beta0 ≤
    GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialUniformGapCutoff
      9 (by norm_num) at hcut
  exact
    GroundStateSourceFixedPairEnergy.twoBoundaryOrderedSchurCoefficient_lt_third_of_le_uniformGapCutoff
      9 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le hcut

/-- If the fixed coupling exceeds the actual frame cutoff, this specific
AKL route cannot certify that beta0 lies in the chosen interval. -/
theorem p4Q2PZ37ALK_originalFixedCoupling_frameObstruction
    (hframe :
      GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialFrameCutoff
        9 (by norm_num) < beta0) :
    ¬ beta0 ≤ betaStar := by
  intro hcut
  exact (not_lt_of_ge
    (p4Q2PZ37ALK_originalFixedCoupling_frameNecessary hcut)) hframe

/-- A Schur coefficient >= 1/3 likewise rules out certification of
beta0 by this selected uniform cutoff; no such numeric lower bound is
assumed or asserted here. -/
theorem p4Q2PZ37ALK_originalFixedCoupling_schurObstruction
    (hschur :
      (1 / 3 : ℝ) ≤
        GroundStateSourceFixedPairEnergy.twoBoundaryOrderedSchurCoefficient
          9 beta0) :
    ¬ beta0 ≤ betaStar := by
  intro hcut
  exact (not_lt_of_ge hschur)
    (p4Q2PZ37ALK_originalFixedCoupling_schurNecessary hcut)

/-- At the derived common positive coupling, actual original SU(2)
full-top-orthogonal transfer contraction works for every finite H. -/
theorem p4Q2PZ37ALK_safeOriginalTopOrthogonal_norm_le (H : ℕ) :
    ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H 2 (by norm_num) betaSafe
          p4Q2PZ37ALK_originalFixedCouplingUniformClip_pos.le‖ ≤
      (3071 / 3072 : ℝ) := by
  exact p4Q2PZ37AKL_originalTopOrthogonal_norm_le
    H betaSafe p4Q2PZ37ALK_originalFixedCouplingUniformClip_pos.le
    p4Q2PZ37ALK_originalFixedCouplingUniformClip_le_cutoff

/-- The ALI/ALJ lower bound applies to the same exact Wilson physical
operator and the same betaSafe, rather than an independently rescaled
surrogate model. -/
theorem p4Q2PZ37ALK_safeOriginalPhysicalNorm_ge_ALJ (H : ℕ) :
    Real.exp (-(betaSafe * p4Q2PZ37AFZ_plaquetteCount H)) *
      p4Q2PZ37ALJ_originalWilsonNormScalarFloor H betaSafe ≤
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) betaSafe
          p4Q2PZ37ALK_originalFixedCouplingUniformClip_pos.le‖ := by
  exact p4Q2PZ37ALJ_originalPhysicalNorm_ge_scalarFloor H betaSafe
    p4Q2PZ37ALK_originalFixedCouplingUniformClip_pos.le

/-- Simultaneous AKL coercivity and STRICT ALJ normalizer improvement at
one H-independent positive coupling, for each genuine finite-H Wilson
operator. Both claims refer to identical betaSafe and original carriers. -/
theorem p4Q2PZ37ALK_safeOriginalCoercivity_and_strictNormalizer
    (H : ℕ) :
    (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H 2 (by norm_num) betaSafe
          p4Q2PZ37ALK_originalFixedCouplingUniformClip_pos.le‖ ≤
        (3071 / 3072 : ℝ)) ∧
    (p4Q2PZ37AIF_originalCrossingPartition H betaSafe /
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) betaSafe
          p4Q2PZ37ALK_originalFixedCouplingUniformClip_pos.le‖ <
      Real.exp (betaSafe * p4Q2PZ37AFZ_plaquetteCount H)) := by
  refine ⟨p4Q2PZ37ALK_safeOriginalTopOrthogonal_norm_le H, ?_⟩
  exact lt_of_le_of_lt
    (p4Q2PZ37ALJ_originalPartitionOverNorm_le_ceiling H betaSafe
      p4Q2PZ37ALK_originalFixedCouplingUniformClip_pos.le)
    (p4Q2PZ37ALJ_originalPartitionOverNormCeiling_lt_old H betaSafe
      p4Q2PZ37ALK_originalFixedCouplingUniformClip_pos)

/-- The original strict AJA negative-event budget is NOT modified. It
inherits ALJ's improved envelope at the same clipped common coupling. -/
theorem p4Q2PZ37ALK_safeOriginalAJABudget_le_ALJ (H : ℕ) :
    (p4Q2PZ37AIW_originalNormalizedNegativeMargin H betaSafe
      p4Q2PZ37ALK_originalFixedCouplingUniformClip_pos.le) ^ 2 *
      Measure.real (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)
        {A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 |
          p4Q2PZ37AIW_originalNormalizedSourceTransfer H betaSafe
            p4Q2PZ37ALK_originalFixedCouplingUniformClip_pos.le A <
          -(p4Q2PZ37AIW_originalNormalizedNegativeMargin H betaSafe
            p4Q2PZ37ALK_originalFixedCouplingUniformClip_pos.le)} ≤
    ((betaSafe * Real.exp (-(2 * betaSafe * p4Q2PZ37AFZ_plaquetteCount H)) *
        p4Q2PZ37AHN_originalSource_HaarSecondMoment H / 2) *
      p4Q2PZ37ALJ_originalPartitionOverNormCeiling H betaSafe) ^ 2 *
      Measure.real (periodicHypercubicEvenSpecialUnitarySpatialSliceHaarMeasure H 2)
        {A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H 2 |
          p4Q2PZ37AIW_originalNormalizedSourceTransfer H betaSafe
            p4Q2PZ37ALK_originalFixedCouplingUniformClip_pos.le A <
          -(p4Q2PZ37AIW_originalNormalizedNegativeMargin H betaSafe
            p4Q2PZ37ALK_originalFixedCouplingUniformClip_pos.le)} := by
  exact p4Q2PZ37ALJ_originalAJABudget_le_improvedCeiling H betaSafe
    p4Q2PZ37ALK_originalFixedCouplingUniformClip_pos

/-- At beta0 itself, both physical claims follow IF the exact outstanding
cutoff comparison is later proved. This conditional theorem does not
silently identify beta0 with betaSafe. -/
theorem p4Q2PZ37ALK_originalFixedCouplingCoercivity_and_strictNormalizer
    (hcut : beta0 ≤ betaStar) (H : ℕ) :
    (‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTopEigenspaceOrthogonalTransferOperator
        H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le‖ ≤
      (3071 / 3072 : ℝ)) ∧
    (p4Q2PZ37AIF_originalCrossingPartition H beta0 /
      ‖periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabTransferOperator
        H 2 (by norm_num) beta0 p4Q2PZ37ADC_fixedCoupling_pos.le‖ <
      Real.exp (beta0 * p4Q2PZ37AFZ_plaquetteCount H)) := by
  refine ⟨p4Q2PZ37AKL_originalTopOrthogonal_norm_le
    H beta0 p4Q2PZ37ADC_fixedCoupling_pos.le hcut, ?_⟩
  exact lt_of_le_of_lt
    (p4Q2PZ37ALJ_originalPartitionOverNorm_le_ceiling H beta0
      p4Q2PZ37ADC_fixedCoupling_pos.le)
    (p4Q2PZ37ALJ_originalPartitionOverNormCeiling_lt_old H beta0
      p4Q2PZ37ADC_fixedCoupling_pos)


/-!
## Fixed-coupling no-go for the *selected* AKL high-temperature route

The physical beta0 is not merely of unknown relation to the chosen AKL
cutoff. The exact original normalized C5 background-update Harnack
influence is 2/5 at beta0, and the pre-existing half-barrier scalar at
s=9 exceeds one by a wide algebraic margin. Because the actual
AKL cutoff lies inside that half-barrier interval, beta_* < beta0.

This obstruction is specific to this quantitative two-boundary
Harnack/Schur/frame proof route. It does not assert that the genuine
Wilson transfer lacks coercivity or a gap at beta0.
-/

/-- No numerical floating-point approximation: the *original* background
Harnack influence at beta0 is exactly 2/5. -/
theorem p4Q2PZ37ALK_originalFixedCoupling_HarnackInfluence_eq_twoFifths :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
        beta0 = (2 / 5 : ℝ) := by
  have hExp :
      (Real.exp (32 * beta0)) ^ 2 = (3 / 2 : ℝ) := by
    calc
      (Real.exp (32 * beta0)) ^ 2 =
          Real.exp (32 * beta0 + 32 * beta0) := by
            rw [Real.exp_add, pow_two]
      _ = Real.exp (64 * beta0) := by
        congr 1
        ring
      _ = (3 / 2 : ℝ) := p4Q2PZ37ADC_fixedCoupling_exp_eq
  change
    2 * (((Real.exp (32 * beta0)) ^ 2 - 1) /
      ((Real.exp (32 * beta0)) ^ 2 + 1)) = (2 / 5 : ℝ)
  rw [hExp]
  norm_num

/-- At s=9 the *unchanged* fixed-coupling original half-barrier
coefficient is strictly ABOVE one, so the high-temperature half-barrier
certificate cannot cover beta0. -/
theorem p4Q2PZ37ALK_originalFixedCoupling_s9HalfBarrier_gt_one :
    (1 : ℝ) <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
        9 beta0 := by
  change
    (1 : ℝ) <
      18 *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
          beta0 * (9 : ℝ) ^ 2 +
        Real.exp (16 * beta0) * (1 / 2 : ℝ)
  rw [p4Q2PZ37ALK_originalFixedCoupling_HarnackInfluence_eq_twoFifths]
  have hExpPos : 0 < Real.exp (16 * beta0) := Real.exp_pos _
  nlinarith

/-- An unconditional obstruction to beta0 belonging to the ACTUAL
AKL chosen interval, obtained by tracing every dependency from the
two-boundary frame and Schur cutoffs to the original half-barrier.
No physical Wilson transfer counterexample is asserted. -/
theorem p4Q2PZ37ALK_originalFixedCoupling_not_le_AKLcutoff :
    ¬ beta0 ≤ betaStar := by
  intro hAKL
  have hFrame :
      beta0 ≤
        GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialFrameCutoff
          9 (by norm_num) :=
    p4Q2PZ37ALK_originalFixedCoupling_frameNecessary hAKL
  have hLoss :
      beta0 ≤
        GroundStateSourceFixedPairEnergy.twoBoundaryOrderedLossContractionCutoff
          9 (by norm_num) :=
    hFrame.trans
      (GroundStateSourceFixedPairEnergy.twoSidedTwelveSpatialFrameCutoff_le_twoBoundary
        9 (by norm_num))
  have hSchurCut :
      beta0 ≤
        GroundStateSourceFixedPairEnergy.twoBoundaryOrderedSchurCutoff
          9 (by norm_num) :=
    hLoss.trans
      (GroundStateSourceFixedPairEnergy.twoBoundaryOrderedLossContractionCutoff_le_schurCutoff
        9 (by norm_num))
  have hJointCut :
      beta0 ≤
        GroundStateSourceFixedPairEnergy.jointLeakageSchurCutoff
          9 (by norm_num) :=
    hSchurCut.trans
      (GroundStateSourceFixedPairEnergy.twoBoundaryOrderedSchurCutoff_le_jointLeakageSchurCutoff
        9 (by norm_num))
  have hShellCut :
      beta0 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCutoff
          9 (by norm_num) :=
    hJointCut.trans
      (GroundStateSourceFixedPairEnergy.jointLeakageSchurCutoff_le_shellCutoff
        9 (by norm_num))
  have hStrictCut :
      beta0 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          9 :=
    hShellCut.trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCutoff_le_strictPhysicalSweepCutoff
        9 (by norm_num))
  have hHalfCut :
      beta0 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          9 :=
    hStrictCut.trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff_le_halfBarrierCutoff
        9)
  have hHalfLtOne :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierPinFreeCoefficient
          9 beta0 < 1 :=
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff_spec
      9 beta0 p4Q2PZ37ADC_fixedCoupling_pos hHalfCut).1
  exact
    (not_lt_of_ge
      p4Q2PZ37ALK_originalFixedCoupling_s9HalfBarrier_gt_one.le)
      hHalfLtOne

/-- The original fixed coupling is rigorously LARGER than the selected
H-uniform AKL coupling cutoff. The AKL theorem itself remains valid
on the smaller interval. -/
theorem p4Q2PZ37ALK_AKLuniformCutoff_lt_originalFixedCoupling :
    betaStar < beta0 := by
  exact lt_of_not_ge p4Q2PZ37ALK_originalFixedCoupling_not_le_AKLcutoff

/-- Therefore the previously constructed common safe coupling is
EXACTLY the existing selected AKL cutoff, and is not beta0. -/
theorem p4Q2PZ37ALK_originalFixedCouplingUniformClip_eq_AKLcutoff :
    betaSafe = betaStar := by
  exact p4Q2PZ37ALK_originalFixedCouplingUniformClip_eq_cutoff_of_lt
    p4Q2PZ37ALK_AKLuniformCutoff_lt_originalFixedCoupling

theorem p4Q2PZ37ALK_originalFixedCouplingUniformClip_lt_original :
    betaSafe < beta0 := by
  rw [p4Q2PZ37ALK_originalFixedCouplingUniformClip_eq_AKLcutoff]
  exact p4Q2PZ37ALK_AKLuniformCutoff_lt_originalFixedCoupling

end GroundStatePosteriorJoint
end
end MGAP4D.MathlibAnalytic

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALK_originalFixedCouplingUniformClip
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALK_originalFixedCouplingUniformClip_pos
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALK_originalFixedCouplingUniformClip_le_original
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALK_originalFixedCouplingUniformClip_le_cutoff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALK_originalFixedCouplingUniformClip_eq_original_of_cutoff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALK_originalFixedCouplingUniformClip_eq_cutoff_of_lt
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALK_originalFixedCoupling_frameNecessary
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALK_originalFixedCoupling_schurNecessary
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALK_originalFixedCoupling_frameObstruction
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALK_originalFixedCoupling_schurObstruction
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALK_safeOriginalTopOrthogonal_norm_le
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALK_safeOriginalPhysicalNorm_ge_ALJ
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALK_safeOriginalCoercivity_and_strictNormalizer
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALK_safeOriginalAJABudget_le_ALJ
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALK_originalFixedCouplingCoercivity_and_strictNormalizer

#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALK_originalFixedCoupling_HarnackInfluence_eq_twoFifths
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALK_originalFixedCoupling_s9HalfBarrier_gt_one
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALK_originalFixedCoupling_not_le_AKLcutoff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALK_AKLuniformCutoff_lt_originalFixedCoupling
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALK_originalFixedCouplingUniformClip_eq_AKLcutoff
#print axioms MGAP4D.MathlibAnalytic.GroundStatePosteriorJoint.p4Q2PZ37ALK_originalFixedCouplingUniformClip_lt_original
