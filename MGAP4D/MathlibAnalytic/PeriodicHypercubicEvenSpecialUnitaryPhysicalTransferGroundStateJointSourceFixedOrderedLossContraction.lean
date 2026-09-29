import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceFixedOrderedTerminalRecurrence
import MGAP4D.MathlibAnalytic.RealRenewalTailContraction

/-!
# Strict geometric loss decay for each actual fixed-color sweep

The ordered coefficient Q from #4936 vanishes at zero. Shrink its own cutoff
until Q < 1/2, so eta = (Q/(1-Q))^2 is strictly below one. Restrict the ordered
kernel to one color without a cardinality factor and reuse #4937's actual
fixed-color recurrence. This yields L_c(S_c f) <= eta L_c(f) and geometric
iteration along the SAME S_c on the bounded concrete core.

This is not yet physical defect contraction. The imported renewal-tail lemma
makes the additional vanishing-tail requirement explicit. No old q_phys,
new representative, density extension or positive-beta commutativity is used.
-/

namespace MGAP4D.MathlibAnalytic

open scoped BigOperators

noncomputable section

attribute [local instance]
  groundStateJointOneLinkBoundedCoreSpecialUnitaryIsTopologicalGroup
  groundStateJointOneLinkBoundedCoreSpecialUnitaryCompactSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitarySecondCountableTopology
  groundStateJointOneLinkBoundedCoreSpecialUnitaryMeasurableSpace
  groundStateJointOneLinkBoundedCoreSpecialUnitaryBorelSpace
  groundStateJointOneLinkBoundedCoreSpatialLinkFintype
  groundStateJointOneLinkBoundedCoreTargetLinkFintype
  groundStateJointOneLinkBoundedCoreTargetLinkUnique

namespace GroundStateSourceFixedPairEnergy

local notation "shellCoefficient" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCoefficient

/-- A positive, volume/rank-independent interval for the strict loss ratio. -/
theorem exists_jointLeakageLossContractionCutoff (s : ℝ) (hs : 8 < s) :
    ∃ cutoff : ℝ, 0 < cutoff ∧ cutoff ≤ jointLeakageSchurCutoff s hs ∧
      ∀ beta : ℝ, 0 ≤ beta → beta ≤ cutoff →
        jointLeakageSchurCoefficient s beta < 1 / 2 := by
  let qReal : ℝ → ℝ := fun beta =>
    jointLeakageRMSMultiplierRealFormula s beta * shellCoefficient s beta
  have hContinuous : ContinuousAt qReal 0 :=
    (continuousAt_jointLeakageRMSMultiplierRealFormula s).mul
      (continuousAt_periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightPinFreeBidirectionalShellCoefficient s)
  rw [Metric.continuousAt_iff] at hContinuous
  obtain ⟨delta, hDelta, hControl⟩ := hContinuous (1 / 2) (by norm_num)
  let cutoff := min (delta / 2) (jointLeakageSchurCutoff s hs)
  have hPos : 0 < cutoff :=
    lt_min (by positivity) (jointLeakageSchurCutoff_pos s hs)
  have hCut : cutoff ≤ jointLeakageSchurCutoff s hs := min_le_right _ _
  refine ⟨cutoff, hPos, hCut, ?_⟩
  intro beta hbeta hbetaCut
  have hHalf : beta ≤ delta / 2 := hbetaCut.trans (min_le_left _ _)
  have hDistance : dist beta 0 < delta := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hbeta]
    linarith
  have hAbs : |qReal beta - qReal 0| < 1 / 2 := by
    simpa only [Real.dist_eq] using hControl hDistance
  have hUpper : qReal beta - qReal 0 < 1 / 2 :=
    lt_of_le_of_lt (le_abs_self _) hAbs
  have hZero : qReal 0 = 0 := by simp [qReal]
  rw [hZero, sub_zero] at hUpper
  have hStrict := (hbetaCut.trans hCut).trans
    (jointLeakageSchurCutoff_le_strictPhysicalSweepCutoff s hs)
  simpa only [qReal, jointLeakageSchurCoefficient,
    jointLeakageRMSMultiplier_eq_realFormula s beta hbeta hStrict] using hUpper

def jointLeakageLossContractionCutoff (s : ℝ) (hs : 8 < s) : ℝ :=
  Classical.choose (exists_jointLeakageLossContractionCutoff s hs)

theorem jointLeakageLossContractionCutoff_pos (s : ℝ) (hs : 8 < s) :
    0 < jointLeakageLossContractionCutoff s hs :=
  (Classical.choose_spec (exists_jointLeakageLossContractionCutoff s hs)).1

theorem jointLeakageLossContractionCutoff_le_schurCutoff (s : ℝ) (hs : 8 < s) :
    jointLeakageLossContractionCutoff s hs ≤ jointLeakageSchurCutoff s hs :=
  (Classical.choose_spec (exists_jointLeakageLossContractionCutoff s hs)).2.1

theorem jointLeakageSchurCoefficient_nonneg_lt_half
    (s : ℝ) (hs : 8 < s) (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut : beta ≤ jointLeakageLossContractionCutoff s hs) :
    0 ≤ jointLeakageSchurCoefficient s beta ∧
      jointLeakageSchurCoefficient s beta < 1 / 2 := by
  exact ⟨(jointLeakageSchurCoefficient_nonneg_lt_one s hs beta hbeta
    (hcut.trans (jointLeakageLossContractionCutoff_le_schurCutoff s hs))).1,
    (Classical.choose_spec (exists_jointLeakageLossContractionCutoff s hs)).2.2 beta hbeta hcut⟩

/-- The loss ratio uses the same ordered Schur coefficient, not old q_phys. -/
def jointLeakageLossRatio (s beta : ℝ) : ℝ :=
  (jointLeakageSchurCoefficient s beta / (1 - jointLeakageSchurCoefficient s beta)) ^ 2

theorem jointLeakageLossRatio_nonneg (s beta : ℝ) :
    0 ≤ jointLeakageLossRatio s beta := sq_nonneg _

@[simp] theorem jointLeakageLossRatio_zero (s : ℝ) :
    jointLeakageLossRatio s 0 = 0 := by simp [jointLeakageLossRatio]

theorem jointLeakageLossRatio_nonneg_lt_one
    (s : ℝ) (hs : 8 < s) (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut : beta ≤ jointLeakageLossContractionCutoff s hs) :
    0 ≤ jointLeakageLossRatio s beta ∧ jointLeakageLossRatio s beta < 1 := by
  have hQ := jointLeakageSchurCoefficient_nonneg_lt_half s hs beta hbeta hcut
  let q := jointLeakageSchurCoefficient s beta
  have hDen : 0 < 1 - q := by dsimp [q]; linarith [hQ.2]
  have hRatio0 : 0 ≤ q / (1 - q) := div_nonneg hQ.1 hDen.le
  have hRatio1 : q / (1 - q) < 1 :=
    (div_lt_one hDen).2 (by dsimp [q]; linarith [hQ.2])
  have hSquare : (q / (1 - q)) * (q / (1 - q)) < 1 :=
    (mul_le_mul_of_nonneg_right hRatio1.le hRatio0).trans_lt (by simpa using hRatio1)
  exact ⟨jointLeakageLossRatio_nonneg s beta,
    by simpa only [jointLeakageLossRatio, pow_two, q] using hSquare⟩

section FixedParameters

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "CLink" => PeriodicHypercubicEvenFixedSpatialColorLink H
local notation "JL2" => PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta
local notation "Core" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore H N hN beta hbeta
local notation "P" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2 H N hN beta hbeta
local notation "O" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageLocalProfile H N hN beta hbeta
local notation "T" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile H N hN beta hbeta
local notation "S" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkFullSweepVector H N hN beta hbeta
local notation "L" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepPathLoss H N hN beta hbeta
local notation "k" => jointLeakageNormCoefficient H N hN beta hbeta

/-- Fixed-color Schur feedback for the ACTUAL profiles. The color subtype is
an injection, so restricting rows and columns introduces no multiplicity. -/
theorem fixedColor_terminalPathLoss_le_ordered_schur_feedback
    (s : ℝ) (hs : 8 < s) (hcut : beta ≤ jointLeakageSchurCutoff s hs)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor) (f : JL2) (hf : f ∈ Core) :
    (1 - jointLeakageSchurCoefficient s beta) ^ 2 * L color (S color f) ≤
      jointLeakageSchurCoefficient s beta ^ 2 * L color f := by
  classical
  let Q := jointLeakageSchurCoefficient s beta
  let matrix := fun (target source : CLink color) => k s source.1 target.1
  let original := O color f
  let terminal := T color f
  let forced := fun target => ∑ source, matrix target source * original source
  have hQ : 0 ≤ Q ∧ Q < 1 :=
    jointLeakageSchurCoefficient_nonneg_lt_one s hs beta hbeta hcut
  have hShell := hcut.trans (jointLeakageSchurCutoff_le_shellCutoff s hs)
  have hStrict := hcut.trans (jointLeakageSchurCutoff_le_strictPhysicalSweepCutoff s hs)
  have hMatrix : ∀ target source, 0 ≤ matrix target source := by
    intro target source
    exact jointLeakageNormCoefficient_nonneg H N hN beta hbeta s source.1 target.1
  have hEmbed : ∀ w : Link → ℝ, (∀ e, 0 ≤ w e) →
      (∑ e : CLink color, w e.1) ≤ ∑ e : Link, w e := by
    intro w hw
    let emb : CLink color ↪ Link := ⟨Subtype.val, Subtype.val_injective⟩
    calc
      (∑ e : CLink color, w e.1) =
        ∑ e ∈ (Finset.univ : Finset (CLink color)).map emb, w e := by simp [emb]
      _ ≤ ∑ e : Link, w e := Finset.sum_le_univ_sum_of_nonneg hw
  have hRows : ∀ target, ∑ source, matrix target source ≤ Q := by
    intro target
    exact (hEmbed (fun source => k s source target.1)
      (fun source => jointLeakageNormCoefficient_nonneg H N hN beta hbeta s source target.1)).trans
      (jointLeakageNormCoefficient_columnSum_le_schurCoefficient
        H N hN s hs beta hbeta hShell target.1)
  have hCols : ∀ source, ∑ target, matrix target source ≤ Q := by
    intro source
    exact (hEmbed (fun target => k s source.1 target)
      (fun target => jointLeakageNormCoefficient_nonneg H N hN beta hbeta s source.1 target)).trans
      (jointLeakageNormCoefficient_rowSum_le_schurCoefficient
        H N hN s hs beta hbeta hShell source.1)
  have hSchur : ∀ v : CLink color → ℝ,
      (∑ target, (∑ source, matrix target source * v source) ^ 2) ≤
        Q ^ 2 * ∑ source, v source ^ 2 := by
    intro v
    have h := FiniteNonnegativeSchur.action_sq_sum_le_row_mul_column
      matrix hMatrix Q Q hQ.1 hRows hCols v
    simpa only [pow_two] using h
  have hOriginal : ∀ source, 0 ≤ original source := by
    intro source
    exact periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageLocalProfile_nonneg
      H N hN beta hbeta color f source
  have hTerminal : ∀ target, 0 ≤ terminal target := by
    intro target
    exact periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile_nonneg
      H N hN beta hbeta color f target
  have hForced : ∀ target, 0 ≤ forced target := by
    intro target
    exact Finset.sum_nonneg fun source _ => mul_nonneg (hMatrix target source) (hOriginal source)
  have hRecurrence : ∀ target,
      terminal target ≤ forced target + ∑ source, matrix target source * terminal source := by
    intro target
    exact fixedColor_terminalProfile_le_ordered_forcing_feedback
      H N hN beta hbeta s (by linarith) hStrict color f hf target
  have hCoercive := FiniteSchurOneSidedProfile.global_energy_coercive
    matrix Q hQ.1 hQ.2 hMatrix hSchur terminal forced hTerminal hForced hRecurrence
  have hEnergy : (1 - Q) ^ 2 * ∑ target, terminal target ^ 2 ≤
      Q ^ 2 * ∑ source, original source ^ 2 := hCoercive.trans (hSchur original)
  have hTerminalEq :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile_sq_sum_eq_terminalSweepPathLoss
      H N hN beta hbeta color f
  have hOriginalEq :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageLocalProfile_sq_sum_eq_pathLoss
      H N hN beta hbeta color f
  rw [← hTerminalEq, ← hOriginalEq]
  exact hEnergy

/-- Division is performed only after positivity of the denominator is proved. -/
theorem fixedColor_terminalPathLoss_le_lossRatio_mul
    (s : ℝ) (hs : 8 < s) (hcut : beta ≤ jointLeakageLossContractionCutoff s hs)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor) (f : JL2) (hf : f ∈ Core) :
    L color (S color f) ≤ jointLeakageLossRatio s beta * L color f := by
  have hQ := jointLeakageSchurCoefficient_nonneg_lt_half s hs beta hbeta hcut
  have hDen : 0 < 1 - jointLeakageSchurCoefficient s beta := by linarith [hQ.2]
  have hDenSq : 0 < (1 - jointLeakageSchurCoefficient s beta) ^ 2 := sq_pos_of_pos hDen
  have hEnergy := fixedColor_terminalPathLoss_le_ordered_schur_feedback
    H N hN beta hbeta s hs
    (hcut.trans (jointLeakageLossContractionCutoff_le_schurCutoff s hs)) color f hf
  calc
    L color (S color f) ≤
        (jointLeakageSchurCoefficient s beta ^ 2 * L color f) /
          (1 - jointLeakageSchurCoefficient s beta) ^ 2 :=
      (le_div_iff₀ hDenSq).2 (by simpa only [mul_comm] using hEnergy)
    _ = jointLeakageLossRatio s beta * L color f := by
      rw [jointLeakageLossRatio, div_pow]
      ring

/-- Geometric loss along iterates of the SAME fixed-color sweep, on the core. -/
theorem fixedColor_iteratedPathLoss_le_geometric
    (s : ℝ) (hs : 8 < s) (hcut : beta ≤ jointLeakageLossContractionCutoff s hs)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (f : JL2) (hf : f ∈ Core) (n : ℕ) :
    L color ((S color)^[n] f) ≤ jointLeakageLossRatio s beta ^ n * L color f := by
  have hInvariant : ∀ (g : JL2), g ∈ Core → S color g ∈ Core := by
    intro g hg
    exact periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweep_mem_boundedConcreteCore
      H N hN beta hbeta color
      ((Finset.univ : Finset (CLink color)).toList) g hg
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      calc
        L color ((S color)^[n] (S color f)) ≤
            jointLeakageLossRatio s beta ^ n * L color (S color f) :=
          ih (S color f) (hInvariant f hf)
        _ ≤ jointLeakageLossRatio s beta ^ n *
            (jointLeakageLossRatio s beta * L color f) :=
          mul_le_mul_of_nonneg_left
            (fixedColor_terminalPathLoss_le_lossRatio_mul H N hN beta hbeta s hs hcut color f hf)
            (pow_nonneg (jointLeakageLossRatio_nonneg s beta) n)
        _ = jointLeakageLossRatio s beta ^ (n + 1) * L color f := by
          rw [pow_succ]
          ring

end FixedParameters
end GroundStateSourceFixedPairEnergy
end
end MGAP4D.MathlibAnalytic
