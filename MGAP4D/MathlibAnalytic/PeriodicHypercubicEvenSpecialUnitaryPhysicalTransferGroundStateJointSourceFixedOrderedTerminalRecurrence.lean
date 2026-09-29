import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceFixedOrderedSchurEnvelope
import MGAP4D.MathlibAnalytic.RealHilbertProjectionSweepTargetResidualForcingBudgetProfileSum

/-!
# Actual terminal recurrence for the ordered RMS leakage envelope

The actual bounded-core cyclic budget from #4935 is classified exactly:
suffix sources carry original profile O, and prefix sources carry terminal
profile T. Each is counted once. Nonnegative extension to genuine spatial
links gives T(target) <= sum_source k(source,target) O(source)
                       + sum_source k(source,target) T(source).

The recurrence is proved, not assumed as a new hOneSided input. With the own
Schur coefficient Q from #4936, its two applications yield
  (1-Q)^2 Lterm <= Q^2 L
with the existing six-color normalization. All analytic statements retain
bounded-core membership. No old K_phys/q_phys substitution, density extension,
new representatives, cardinality factor or coefficient-two weakening occurs.
Strict renewal contraction, the physical gap and continuum remain downstream.
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

section FixedParameters

variable (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)

local notation "Link" => PeriodicHypercubicEvenSpatialSliceLink H
local notation "CLink" => PeriodicHypercubicEvenFixedSpatialColorLink H
local notation "JL2" => PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta
local notation "Core" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore H N hN beta hbeta
local notation "P" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkCondExpL2 H N hN beta hbeta
local notation "O" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageLocalProfile H N hN beta hbeta
local notation "T" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile H N hN beta hbeta
local notation "sixO" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile H N hN beta hbeta
local notation "sixT" => periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkTerminalSweepStageLocalProfile H N hN beta hbeta
local notation "k" => jointLeakageNormCoefficient H N hN beta hbeta

/-- Exact split of the actual cyclic source-residual budget. This is a
trajectory identity and needs no analytic cutoff or core assumption. -/
theorem fixedColor_orderedBudget_eq_split_profiles
    (s : ℝ) (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (pre suffix : List (CLink color)) (target : CLink color) (f : JL2)
    (hSplit : (Finset.univ : Finset (CLink color)).toList = pre ++ target :: suffix) :
    realHilbertProjectionSweepTargetResidualForcingBudget (P color)
      (fun source x => k s source.1 target.1 * ‖x - P color source x‖)
      (suffix ++ pre) (P color target (realHilbertProjectionSweep (P color) pre f)) =
      (∑ source ∈ suffix.toFinset, k s source.1 target.1 * O color f source) +
        ∑ source ∈ pre.toFinset, k s source.1 target.1 * T color f source := by
  classical
  let x0 := P color target (realHilbertProjectionSweep (P color) pre f)
  let forcing := fun (source : CLink color) (x : JL2) =>
    k s source.1 target.1 * ‖x - P color source x‖
  have hNodup : (pre ++ target :: suffix).Nodup := by
    rw [← hSplit]
    exact Finset.nodup_toList _
  have hPreNodup : pre.Nodup := (List.nodup_append.mp hNodup).1
  have hSuffixNodup : suffix.Nodup := (List.nodup_append.mp hNodup).2.1.of_cons
  have hSuffix :
      realHilbertProjectionSweepTargetResidualForcingBudget (P color) forcing suffix x0 =
        ∑ source ∈ suffix.toFinset, k s source.1 target.1 * O color f source := by
    apply realHilbertProjectionSweepTargetResidualForcingBudget_eq_sum_of_trajectory
      (P color) forcing (fun source => k s source.1 target.1 * O color f source)
      suffix x0 hSuffixNodup
    intro before source after hSuffixSplit
    have hSq :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSecondVisitCyclicSourceStepResidualEnergy_eq_originalLocalProfile_sq_of_suffixSplit
        H N hN beta hbeta color pre suffix before after target source f hSplit hSuffixSplit
    unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSecondVisitCyclicSourceStepResidualEnergy at hSq
    change ‖realHilbertProjectionSweep (P color) before x0 -
      realHilbertProjectionSweep (P color) (before ++ [source]) x0‖ ^ 2 =
        O color f source ^ 2 at hSq
    rw [realHilbertProjectionSweep_append (P color) before [source] x0] at hSq
    change ‖realHilbertProjectionSweep (P color) before x0 -
      P color source (realHilbertProjectionSweep (P color) before x0)‖ ^ 2 =
        O color f source ^ 2 at hSq
    have hNonneg :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageLocalProfile_nonneg
        H N hN beta hbeta color f source
    have hNorm : ‖realHilbertProjectionSweep (P color) before x0 -
        P color source (realHilbertProjectionSweep (P color) before x0)‖ = O color f source := by
      nlinarith [norm_nonneg (realHilbertProjectionSweep (P color) before x0 -
        P color source (realHilbertProjectionSweep (P color) before x0))]
    exact congrArg (fun a : ℝ => k s source.1 target.1 * a) hNorm
  have hPre :
      realHilbertProjectionSweepTargetResidualForcingBudget (P color) forcing pre
          (realHilbertProjectionSweep (P color) suffix x0) =
        ∑ source ∈ pre.toFinset, k s source.1 target.1 * T color f source := by
    apply realHilbertProjectionSweepTargetResidualForcingBudget_eq_sum_of_trajectory
      (P color) forcing (fun source => k s source.1 target.1 * T color f source)
      pre (realHilbertProjectionSweep (P color) suffix x0) hPreNodup
    intro before source after hPreSplit
    have hSq :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSecondVisitCyclicSourceStepResidualEnergy_eq_terminalLocalProfile_sq_of_preSplit
        H N hN beta hbeta color pre suffix before after target source f hSplit hPreSplit
    unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSecondVisitCyclicSourceStepResidualEnergy at hSq
    change ‖realHilbertProjectionSweep (P color) (suffix ++ before) x0 -
      realHilbertProjectionSweep (P color) ((suffix ++ before) ++ [source]) x0‖ ^ 2 =
        T color f source ^ 2 at hSq
    rw [realHilbertProjectionSweep_append (P color) (suffix ++ before) [source] x0] at hSq
    change ‖realHilbertProjectionSweep (P color) (suffix ++ before) x0 -
      P color source (realHilbertProjectionSweep (P color) (suffix ++ before) x0)‖ ^ 2 =
        T color f source ^ 2 at hSq
    rw [realHilbertProjectionSweep_append (P color) suffix before x0] at hSq
    have hNonneg :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile_nonneg
        H N hN beta hbeta color f source
    have hNorm : ‖realHilbertProjectionSweep (P color) before
          (realHilbertProjectionSweep (P color) suffix x0) -
        P color source (realHilbertProjectionSweep (P color) before
          (realHilbertProjectionSweep (P color) suffix x0))‖ = T color f source := by
      nlinarith [norm_nonneg (realHilbertProjectionSweep (P color) before
        (realHilbertProjectionSweep (P color) suffix x0) -
          P color source (realHilbertProjectionSweep (P color) before
            (realHilbertProjectionSweep (P color) suffix x0)))]
    exact congrArg (fun a : ℝ => k s source.1 target.1 * a) hNorm
  change realHilbertProjectionSweepTargetResidualForcingBudget (P color) forcing (suffix ++ pre) x0 = _
  rw [realHilbertProjectionSweepTargetResidualForcingBudget_append, hSuffix, hPre]

/-- Actual fixed-color forcing/feedback recurrence. No extra analytic one-step
or hOneSided premise remains; all inputs are on the bounded concrete core. -/
theorem fixedColor_terminalProfile_le_ordered_forcing_feedback
    (s : ℝ) (hs : 1 < s)
    (hcut : beta ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff s)
    (color : PeriodicHypercubicEvenGroundStateSpatialColor)
    (f : JL2) (hf : f ∈ Core) (target : CLink color) :
    T color f target ≤
      (∑ source : CLink color, k s source.1 target.1 * O color f source) +
        ∑ source : CLink color, k s source.1 target.1 * T color f source := by
  classical
  have hMem : target ∈ (Finset.univ : Finset (CLink color)).toList := by simp
  obtain ⟨pre, suffix, hSplit⟩ := List.mem_iff_append.mp hMem
  have hBudget :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile_le_cyclicOrderedNormSourceResidualBudget
      H N hN beta hbeta s hs hcut color pre suffix target f hf hSplit
  rw [fixedColor_orderedBudget_eq_split_profiles H N hN beta hbeta s color pre suffix target f hSplit] at hBudget
  exact hBudget.trans (_root_.add_le_add
    (Finset.sum_le_univ_sum_of_nonneg (fun source => mul_nonneg
      (jointLeakageNormCoefficient_nonneg H N hN beta hbeta s source.1 target.1)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkSweepStageLocalProfile_nonneg
        H N hN beta hbeta color f source)))
    (Finset.sum_le_univ_sum_of_nonneg (fun source => mul_nonneg
      (jointLeakageNormCoefficient_nonneg H N hN beta hbeta s source.1 target.1)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateFixedSpatialColorOneLinkTerminalSweepStageLocalProfile_nonneg
        H N hN beta hbeta color f source))))

private theorem fixedColor_originalProfile_eq_sixSpatial
    (color : PeriodicHypercubicEvenGroundStateSpatialColor) (f : JL2) (source : CLink color) :
    O color f source = sixO f source.1 := by
  rcases source with ⟨source, hColor⟩
  subst color
  rfl

private theorem fixedColor_terminalProfile_eq_sixSpatial
    (color : PeriodicHypercubicEvenGroundStateSpatialColor) (f : JL2) (source : CLink color) :
    T color f source = sixT f source.1 := by
  rcases source with ⟨source, hColor⟩
  subst color
  rfl

/-- The genuine-link recurrence retains k(source,target). The fixed-color
embedding adds only nonnegative omitted sources, with no color-count factor. -/
theorem sixSpatial_terminalProfile_le_ordered_forcing_feedback
    (s : ℝ) (hs : 1 < s)
    (hcut : beta ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff s)
    (f : JL2) (hf : f ∈ Core) (target : Link) :
    sixT f target ≤
      (∑ source : Link, k s source target * sixO f source) +
        ∑ source : Link, k s source target * sixT f source := by
  classical
  let color := periodicHypercubicEvenSpatialSliceLinkColor H target
  let t : CLink color := ⟨target, rfl⟩
  have hColor := fixedColor_terminalProfile_le_ordered_forcing_feedback
    H N hN beta hbeta s hs hcut color f hf t
  simp_rw [fixedColor_originalProfile_eq_sixSpatial,
    fixedColor_terminalProfile_eq_sixSpatial] at hColor
  change sixT f target ≤
    (∑ source : CLink color, k s source.1 target * sixO f source.1) +
      ∑ source : CLink color, k s source.1 target * sixT f source.1 at hColor
  have hEmbed : ∀ (w : Link → ℝ), (∀ e, 0 ≤ w e) →
      (∑ source : CLink color, w source.1) ≤ ∑ source : Link, w source := by
    intro w hw
    let emb : CLink color ↪ Link := ⟨Subtype.val, Subtype.val_injective⟩
    calc
      (∑ source : CLink color, w source.1) =
        ∑ source ∈ (Finset.univ : Finset (CLink color)).map emb, w source := by
          simp [emb]
      _ ≤ ∑ source : Link, w source := Finset.sum_le_univ_sum_of_nonneg hw
  exact hColor.trans (_root_.add_le_add
    (hEmbed (fun source => k s source target * sixO f source) (fun source => mul_nonneg
      (jointLeakageNormCoefficient_nonneg H N hN beta hbeta s source target)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile_nonneg
        H N hN beta hbeta f source)))
    (hEmbed (fun source => k s source target * sixT f source) (fun source => mul_nonneg
      (jointLeakageNormCoefficient_nonneg H N hN beta hbeta s source target)
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkTerminalSweepStageLocalProfile_nonneg
        H N hN beta hbeta f source))))

end FixedParameters

/-- Apply the SAME ordered Schur bound twice to the actual recurrence.
The exact six-color normalization cancels; the forcing retains Q squared. -/
theorem sixSpatial_terminalPathLoss_le_ordered_schur_feedback
    (H N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 8 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta) (hcut : beta ≤ jointLeakageSchurCutoff s hs)
    (f : PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2 H N hN beta hbeta)
    (hf : f ∈ periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
      H N hN beta hbeta) :
    (1 - jointLeakageSchurCoefficient s beta) ^ 2 *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkTerminalSweepPathLoss
        H N hN beta hbeta f ≤
    jointLeakageSchurCoefficient s beta ^ 2 *
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepPathLoss
        H N hN beta hbeta f := by
  let matrix := fun (target source : PeriodicHypercubicEvenSpatialSliceLink H) =>
    jointLeakageNormCoefficient H N hN beta hbeta s source target
  let terminal :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkTerminalSweepStageLocalProfile
      H N hN beta hbeta f
  let original :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile
      H N hN beta hbeta f
  let Q := jointLeakageSchurCoefficient s beta
  let forced := fun target => ∑ source, matrix target source * original source
  have hQ : 0 ≤ Q ∧ Q < 1 :=
    jointLeakageSchurCoefficient_nonneg_lt_one s hs beta hbeta hcut
  have hShell := hcut.trans (jointLeakageSchurCutoff_le_shellCutoff s hs)
  have hStrict := hcut.trans (jointLeakageSchurCutoff_le_strictPhysicalSweepCutoff s hs)
  have hMatrix : ∀ target source, 0 ≤ matrix target source := by
    intro target source
    exact jointLeakageNormCoefficient_nonneg H N hN beta hbeta s source target
  have hSchur : ∀ v : PeriodicHypercubicEvenSpatialSliceLink H → ℝ,
      (∑ target, (∑ source, matrix target source * v source) ^ 2) ≤ Q ^ 2 * ∑ source, v source ^ 2 := by
    intro v
    exact jointLeakageNormCoefficient_transpose_action_sq_sum_le H N hN s hs beta hbeta hShell v
  have hTerminal : ∀ target, 0 ≤ terminal target := by
    intro target
    exact periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkTerminalSweepStageLocalProfile_nonneg
      H N hN beta hbeta f target
  have hOriginal : ∀ source, 0 ≤ original source := by
    intro source
    exact periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile_nonneg
      H N hN beta hbeta f source
  have hForced : ∀ target, 0 ≤ forced target := by
    intro target
    exact Finset.sum_nonneg (fun source _ => mul_nonneg (hMatrix target source) (hOriginal source))
  have hRecurrence : ∀ target,
      terminal target ≤ forced target + ∑ source, matrix target source * terminal source := by
    intro target
    exact sixSpatial_terminalProfile_le_ordered_forcing_feedback
      H N hN beta hbeta s (by linarith) hStrict f hf target
  have hCoercive := FiniteSchurOneSidedProfile.global_energy_coercive
    matrix Q hQ.1 hQ.2 hMatrix hSchur terminal forced hTerminal hForced hRecurrence
  have hEnergy : (1 - Q) ^ 2 * ∑ target, terminal target ^ 2 ≤
      Q ^ 2 * ∑ source, original source ^ 2 := hCoercive.trans (hSchur original)
  have hScaled := mul_le_mul_of_nonneg_left hEnergy (show 0 ≤ (1 / 6 : ℝ) by norm_num)
  have hTerminalEq :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkTerminalSweepStageLocalProfile_normalized_sq_sum_eq_terminalSweepPathLoss
      H N hN beta hbeta f
  have hOriginalEq :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepStageLocalProfile_normalized_sq_sum_eq_sweepPathLoss
      H N hN beta hbeta f
  calc
    (1 - jointLeakageSchurCoefficient s beta) ^ 2 *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkTerminalSweepPathLoss
          H N hN beta hbeta f =
      (1 / 6 : ℝ) * ((1 - Q) ^ 2 * ∑ target, terminal target ^ 2) := by
        rw [← hTerminalEq]
        simp only [terminal, Q]
        ring
    _ ≤ (1 / 6 : ℝ) * (Q ^ 2 * ∑ source, original source ^ 2) := hScaled
    _ = jointLeakageSchurCoefficient s beta ^ 2 *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateSixSpatialOneLinkSweepPathLoss
          H N hN beta hbeta f := by
        rw [← hOriginalEq]
        simp only [original, Q]
        ring

end GroundStateSourceFixedPairEnergy

end

end MGAP4D.MathlibAnalytic
