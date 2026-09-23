import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeBidirectionalSchurGate
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCanonicalFixedRightHighTemperatureRemoteResidualOscillationUniform
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceTwoStepTerminalSpatialBaseL1PolynomialShellBound
import MGAP4D.MathlibAnalytic.FiniteSpatialShellSummability
import Mathlib.Tactic

/-!
# Oscillation-sharpened closure of the physical remote row

The strict physical sweep theorem closes the actual influence-envelope columns,
while the row obstruction was isolated separately.  This file closes that row
obstruction from the same beta-zero-vanishing two-step covariance input used
for the column.

The two ingredients are directional but both admit volume-independent bounds:

* the explicit two-step represented-right transport is constant on every
  off-diagonal ordered pair, hence its source-summed row equals the already
  bounded target-summed column;
* the two-step terminal response has pointwise base-L1 decay.  For a fixed
  target, the source shells obey the same cubic three-dimensional cardinality
  bound after using symmetry of the periodic base-L1 distance.

Consequently the remote row is bounded by exactly the same oscillation-sharpened
scalar as the remote column.  On the existing strict physical sweep cutoff,
both maximum row and maximum column are therefore below one, so the
bidirectional Schur coefficient is genuinely strict.

No symmetry of the full remote residual is asserted.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory
open scoped BigOperators

noncomputable section

local instance physicalRemoteRowOscillationSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

local instance physicalRemoteRowOscillationSpatialLinkNonempty
    (H : ℕ) :
    Nonempty (PeriodicHypercubicEvenSpatialSliceLink H) :=
  ⟨(⟨(0 : PeriodicHypercubicEvenVertex H), by
      simp [periodicHypercubicEvenOnPrimaryReflectionPlane]⟩,
    ⟨(1 : PeriodicHypercubicAxis), by norm_num⟩)⟩

local instance physicalRemoteRowOscillationSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance physicalRemoteRowOscillationSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance physicalRemoteRowOscillationSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance physicalRemoteRowOscillationSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance physicalRemoteRowOscillationSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- For a fixed physical target, the sources for which that target lies in the
source-aligned remote set. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteSourceFibers
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    Finset (PeriodicHypercubicEvenSpatialSliceLink H) := by
  classical
  exact Finset.univ.filter fun source =>
    target ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
        H source source

/-- The source-summed two-step represented-right transport at one fixed target. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_twoStep_remoteRightRowSum
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) : ℝ :=
  ∑ source ∈ (Finset.univ.erase target),
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
      H beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
        H beta target)
      2 (Sum.inr source)

/-- Off the diagonal the exact two-step represented-right transport is
independent of the ordered pair, so the source-summed row equals the existing
target-summed column. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_twoStep_remoteRightRowSum_eq_columnSum
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_twoStep_remoteRightRowSum
        H beta hbeta target =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_twoStep_remoteRightColumnSum
        H beta hbeta target := by
  classical
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_twoStep_remoteRightRowSum
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_twoStep_remoteRightColumnSum
  apply Finset.sum_congr rfl
  intro source hsource
  have hTargetSource : target ≠ source := by
    exact fun hEq => (Finset.ne_of_mem_erase hsource) hEq.symm
  have hSourceTarget : source ≠ target :=
    Finset.ne_of_mem_erase hsource
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_twoStep_remoteRightSource_eq
      H beta hbeta hTargetSource,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_twoStep_remoteRightSource_eq
      H beta hbeta hSourceTarget]

/-- The complete off-diagonal two-step transport row has the same
volume-independent coefficient as the already integrated column. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_twoStep_remoteRightRowSum_le
    (H : ℕ)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_twoStep_remoteRightRowSum
        H beta hbeta target ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepRemoteTransportCoefficient
        beta := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_twoStep_remoteRightRowSum_eq_columnSum]
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepRemoteTransportCoefficient] using
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_twoStep_remoteRightColumnSum_le
      H beta hbeta target

/-- The row-oriented source shells inherit the same cubic cardinality majorant.
The only extra step compared with the target-oriented shell theorem is symmetry
of the periodic link-base L1 distance. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteSourceSpatialBaseL1Shell_card_le_polynomial
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H)
    (r : ℕ) :
    (((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteSourceFibers
          H target).filter
      (fun source =>
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalSpatialBaseL1Distance
          H target source = r)).card) ≤
      3 * (2 * r + 1) ^ 3 := by
  classical
  apply le_trans
    (Finset.card_le_card (by
      intro source hsource
      have hRadius := (Finset.mem_filter.mp hsource).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      unfold
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalSpatialBaseL1Distance at hRadius
      rw [
        periodicHypercubicEdgeBaseL1Distance_comm
          (PeriodicHypercubicEvenSideLength H)
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H source)
          (periodicHypercubicEvenSpatialSliceLinkEmbedding H target)]
      exact hRadius))
    (periodicHypercubicEvenSpatialSliceBaseL1Shell_card_le_polynomial
      H target r)

/-- A pointwise terminal-response decay certificate sums uniformly over the
remote sources of one fixed target, with the same cubic shell mass used in the
column route. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalEnvelope_remoteSourceSum_le_cubicSpatialBaseL1ShellMass
    (terminalPrefactor terminalRatio : ℝ)
    (hTerminalPrefactor : 0 ≤ terminalPrefactor)
    (hTerminalRatio : 0 ≤ terminalRatio)
    (hTerminalRatioLtOne : terminalRatio < 1)
    (H : ℕ)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    (∑ source ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteSourceFibers
          H target,
      terminalPrefactor *
        terminalRatio ^
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalSpatialBaseL1Distance
            H target source) ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCubicSpatialBaseL1ShellMass
        terminalPrefactor terminalRatio := by
  classical
  let remote :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteSourceFibers
      H target
  let radius : PeriodicHypercubicEvenSpatialSliceLink H → ℕ :=
    fun source =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalSpatialBaseL1Distance
        H target source
  let terminal : PeriodicHypercubicEvenSpatialSliceLink H → ℝ :=
    fun source => terminalPrefactor * terminalRatio ^ radius source
  let cutoff : ℕ := Finset.sum remote radius + 1
  have hRadius :
      ∀ source, source ∈ remote → radius source < cutoff := by
    intro source hsource
    have hLe : radius source ≤ Finset.sum remote radius :=
      Finset.single_le_sum
        (fun other _ => Nat.zero_le (radius other)) hsource
    simpa [cutoff] using Nat.lt_succ_of_le hLe
  have hShellCard :
      ∀ r, r < cutoff →
        (((remote.filter fun source => radius source = r).card : ℕ) : ℝ) ≤
          cubicSpatialShellMajorant r := by
    intro r _hr
    have hNat :
        (remote.filter fun source => radius source = r).card ≤
          3 * (2 * r + 1) ^ 3 := by
      simpa [remote, radius] using
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteSourceSpatialBaseL1Shell_card_le_polynomial
          H target r
    have hCast :
        (((remote.filter fun source => radius source = r).card : ℕ) : ℝ) ≤
          (((3 * (2 * r + 1) ^ 3 : ℕ) : ℝ)) := by
      exact_mod_cast hNat
    have hRhs :
        (((3 * (2 * r + 1) ^ 3 : ℕ) : ℝ)) =
          cubicSpatialShellMajorant r := by
      unfold cubicSpatialShellMajorant
      push_cast
      ring
    rw [hRhs] at hCast
    exact hCast
  have hSummable :
      Summable (fun r : ℕ =>
        cubicSpatialShellMajorant r *
          (terminalPrefactor * terminalRatio ^ r)) :=
    summable_cubicSpatialShellMajorant_mul_geometric_of_nonneg_lt_one
      terminalPrefactor terminalRatio hTerminalRatio hTerminalRatioLtOne
  have hSum :=
    finiteRealSum_le_tsum_of_pointwiseDecay_shellCardinality
      remote radius cutoff terminal
      terminalPrefactor terminalRatio cubicSpatialShellMajorant
      hRadius
      hTerminalPrefactor
      hTerminalRatio
      cubicSpatialShellMajorant_nonneg
      (by
        intro source _hsource
        exact le_rfl)
      hShellCard
      hSummable
  simpa [
    remote,
    radius,
    terminal,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCubicSpatialBaseL1ShellMass,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalSpatialShellMass] using
    hSum

/-- The source-aligned remote residual row is exactly the sum of the targetwise
worst-case majorants over remote sources. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidualRowSum_eq_worstCaseRemoteSourceSum
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidualRowSum
        H N hN beta hbeta A target =
      ∑ source ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteSourceFibers
          H target,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant
          H N hN beta hbeta A target source := by
  classical
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidualRowSum
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidual
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceRemotePhysicalInfluenceResidual
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteSourceFibers
  rw [← Finset.sum_filter]

/-- Pointwise terminal decay closes the complete remote-residual row by the
same two-step transport coefficient plus cubic terminal shell mass as in the
column route. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidualRowSum_le_twoStepTransport_add_cubicTerminal
    (N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (terminalPrefactor terminalRatio : ℝ)
    (hTerminalPrefactor : 0 ≤ terminalPrefactor)
    (hTerminalRatio : 0 ≤ terminalRatio)
    (hTerminalRatioLtOne : terminalRatio < 1)
    (hDecay :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalResponseSpatialBaseL1DecayBound
        N hN beta hbeta terminalPrefactor terminalRatio)
    (H : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target : PeriodicHypercubicEvenSpatialSliceLink H) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidualRowSum
        H N hN beta hbeta A target ≤
      Real.exp (16 * beta) *
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepRemoteTransportCoefficient
            beta +
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCubicSpatialBaseL1ShellMass
            terminalPrefactor terminalRatio) := by
  classical
  let remote :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteSourceFibers
      H target
  let transport := fun source : PeriodicHypercubicEvenSpatialSliceLink H =>
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate
      H beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
        H beta target)
      2 (Sum.inr source)
  let terminal := fun source : PeriodicHypercubicEvenSpatialSliceLink H =>
    terminalPrefactor *
      terminalRatio ^
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalSpatialBaseL1Distance
          H target source
  have hGeometry :
      ∀ source ∈ remote,
        target ≠ source ∧
          ¬ periodicHypercubicEvenSpatialSliceLinksSharePlaquette H target source := by
    intro source hsource
    have hTargetRemote :
        target ∈
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
            H source source := by
      simpa [remote,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteSourceFibers] using
        hsource
    have hRemote :
        target ∉ periodicHypercubicEvenSpatialSliceC5ExceptionalBackgroundFibers
          H source source := by
      simpa [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers] using
        hTargetRemote
    rcases
      periodicHypercubicEvenSpatialSlice_not_mem_C5ExceptionalBackgroundFibers
        H source source target hRemote with
      ⟨hSourceTarget, _hTargetDistinguished, hNoShare⟩
    exact ⟨Ne.symm hSourceTarget, hNoShare⟩
  have hPoint :
      ∀ source ∈ remote,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant
            H N hN beta hbeta A target source ≤
          Real.exp (16 * beta) * (transport source + terminal source) := by
    intro source hsource
    rcases hGeometry source hsource with ⟨hne, hNoShare⟩
    apply
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceWorstCaseCrossRatioInfluenceMajorant_le_exp_sixteen_mul_twoStepTransport_add_terminal
        H N hN beta hbeta A hne hNoShare (terminal source)
    intro g₁ g₂ h k
    have hTargetRemote :
        target ∈
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteTargetFibers
            H source source := by
      simpa [remote,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceC5RemoteSourceFibers] using
        hsource
    simpa [terminal] using
      hDecay H A source target hTargetRemote g₁ g₂ h k
  have hRemoteSubset :
      remote ⊆ Finset.univ.erase target := by
    intro source hsource
    have hne : target ≠ source := (hGeometry source hsource).1
    exact Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ source⟩
  have hTransportSum :
      (∑ source ∈ remote, transport source) ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepRemoteTransportCoefficient
          beta := by
    have hSubset :
        (∑ source ∈ remote, transport source) ≤
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_twoStep_remoteRightRowSum
            H beta hbeta target := by
      unfold
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_twoStep_remoteRightRowSum
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact hRemoteSubset
      · intro source _ _
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDistinctFiberTaggedRestrictedRandomScanVariationIterate_nonneg
            H beta hbeta
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation
              H beta target)
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_nonneg
              H beta target)
            2 (Sum.inr source)
    exact hSubset.trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioVariation_twoStep_remoteRightRowSum_le
        H beta hbeta target)
  have hTerminalSum :
      (∑ source ∈ remote, terminal source) ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCubicSpatialBaseL1ShellMass
          terminalPrefactor terminalRatio := by
    simpa [remote, terminal] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalEnvelope_remoteSourceSum_le_cubicSpatialBaseL1ShellMass
        terminalPrefactor terminalRatio
        hTerminalPrefactor hTerminalRatio hTerminalRatioLtOne
        H target
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidualRowSum_eq_worstCaseRemoteSourceSum]
  calc
    (∑ source ∈ remote,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFixedRightTargetRatioWorstCaseCrossRatioInfluenceMajorant
        H N hN beta hbeta A target source) ≤
      ∑ source ∈ remote,
        Real.exp (16 * beta) * (transport source + terminal source) := by
      apply Finset.sum_le_sum
      intro source hsource
      exact hPoint source hsource
    _ =
      Real.exp (16 * beta) *
        ((∑ source ∈ remote, transport source) +
          (∑ source ∈ remote, terminal source)) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤
      Real.exp (16 * beta) *
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepRemoteTransportCoefficient
            beta +
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCubicSpatialBaseL1ShellMass
            terminalPrefactor terminalRatio) := by
      exact
        mul_le_mul_of_nonneg_left
          (add_le_add hTransportSum hTerminalSum)
          (Real.exp_nonneg _)

/-- The oscillation-sharpened canonical covariance certificate supplies the
same beta-zero-vanishing scalar as a uniform bound for the remote row. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperature_remoteResidualOscillationUniformRowBound
    (N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 1 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s) :
    PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceHasUniformRemoteResidualRowBound
      N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureRemoteResidualOscillationBound
        s beta) := by
  have hsPos : 0 < s := zero_lt_one.trans hs
  have hRatioNonneg : 0 ≤ s⁻¹ := inv_nonneg.mpr hsPos.le
  have hRatioLtOne : s⁻¹ < 1 := inv_lt_one_of_one_lt₀ hs
  have hCovariance :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTwoStepTerminalCovarianceSpatialBaseL1OscillationDecayBound
      N hN s hs beta hbeta hcut
  have hTerminal :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceTwoStepTerminalCovarianceSpatialBaseL1DecayBound_to_terminalResponseSpatialBaseL1DecayBound
      N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovarianceOscillationPrefactor
        s beta)
      s⁻¹ hCovariance
  have hPrefactorNonneg :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovarianceOscillationPrefactor_nonneg
      s beta hbeta hcut
  have hTerminalPrefactorNonneg :
      0 ≤
        Real.exp (2 * beta) *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovarianceOscillationPrefactor
            s beta :=
    mul_nonneg (Real.exp_nonneg _) hPrefactorNonneg
  intro H A target
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureRemoteResidualOscillationBound] using
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceSourceAlignedRemotePhysicalInfluenceResidualRowSum_le_twoStepTransport_add_cubicTerminal
      N hN beta hbeta
      (Real.exp (2 * beta) *
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureTerminalCovarianceOscillationPrefactor
          s beta)
      s⁻¹
      hTerminalPrefactorNonneg hRatioNonneg hRatioLtOne hTerminal
      H A target

/-- On the existing strict physical sweep interval, the actual physical
influence envelope has strict maximum row as well as strict maximum column. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperaturePhysicalLeftInfluenceEnvelopeKernel_maximumRow_lt_one
    (N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 1 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (H : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    finiteInfluenceKernelMaximumRowSum
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
          H N hN beta hbeta A) < 1 := by
  have hHalfCut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s :=
    hcut.trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff_le_halfBarrierCutoff
        s)
  have hRemoteRow :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperature_remoteResidualOscillationUniformRowBound
      N hN s hs beta hbeta hHalfCut
  have hGate :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff_spec
      s beta hbeta hcut
  have hRowStrict :
      18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta +
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureRemoteResidualOscillationBound
          s beta < 1 := by
    simpa [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformEnvelopeColumnCoefficient] using
      hGate
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel_maximumRow_lt_one_of_uniformRemoteRow
      N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureRemoteResidualOscillationBound
        s beta)
      hRemoteRow hRowStrict H A

/-- The actual physical envelope therefore has a strict bidirectional Schur
coefficient on the same canonical positive high-temperature interval, with no
remaining row-bound premise. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperaturePhysicalLeftInfluenceEnvelopeKernel_bidirectionalSchurCoefficient_lt_one_closed
    (N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 1 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (H : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    finiteInfluenceKernelBidirectionalSchurCoefficient
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
          H N hN beta hbeta A) < 1 := by
  let rho :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureRemoteResidualOscillationBound
      s beta
  have hHalfCut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHalfBarrierCutoff
          s :=
    hcut.trans
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff_le_halfBarrierCutoff
        s)
  have hRemoteRow :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceHasUniformRemoteResidualRowBound
        N hN beta hbeta rho := by
    simpa [rho] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperature_remoteResidualOscillationUniformRowBound
        N hN s hs beta hbeta hHalfCut
  have hGate :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff_spec
      s beta hbeta hcut
  have hRowStrict :
      18 *
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceBackgroundUpdateHarnackInfluence
            beta +
        rho < 1 := by
    simpa [
      rho,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceUniformEnvelopeColumnCoefficient] using
      hGate
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperaturePhysicalLeftInfluenceEnvelopeKernel_bidirectionalSchurCoefficient_lt_one
      N hN s hs beta hbeta hcut rho hRemoteRow hRowStrict H A

/-- With the row obstruction closed, the actual physical envelope satisfies
the one-sided L2 profile coercivity whenever the observable-specific one-sided
profile comparison is supplied. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperaturePhysicalLeftInfluenceEnvelopeKernel_oneSided_global_energy_coercive_closed
    (N : ℕ)
    (hN : 0 < N)
    (s : ℝ)
    (hs : 1 < s)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff
          s)
    (H : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (profile localProfile : PeriodicHypercubicEvenSpatialSliceLink H → ℝ)
    (hProfileNonneg : ∀ e, 0 ≤ profile e)
    (hLocalNonneg : ∀ e, 0 ≤ localProfile e)
    (hOneSided : ∀ target,
      profile target ≤
        localProfile target +
          ∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
            (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
              H N hN beta hbeta A).influence target source *
              profile source) :
    (1 -
        finiteInfluenceKernelBidirectionalSchurCoefficient
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
            H N hN beta hbeta A)) ^ 2 *
        ∑ e : PeriodicHypercubicEvenSpatialSliceLink H, profile e ^ 2 ≤
      ∑ e : PeriodicHypercubicEvenSpatialSliceLink H, localProfile e ^ 2 := by
  let K :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferencePhysicalLeftInfluenceEnvelopeKernel
      H N hN beta hbeta A
  have hStrict :
      finiteInfluenceKernelBidirectionalSchurCoefficient K < 1 := by
    simpa [K] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperaturePhysicalLeftInfluenceEnvelopeKernel_bidirectionalSchurCoefficient_lt_one_closed
        N hN s hs beta hbeta hcut H A
  exact
    finiteInfluenceKernelBidirectional_oneSided_global_energy_coercive
      K hStrict profile localProfile
      hProfileNonneg hLocalNonneg
      (by simpa [K] using hOneSided)

end

end MGAP4D.MathlibAnalytic
