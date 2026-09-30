import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferTwoSidedOrderedTerminalRecurrence
import MGAP4D.MathlibAnalytic.RealHilbertProjectionSweepGeometricConvergence
import Mathlib.Tactic

/-!
# Strict loss contraction for the actual two-sided one-link sweep

PR #4968 proves the exact two-sided terminal-profile Schur feedback

  (1 - Q)^2 * sum T^2 <= Q^2 * sum O^2

on the bounded concrete core, where Q is the already-established
two-boundary ordered Schur coefficient.

This file turns that estimate into strict geometric decay of the actual full
two-sided one-link sweep.

1. Shrink the existing positive small-coupling interval until Q < 1/2 while
   also staying strictly below the cross-boundary threshold.
2. Define eta = (Q / (1 - Q))^2 and prove 0 <= eta < 1.
3. Identify sum O^2 and sum T^2 with the first and second full-sweep path
   losses and obtain

     loss(S f) <= eta * loss(f)

   on the bounded concrete core.
4. Extend the same inequality to every genuine joint L2 vector by density and
   closedness.  Closedness is proved through the exact Hilbert norm-loss
   identity, so no continuity API for the recursive path-loss definition is
   needed.
5. Package geometric decay of the same full sweep on all joint L2.

No new coefficient, cardinality factor, or volume factor is introduced.
-/

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory Set
open scoped BigOperators InnerProductSpace

noncomputable section

local instance twoSidedLossContractionSpatialLinkFintype
    (H : ℕ) :
    Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

namespace GroundStateSourceFixedPairEnergy

local notation "crossCoefficient" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient

private theorem twoSidedLossContinuousAt_crossCoefficient :
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

/-- Positive volume/rank-independent interval on which the two-boundary Schur
coefficient is below one half and the cross-boundary threshold is strict. -/
theorem exists_twoBoundaryOrderedLossContractionCutoff
    (s : ℝ) (hs : 8 < s) :
    ∃ cutoff : ℝ,
      0 < cutoff ∧
      cutoff ≤ twoBoundaryOrderedSchurCutoff s hs ∧
      cutoff <
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBetaThreshold ∧
      ∀ beta : ℝ, 0 ≤ beta → beta ≤ cutoff →
        twoBoundaryOrderedSchurCoefficient s beta < 1 / 2 := by
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
    hQContinuous.add twoSidedLossContinuousAt_crossCoefficient
  rw [Metric.continuousAt_iff] at hContinuous
  obtain ⟨delta, hDelta, hControl⟩ :=
    hContinuous (1 / 2) (by norm_num)
  have hCrossPos :
      0 <
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBetaThreshold := by
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBetaThreshold
    exact div_pos (Real.log_pos (by norm_num)) (by norm_num)
  let cutoff :=
    min (delta / 2)
      (min
        (twoBoundaryOrderedSchurCutoff s hs)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBetaThreshold / 2))
  have hPos : 0 < cutoff := by
    dsimp [cutoff]
    exact lt_min
      (by positivity)
      (lt_min
        (twoBoundaryOrderedSchurCutoff_pos s hs)
        (by positivity))
  have hSchur :
      cutoff ≤ twoBoundaryOrderedSchurCutoff s hs := by
    dsimp [cutoff]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hCross :
      cutoff <
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBetaThreshold := by
    have hHalf :
        cutoff ≤
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBetaThreshold / 2 := by
      dsimp [cutoff]
      exact (min_le_right _ _).trans (min_le_right _ _)
    linarith
  refine ⟨cutoff, hPos, hSchur, hCross, ?_⟩
  intro beta hbeta hbetaCut
  have hHalf : beta ≤ delta / 2 := by
    exact hbetaCut.trans (by
      dsimp [cutoff]
      exact min_le_left _ _)
  have hDistance : dist beta 0 < delta := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hbeta]
    linarith
  have hAbs : |totalReal beta - totalReal 0| < 1 / 2 := by
    simpa only [Real.dist_eq] using hControl hDistance
  have hUpper : totalReal beta - totalReal 0 < 1 / 2 :=
    lt_of_le_of_lt (le_abs_self _) hAbs
  have hZero : totalReal 0 = 0 := by
    simp [
      totalReal, qReal,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient]
  rw [hZero, sub_zero] at hUpper
  have hJoint :
      beta ≤ jointLeakageSchurCutoff s hs :=
    (hbetaCut.trans hSchur).trans
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
    jointLeakageRMSMultiplier_eq_realFormula s beta hbeta hStrict] using hUpper

def twoBoundaryOrderedLossContractionCutoff
    (s : ℝ) (hs : 8 < s) : ℝ :=
  Classical.choose (exists_twoBoundaryOrderedLossContractionCutoff s hs)

theorem twoBoundaryOrderedLossContractionCutoff_pos
    (s : ℝ) (hs : 8 < s) :
    0 < twoBoundaryOrderedLossContractionCutoff s hs :=
  (Classical.choose_spec
    (exists_twoBoundaryOrderedLossContractionCutoff s hs)).1

theorem twoBoundaryOrderedLossContractionCutoff_le_schurCutoff
    (s : ℝ) (hs : 8 < s) :
    twoBoundaryOrderedLossContractionCutoff s hs ≤
      twoBoundaryOrderedSchurCutoff s hs :=
  (Classical.choose_spec
    (exists_twoBoundaryOrderedLossContractionCutoff s hs)).2.1

theorem twoBoundaryOrderedLossContractionCutoff_lt_crossThreshold
    (s : ℝ) (hs : 8 < s) :
    twoBoundaryOrderedLossContractionCutoff s hs <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBetaThreshold :=
  (Classical.choose_spec
    (exists_twoBoundaryOrderedLossContractionCutoff s hs)).2.2.1

theorem twoBoundaryOrderedSchurCoefficient_nonneg_lt_half
    (s : ℝ) (hs : 8 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut : beta ≤ twoBoundaryOrderedLossContractionCutoff s hs) :
    0 ≤ twoBoundaryOrderedSchurCoefficient s beta ∧
      twoBoundaryOrderedSchurCoefficient s beta < 1 / 2 := by
  have hSchur :
      beta ≤ twoBoundaryOrderedSchurCutoff s hs :=
    hcut.trans
      (twoBoundaryOrderedLossContractionCutoff_le_schurCutoff s hs)
  exact ⟨
    (twoBoundaryOrderedSchurCoefficient_nonneg_lt_one
      s hs beta hbeta hSchur).1,
    (Classical.choose_spec
      (exists_twoBoundaryOrderedLossContractionCutoff s hs)).2.2.2
        beta hbeta hcut⟩

theorem beta_lt_crossThreshold_of_le_twoBoundaryOrderedLossContractionCutoff
    (s : ℝ) (hs : 8 < s)
    (beta : ℝ)
    (hcut : beta ≤ twoBoundaryOrderedLossContractionCutoff s hs) :
    beta <
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBetaThreshold :=
  hcut.trans_lt
    (twoBoundaryOrderedLossContractionCutoff_lt_crossThreshold s hs)

/-- Strict loss ratio generated by the exact two-boundary Schur coefficient. -/
def twoBoundaryOrderedLossRatio (s beta : ℝ) : ℝ :=
  (twoBoundaryOrderedSchurCoefficient s beta /
    (1 - twoBoundaryOrderedSchurCoefficient s beta)) ^ 2

theorem twoBoundaryOrderedLossRatio_nonneg (s beta : ℝ) :
    0 ≤ twoBoundaryOrderedLossRatio s beta :=
  sq_nonneg _

@[simp] theorem twoBoundaryOrderedLossRatio_zero (s : ℝ) :
    twoBoundaryOrderedLossRatio s 0 = 0 := by
  simp [
    twoBoundaryOrderedLossRatio,
    twoBoundaryOrderedSchurCoefficient,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient]

theorem twoBoundaryOrderedLossRatio_nonneg_lt_one
    (s : ℝ) (hs : 8 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut : beta ≤ twoBoundaryOrderedLossContractionCutoff s hs) :
    0 ≤ twoBoundaryOrderedLossRatio s beta ∧
      twoBoundaryOrderedLossRatio s beta < 1 := by
  have hQ :=
    twoBoundaryOrderedSchurCoefficient_nonneg_lt_half
      s hs beta hbeta hcut
  let q := twoBoundaryOrderedSchurCoefficient s beta
  have hDen : 0 < 1 - q := by
    dsimp [q]
    linarith [hQ.2]
  have hRatio0 : 0 ≤ q / (1 - q) :=
    div_nonneg hQ.1 hDen.le
  have hRatio1 : q / (1 - q) < 1 :=
    (div_lt_one hDen).2 (by
      dsimp [q]
      linarith [hQ.2])
  have hSquare : (q / (1 - q)) * (q / (1 - q)) < 1 :=
    (mul_le_mul_of_nonneg_right hRatio1.le hRatio0).trans_lt
      (by simpa using hRatio1)
  exact ⟨
    twoBoundaryOrderedLossRatio_nonneg s beta,
    by simpa only [twoBoundaryOrderedLossRatio, pow_two, q] using hSquare⟩

end GroundStateSourceFixedPairEnergy

/-- The terminal profile energy is exactly the path loss of the next complete
two-sided sweep. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkTerminalSweepStageLocalProfile_sq_sum_eq_terminalPathLoss
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :
    (∑ source : PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkTerminalSweepStageLocalProfile
        H N hN beta hbeta f source ^ 2) =
      realHilbertProjectionSweepPathLoss
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
          H N hN beta hbeta)
        ((Finset.univ :
          Finset (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H)).toList)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkFullSweepVector
          H N hN beta hbeta f) := by
  simpa [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkTerminalSweepStageLocalProfile] using
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweepStageLocalProfile_sq_sum_eq_pathLoss
      H N hN beta hbeta
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkFullSweepVector
        H N hN beta hbeta f)

/-- On the bounded concrete core, one complete two-sided sweep contracts the
next sweep path loss by the exact eta generated by the two-boundary Schur
coefficient. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_pathLoss_le_lossRatio_mul
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ) (hs : 8 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        GroundStateSourceFixedPairEnergy.twoBoundaryOrderedLossContractionCutoff
          s hs)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (hf :
      f ∈
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta) :
    let P :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
        H N hN beta hbeta
    let sources :=
      (Finset.univ :
        Finset (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H)).toList
    let S :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkFullSweepVector
        H N hN beta hbeta
    realHilbertProjectionSweepPathLoss P sources (S f) ≤
      GroundStateSourceFixedPairEnergy.twoBoundaryOrderedLossRatio s beta *
        realHilbertProjectionSweepPathLoss P sources f := by
  dsimp only
  let Q :=
    GroundStateSourceFixedPairEnergy.twoBoundaryOrderedSchurCoefficient s beta
  have hQ :=
    GroundStateSourceFixedPairEnergy.twoBoundaryOrderedSchurCoefficient_nonneg_lt_half
      s hs beta hbeta hcut
  have hDen : 0 < 1 - Q := by
    dsimp [Q]
    linarith [hQ.2]
  have hDenSq : 0 < (1 - Q) ^ 2 :=
    sq_pos_of_pos hDen
  have hEnergy :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_terminalProfile_energy_le_orderedSchur_feedback
      H N hN s hs beta hbeta
      (hcut.trans
        (GroundStateSourceFixedPairEnergy.twoBoundaryOrderedLossContractionCutoff_le_schurCutoff
          s hs))
      (GroundStateSourceFixedPairEnergy.beta_lt_crossThreshold_of_le_twoBoundaryOrderedLossContractionCutoff
        s hs beta hcut)
      f hf
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkTerminalSweepStageLocalProfile_sq_sum_eq_terminalPathLoss
      H N hN beta hbeta f,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkSweepStageLocalProfile_sq_sum_eq_pathLoss
      H N hN beta hbeta f] at hEnergy
  calc
    realHilbertProjectionSweepPathLoss
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
          H N hN beta hbeta)
        ((Finset.univ :
          Finset (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H)).toList)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkFullSweepVector
          H N hN beta hbeta f) ≤
      (Q ^ 2 *
        realHilbertProjectionSweepPathLoss
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
            H N hN beta hbeta)
          ((Finset.univ :
            Finset (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H)).toList)
          f) / (1 - Q) ^ 2 :=
      (le_div_iff₀ hDenSq).2
        (by simpa only [mul_comm] using hEnergy)
    _ =
      GroundStateSourceFixedPairEnergy.twoBoundaryOrderedLossRatio s beta *
        realHilbertProjectionSweepPathLoss
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
            H N hN beta hbeta)
          ((Finset.univ :
            Finset (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H)).toList)
          f := by
      rw [
        GroundStateSourceFixedPairEnergy.twoBoundaryOrderedLossRatio,
        div_pow]
      ring

/-- Density/closedness extension: the same loss contraction holds for every
genuine joint L2 vector. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_pathLoss_le_lossRatio_mul_allL2
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ) (hs : 8 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        GroundStateSourceFixedPairEnergy.twoBoundaryOrderedLossContractionCutoff
          s hs)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta) :
    let P :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
        H N hN beta hbeta
    let sources :=
      (Finset.univ :
        Finset (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H)).toList
    let S := realHilbertProjectionSweep P sources
    realHilbertProjectionSweepPathLoss P sources (S f) ≤
      GroundStateSourceFixedPairEnergy.twoBoundaryOrderedLossRatio s beta *
        realHilbertProjectionSweepPathLoss P sources f := by
  dsimp only
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
      H N hN beta hbeta
  let sources :=
    (Finset.univ :
      Finset (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H)).toList
  let S := realHilbertProjectionSweep P sources
  let eta :=
    GroundStateSourceFixedPairEnergy.twoBoundaryOrderedLossRatio s beta
  let loss :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta → ℝ :=
    fun g => ‖g‖ ^ 2 - ‖S g‖ ^ 2
  have hLossEq :
      ∀ g :
        PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta,
        loss g =
          realHilbertProjectionSweepPathLoss P sources g := by
    intro g
    exact
      realHilbertProjectionSweep_norm_sq_loss
        P
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2_idempotent
          H N hN beta hbeta)
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2_symmetric
          H N hN beta hbeta)
        sources g
  let good :
      Set
        (PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
          H N hN beta hbeta) :=
    {g | loss (S g) ≤ eta * loss g}
  have hLossContinuous : Continuous loss := by
    dsimp [loss]
    fun_prop
  have hClosed : IsClosed good := by
    exact
      isClosed_le
        (hLossContinuous.comp S.continuous)
        (continuous_const.mul hLossContinuous)
  have hCoreSub :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta ⊆ good := by
    intro g hg
    change loss (S g) ≤ eta * loss g
    rw [hLossEq, hLossEq]
    simpa [P, sources, S, eta,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkFullSweepVector] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_pathLoss_le_lossRatio_mul
        H N hN s hs beta hbeta hcut g hg
  have hDense :
      Dense
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
          H N hN beta hbeta) :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore_dense
      H N hN beta hbeta
  have hAll :
      closure
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointBoundedConcreteCore
            H N hN beta hbeta) ⊆ good :=
    closure_minimal hCoreSub hClosed
  have hfGood : f ∈ good := by
    apply hAll
    rw [hDense.closure_eq]
    exact Set.mem_univ f
  change loss (S f) ≤ eta * loss f at hfGood
  rw [hLossEq, hLossEq] at hfGood
  exact hfGood

/-- Geometric path-loss decay along iterates of the same complete two-sided
one-link sweep, on all joint L2. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_iteratedPathLoss_le_geometric
    (H N : ℕ)
    (hN : 0 < N)
    (s : ℝ) (hs : 8 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut :
      beta ≤
        GroundStateSourceFixedPairEnergy.twoBoundaryOrderedLossContractionCutoff
          s hs)
    (f :
      PeriodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointL2
        H N hN beta hbeta)
    (n : ℕ) :
    let P :=
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
        H N hN beta hbeta
    let sources :=
      (Finset.univ :
        Finset (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H)).toList
    let S := realHilbertProjectionSweep P sources
    realHilbertProjectionSweepPathLoss P sources (S^[n] f) ≤
      GroundStateSourceFixedPairEnergy.twoBoundaryOrderedLossRatio s beta ^ n *
        realHilbertProjectionSweepPathLoss P sources f := by
  dsimp only
  let P :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLinkCondExpL2
      H N hN beta hbeta
  let sources :=
    (Finset.univ :
      Finset (PeriodicHypercubicEvenGroundStateTwoSidedSpatialLink H)).toList
  let S := realHilbertProjectionSweep P sources
  let eta :=
    GroundStateSourceFixedPairEnergy.twoBoundaryOrderedLossRatio s beta
  induction n generalizing f with
  | zero =>
      simp
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      calc
        realHilbertProjectionSweepPathLoss P sources (S^[n] (S f)) ≤
            eta ^ n *
              realHilbertProjectionSweepPathLoss P sources (S f) :=
          ih (S f)
        _ ≤ eta ^ n *
            (eta * realHilbertProjectionSweepPathLoss P sources f) :=
          mul_le_mul_of_nonneg_left
            (by
              simpa [P, sources, S, eta] using
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateTwoSidedSpatialLink_pathLoss_le_lossRatio_mul_allL2
                  H N hN s hs beta hbeta hcut f)
            (pow_nonneg
              (GroundStateSourceFixedPairEnergy.twoBoundaryOrderedLossRatio_nonneg
                s beta)
              n)
        _ = eta ^ (n + 1) *
            realHilbertProjectionSweepPathLoss P sources f := by
          rw [pow_succ]
          ring

end

end MathlibAnalytic
end MGAP4D
