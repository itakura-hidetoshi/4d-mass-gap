import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceFixedOrderedSchurEnvelope
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceCrossBoundaryInfluenceOperator
import Mathlib.Tactic

/-!
# Two-boundary ordered Schur envelope

Combine the exact ordered same-boundary leakage coefficient from #4936 with
the already-proved one-point-supported cross-boundary C5 influence.

The matrix convention is target first, source second.  On each diagonal
boundary block we use
  k(source,target),
without assuming symmetry.  On each off-diagonal boundary block we use the
literal cross-boundary majorant, which is supported only at matching spatial
links.

Both row and column sums are bounded by
  Q(s,beta) + c_cross(beta)
with no link-count or volume factor.  Since both summands vanish at beta=0,
a positive volume/rank-independent cutoff makes the sum strictly below one.

This file proves coefficient geometry only.  It does not assert the missing
cross-boundary one-step L2 source-residual inequality or a physical gap.
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

local notation "crossCoefficient" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
local notation "crossMajorant" =>
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant

/-- The common Schur coefficient for the two-boundary block matrix. -/
def twoBoundaryOrderedSchurCoefficient (s beta : ℝ) : ℝ :=
  jointLeakageSchurCoefficient s beta + crossCoefficient beta

@[simp] theorem twoBoundaryOrderedSchurCoefficient_zero (s : ℝ) :
    twoBoundaryOrderedSchurCoefficient s 0 = 0 := by
  simp [twoBoundaryOrderedSchurCoefficient,
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient]

/-- Target-first two-boundary matrix.  The same-boundary ordered coefficient
keeps its literal source,target orientation. -/
def twoBoundaryOrderedKernel
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) (s : ℝ) :
    Sum (PeriodicHypercubicEvenSpatialSliceLink H)
        (PeriodicHypercubicEvenSpatialSliceLink H) →
    Sum (PeriodicHypercubicEvenSpatialSliceLink H)
        (PeriodicHypercubicEvenSpatialSliceLink H) → ℝ
  | Sum.inl target, Sum.inl source =>
      jointLeakageNormCoefficient H N hN beta hbeta s source target
  | Sum.inr target, Sum.inr source =>
      jointLeakageNormCoefficient H N hN beta hbeta s source target
  | Sum.inl target, Sum.inr source => crossMajorant beta target source
  | Sum.inr target, Sum.inl source => crossMajorant beta target source

private theorem crossMajorant_nonneg
    {H : ℕ} (beta : ℝ) (hbeta : 0 ≤ beta)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H) :
    0 ≤ crossMajorant beta target source := by
  by_cases h : source = target
  · subst source
    simpa [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient] using
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient_nonneg
        beta hbeta
  · simp [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant,
      h]

theorem twoBoundaryOrderedKernel_nonneg
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta) (s : ℝ)
    (target source :
      Sum (PeriodicHypercubicEvenSpatialSliceLink H)
          (PeriodicHypercubicEvenSpatialSliceLink H)) :
    0 ≤ twoBoundaryOrderedKernel H N hN beta hbeta s target source := by
  cases target <;> cases source
  · exact jointLeakageNormCoefficient_nonneg H N hN beta hbeta s _ _
  · exact crossMajorant_nonneg beta hbeta _ _
  · exact crossMajorant_nonneg beta hbeta _ _
  · exact jointLeakageNormCoefficient_nonneg H N hN beta hbeta s _ _

private theorem crossMajorant_columnSum_eq_coefficient
    (H : ℕ) (beta : ℝ)
    (source : PeriodicHypercubicEvenSpatialSliceLink H) :
    (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
      crossMajorant beta target source) = crossCoefficient beta := by
  classical
  rw [Finset.sum_eq_single source]
  · simp [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient]
  · intro target _ hne
    have hne' : source ≠ target := Ne.symm hne
    simp [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorant,
      hne']
  · simp

/-- Every target row is bounded by Q + c_cross.  The same-boundary term uses
the COLUMN sum theorem for k(source,target), because target is fixed. -/
theorem twoBoundaryOrderedKernel_rowSum_le
    (H N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 8 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut : beta ≤ jointLeakageSchurCutoff s hs)
    (target :
      Sum (PeriodicHypercubicEvenSpatialSliceLink H)
          (PeriodicHypercubicEvenSpatialSliceLink H)) :
    (∑ source,
      twoBoundaryOrderedKernel H N hN beta hbeta s target source) ≤
      twoBoundaryOrderedSchurCoefficient s beta := by
  classical
  cases target with
  | inl target =>
      rw [Fintype.sum_sum_type]
      change
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          jointLeakageNormCoefficient H N hN beta hbeta s source target) +
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          crossMajorant beta target source) ≤ _
      have hCross :
          (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
            crossMajorant beta target source) = crossCoefficient beta := by
        simpa [
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorantRowSum] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorantRowSum_eq_diagonal
            H beta target
      rw [hCross]
      change
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          jointLeakageNormCoefficient H N hN beta hbeta s source target) +
            crossCoefficient beta ≤
          jointLeakageSchurCoefficient s beta + crossCoefficient beta
      exact _root_.add_le_add
        (jointLeakageNormCoefficient_columnSum_le_schurCoefficient
          H N hN s hs beta hbeta
          (hcut.trans (jointLeakageSchurCutoff_le_shellCutoff s hs)) target)
        (le_refl _)
  | inr target =>
      rw [Fintype.sum_sum_type]
      change
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          crossMajorant beta target source) +
        (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
          jointLeakageNormCoefficient H N hN beta hbeta s source target) ≤ _
      have hCross :
          (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
            crossMajorant beta target source) = crossCoefficient beta := by
        simpa [
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorantRowSum] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryBoundedTestMajorantRowSum_eq_diagonal
            H beta target
      rw [hCross]
      change
        crossCoefficient beta +
            (∑ source : PeriodicHypercubicEvenSpatialSliceLink H,
              jointLeakageNormCoefficient H N hN beta hbeta s source target) ≤
          jointLeakageSchurCoefficient s beta + crossCoefficient beta
      calc
        _ ≤ crossCoefficient beta + jointLeakageSchurCoefficient s beta :=
          _root_.add_le_add (le_refl _)
            (jointLeakageNormCoefficient_columnSum_le_schurCoefficient
              H N hN s hs beta hbeta
              (hcut.trans (jointLeakageSchurCutoff_le_shellCutoff s hs)) target)
        _ = _ := by ring

/-- Every source column is bounded by Q + c_cross.  The same-boundary term uses
the ROW sum theorem for k(source,target), because source is fixed. -/
theorem twoBoundaryOrderedKernel_columnSum_le
    (H N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 8 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut : beta ≤ jointLeakageSchurCutoff s hs)
    (source :
      Sum (PeriodicHypercubicEvenSpatialSliceLink H)
          (PeriodicHypercubicEvenSpatialSliceLink H)) :
    (∑ target,
      twoBoundaryOrderedKernel H N hN beta hbeta s target source) ≤
      twoBoundaryOrderedSchurCoefficient s beta := by
  classical
  cases source with
  | inl source =>
      rw [Fintype.sum_sum_type]
      change
        (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          jointLeakageNormCoefficient H N hN beta hbeta s source target) +
        (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          crossMajorant beta target source) ≤ _
      rw [crossMajorant_columnSum_eq_coefficient H beta source]
      change
        (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          jointLeakageNormCoefficient H N hN beta hbeta s source target) +
            crossCoefficient beta ≤
          jointLeakageSchurCoefficient s beta + crossCoefficient beta
      exact _root_.add_le_add
        (jointLeakageNormCoefficient_rowSum_le_schurCoefficient
          H N hN s hs beta hbeta
          (hcut.trans (jointLeakageSchurCutoff_le_shellCutoff s hs)) source)
        (le_refl _)
  | inr source =>
      rw [Fintype.sum_sum_type]
      change
        (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          crossMajorant beta target source) +
        (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
          jointLeakageNormCoefficient H N hN beta hbeta s source target) ≤ _
      rw [crossMajorant_columnSum_eq_coefficient H beta source]
      change
        crossCoefficient beta +
            (∑ target : PeriodicHypercubicEvenSpatialSliceLink H,
              jointLeakageNormCoefficient H N hN beta hbeta s source target) ≤
          jointLeakageSchurCoefficient s beta + crossCoefficient beta
      calc
        _ ≤ crossCoefficient beta + jointLeakageSchurCoefficient s beta :=
          _root_.add_le_add (le_refl _)
            (jointLeakageNormCoefficient_rowSum_le_schurCoefficient
              H N hN s hs beta hbeta
              (hcut.trans (jointLeakageSchurCutoff_le_shellCutoff s hs)) source)
        _ = _ := by ring

theorem twoBoundaryOrderedSchurCoefficient_nonneg
    (s : ℝ) (hs : 8 < s) (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut : beta ≤ jointLeakageSchurCutoff s hs) :
    0 ≤ twoBoundaryOrderedSchurCoefficient s beta := by
  exact add_nonneg
    (jointLeakageSchurCoefficient_nonneg s hs beta hbeta
      (hcut.trans (jointLeakageSchurCutoff_le_shellCutoff s hs)))
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient_nonneg
      beta hbeta)

/-- Finite L2 Schur estimate for the complete two-boundary block matrix. -/
theorem twoBoundaryOrderedKernel_action_sq_sum_le
    (H N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 8 < s)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut : beta ≤ jointLeakageSchurCutoff s hs)
    (v :
      Sum (PeriodicHypercubicEvenSpatialSliceLink H)
          (PeriodicHypercubicEvenSpatialSliceLink H) → ℝ) :
    (∑ target,
      (∑ source,
        twoBoundaryOrderedKernel H N hN beta hbeta s target source * v source) ^ 2) ≤
      twoBoundaryOrderedSchurCoefficient s beta ^ 2 *
        ∑ source, v source ^ 2 := by
  have h :=
    FiniteNonnegativeSchur.action_sq_sum_le_row_mul_column
      (twoBoundaryOrderedKernel H N hN beta hbeta s)
      (twoBoundaryOrderedKernel_nonneg H N hN beta hbeta s)
      (twoBoundaryOrderedSchurCoefficient s beta)
      (twoBoundaryOrderedSchurCoefficient s beta)
      (twoBoundaryOrderedSchurCoefficient_nonneg s hs beta hbeta hcut)
      (twoBoundaryOrderedKernel_rowSum_le H N hN s hs beta hbeta hcut)
      (twoBoundaryOrderedKernel_columnSum_le H N hN s hs beta hbeta hcut)
      v
  simpa only [pow_two] using h

private theorem continuousAt_crossCoefficient :
    ContinuousAt crossCoefficient 0 := by
  unfold periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient
  have hExp : ContinuousAt (fun beta : ℝ => Real.exp (8 * beta)) 0 := by
    fun_prop
  have hDen :
      (Real.exp (8 * (0 : ℝ))) ^ 2 + 1 ≠ 0 := by
    norm_num
  exact
    continuousAt_const.mul
      (((hExp.pow 2).sub continuousAt_const).div
        ((hExp.pow 2).add continuousAt_const) hDen)

/-- A positive, volume/rank-independent interval on which the two-boundary
Schur coefficient is strictly below one. -/
theorem exists_twoBoundaryOrderedSchurCutoff (s : ℝ) (hs : 8 < s) :
    ∃ cutoff : ℝ, 0 < cutoff ∧ cutoff ≤ jointLeakageSchurCutoff s hs ∧
      ∀ beta : ℝ, 0 ≤ beta → beta ≤ cutoff →
        twoBoundaryOrderedSchurCoefficient s beta < 1 := by
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
    hQContinuous.add continuousAt_crossCoefficient
  rw [Metric.continuousAt_iff] at hContinuous
  obtain ⟨delta, hDelta, hControl⟩ := hContinuous 1 (by norm_num)
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
  have hAbs : |totalReal beta - totalReal 0| < 1 := by
    simpa only [Real.dist_eq] using hControl hDistance
  have hUpper : totalReal beta - totalReal 0 < 1 :=
    lt_of_le_of_lt (le_abs_self _) hAbs
  have hZero : totalReal 0 = 0 := by
    simp [totalReal, qReal,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCrossBoundaryContractionCoefficient]
  rw [hZero, sub_zero] at hUpper
  have hStrict : beta ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceCanonicalFixedRightHighTemperatureStrictPhysicalSweepCutoff s :=
    (hbetaCut.trans hCut).trans
      (jointLeakageSchurCutoff_le_strictPhysicalSweepCutoff s hs)
  simpa only [totalReal, qReal, twoBoundaryOrderedSchurCoefficient,
    jointLeakageSchurCoefficient,
    jointLeakageRMSMultiplier_eq_realFormula s beta hbeta hStrict] using hUpper

def twoBoundaryOrderedSchurCutoff (s : ℝ) (hs : 8 < s) : ℝ :=
  Classical.choose (exists_twoBoundaryOrderedSchurCutoff s hs)

theorem twoBoundaryOrderedSchurCutoff_pos (s : ℝ) (hs : 8 < s) :
    0 < twoBoundaryOrderedSchurCutoff s hs :=
  (Classical.choose_spec (exists_twoBoundaryOrderedSchurCutoff s hs)).1

theorem twoBoundaryOrderedSchurCutoff_le_jointLeakageSchurCutoff
    (s : ℝ) (hs : 8 < s) :
    twoBoundaryOrderedSchurCutoff s hs ≤ jointLeakageSchurCutoff s hs :=
  (Classical.choose_spec (exists_twoBoundaryOrderedSchurCutoff s hs)).2.1

theorem twoBoundaryOrderedSchurCoefficient_nonneg_lt_one
    (s : ℝ) (hs : 8 < s) (beta : ℝ) (hbeta : 0 ≤ beta)
    (hcut : beta ≤ twoBoundaryOrderedSchurCutoff s hs) :
    0 ≤ twoBoundaryOrderedSchurCoefficient s beta ∧
      twoBoundaryOrderedSchurCoefficient s beta < 1 := by
  have hJoint : beta ≤ jointLeakageSchurCutoff s hs :=
    hcut.trans (twoBoundaryOrderedSchurCutoff_le_jointLeakageSchurCutoff s hs)
  exact ⟨
    twoBoundaryOrderedSchurCoefficient_nonneg s hs beta hbeta hJoint,
    (Classical.choose_spec (exists_twoBoundaryOrderedSchurCutoff s hs)).2.2
      beta hbeta hcut⟩

end GroundStateSourceFixedPairEnergy

end
end MGAP4D.MathlibAnalytic
