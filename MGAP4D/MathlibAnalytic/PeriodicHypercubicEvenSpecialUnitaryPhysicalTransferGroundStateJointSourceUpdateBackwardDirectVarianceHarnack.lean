import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSourceUpdateBackwardDirectFiberEnergyPythagorean
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceBackgroundUpdateVarianceComparison
import Mathlib.Tactic

/-!
# Harnack transport of backward direct variance to the diagonal source law

PR #4868 splits the backward direct fiber energy exactly into a centered
variance term and a squared backward direct mean.

For a target update D = C[target <- g] with source != target, the centered
source-update observable is the same function of the source replacement value;
only its source conditional law changes from the law based at C to the law
based at D.

The existing normalized one-link Harnack comparison therefore gives

  ofReal V_backward(C,D)
    <= (exp (32 beta))^2 * ofReal V_backward(C,C).

This is a pointwise ordered-carrier theorem. No target averaging, response
estimate, finite-cardinality factor, or triangle inequality is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance backwardDirectVarianceHarnackSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance backwardDirectVarianceHarnackSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance backwardDirectVarianceHarnackSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance backwardDirectVarianceHarnackSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance backwardDirectVarianceHarnackSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- One off-source target update changes the backward direct variance by at
most the normalized Harnack law factor. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy_targetUpdate_ofReal_le_harnackLawFactor_mul_diagonal_of_bounded
    (H N : ℕ) (hN : 0 < N)
    (beta : ℝ) (hbeta : 0 ≤ beta)
    (source target : PeriodicHypercubicEvenSpatialSliceLink H)
    (hne : source ≠ target)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left B C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ g : Matrix.specialUnitaryGroup (Fin N) ℂ) :
    ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy
          H N hN beta hbeta source F left B distinguishedSource k g₂
          (C, Function.update C target g)) ≤
      ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2) *
        ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy
            H N hN beta hbeta source F left B distinguishedSource k g₂
            (C, C)) := by
  let X : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ :=
    fun v =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateFullConfigurationDifference
        H N source F left C v
  let μUpdated :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalKernel
      H N hN beta hbeta B source distinguishedSource source k g₂
      (Function.update C target g)
  let μDiagonal :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalKernel
      H N hN beta hbeta B source distinguishedSource source k g₂ C
  letI : IsProbabilityMeasure μUpdated := by
    dsimp [μUpdated]
    infer_instance
  letI : IsProbabilityMeasure μDiagonal := by
    dsimp [μDiagonal]
    infer_instance
  have hUpdate :
      Measurable
        (fun v : Matrix.specialUnitaryGroup (Fin N) ℂ =>
          Function.update C source v) :=
    measurable_update C
  have hRight :
      StronglyMeasurable
        (fun D : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
          F (left, D)) :=
    hF.comp_measurable (measurable_const.prodMk measurable_id)
  have hUpdated :
      StronglyMeasurable
        (fun v : Matrix.specialUnitaryGroup (Fin N) ℂ =>
          F (left, Function.update C source v)) :=
    hRight.comp_measurable hUpdate
  have hXStrong : StronglyMeasurable X := by
    dsimp [X,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateFullConfigurationDifference]
    exact stronglyMeasurable_const.sub hUpdated
  have hXBound : ∀ v, ‖X v‖ ≤ 2 * |bound| := by
    intro v
    have hFirst :
        |F (left, C)| ≤ |bound| := by
      simpa [Real.norm_eq_abs] using
        (hbound (left, C)).trans (le_abs_self bound)
    have hSecond :
        |F (left, Function.update C source v)| ≤ |bound| := by
      simpa [Real.norm_eq_abs] using
        (hbound (left, Function.update C source v)).trans (le_abs_self bound)
    rw [Real.norm_eq_abs]
    dsimp [X,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateFullConfigurationDifference]
    calc
      |F (left, C) - F (left, Function.update C source v)| ≤
          |F (left, C)| + |F (left, Function.update C source v)| :=
        abs_sub _ _
      _ ≤ |bound| + |bound| := add_le_add hFirst hSecond
      _ = 2 * |bound| := by ring
  have hXUpdated : MemLp X 2 μUpdated :=
    MemLp.of_bound hXStrong.aestronglyMeasurable (2 * |bound|)
      (Filter.Eventually.of_forall hXBound)
  have hXDiagonal : MemLp X 2 μDiagonal :=
    MemLp.of_bound hXStrong.aestronglyMeasurable (2 * |bound|)
      (Filter.Eventually.of_forall hXBound)
  have hUpdatedMean :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectMean
          H N hN beta hbeta source F left B distinguishedSource k g₂
          (C, Function.update C target g) =
        ∫ v, X v ∂μUpdated := by
    rfl
  have hDiagonalMean :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectMean
          H N hN beta hbeta source F left B distinguishedSource k g₂ (C, C) =
        ∫ v, X v ∂μDiagonal := by
    rfl
  have hUpdatedEnergy :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy
          H N hN beta hbeta source F left B distinguishedSource k g₂
          (C, Function.update C target g) =
        ∫ v,
          (X v -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectMean
              H N hN beta hbeta source F left B distinguishedSource k g₂
              (C, Function.update C target g)) ^ 2
          ∂μUpdated := by
    rfl
  have hDiagonalEnergy :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy
          H N hN beta hbeta source F left B distinguishedSource k g₂ (C, C) =
        ∫ v,
          (X v -
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectMean
              H N hN beta hbeta source F left B distinguishedSource k g₂
              (C, C)) ^ 2
          ∂μDiagonal := by
    rfl
  have hUpdatedVar :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy
          H N hN beta hbeta source F left B distinguishedSource k g₂
          (C, Function.update C target g) =
        variance X μUpdated := by
    rw [hUpdatedEnergy, hUpdatedMean]
    exact (variance_eq_integral hXStrong.aemeasurable).symm
  have hDiagonalVar :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy
          H N hN beta hbeta source F left B distinguishedSource k g₂ (C, C) =
        variance X μDiagonal := by
    rw [hDiagonalEnergy, hDiagonalMean]
    exact (variance_eq_integral hXStrong.aemeasurable).symm
  have hUpdatedOf :
      ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy
            H N hN beta hbeta source F left B distinguishedSource k g₂
            (C, Function.update C target g)) =
        evariance X μUpdated := by
    rw [hUpdatedVar]
    exact hXUpdated.ofReal_variance_eq
  have hDiagonalOf :
      ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy
            H N hN beta hbeta source F left B distinguishedSource k g₂ (C, C)) =
        evariance X μDiagonal := by
    rw [hDiagonalVar]
    exact hXDiagonal.ofReal_variance_eq
  have hUpdatedLaw :
      μUpdated =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B source distinguishedSource source k g₂
          (Function.update C target g) := by
    dsimp [μUpdated]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalKernel_apply
        H N hN beta hbeta B source distinguishedSource source k g₂
        (Function.update C target g)
  have hDiagonalLaw :
      μDiagonal =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B source distinguishedSource source k g₂ C := by
    dsimp [μDiagonal]
    exact
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalKernel_apply
        H N hN beta hbeta B source distinguishedSource source k g₂ C
  have hXRaw :
      MemLp X 2
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure
          H N hN beta hbeta B source distinguishedSource source k g₂
          (Function.update C target g)) := by
    rw [← hUpdatedLaw]
    exact hXUpdated
  have hCompareRaw :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkFiberProbabilityMeasure_backgroundUpdate_evariance_le_harnackLawFactor_mul
      H N hN beta hbeta B source distinguishedSource source target hne
      k g₂ g (C target) C X hXRaw
  have hCompare :
      evariance X μUpdated ≤
        ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2) *
          evariance X μDiagonal := by
    rw [hUpdatedLaw, hDiagonalLaw]
    simpa [Function.update_eq_self target C] using hCompareRaw
  calc
    ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy
          H N hN beta hbeta source F left B distinguishedSource k g₂
          (C, Function.update C target g)) =
      evariance X μUpdated := hUpdatedOf
    _ ≤
      ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2) *
        evariance X μDiagonal := hCompare
    _ =
      ENNReal.ofReal ((Real.exp (32 * beta)) ^ 2) *
        ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy
            H N hN beta hbeta source F left B distinguishedSource k g₂
            (C, C)) := by
      rw [hDiagonalOf]

end

end MGAP4D.MathlibAnalytic
