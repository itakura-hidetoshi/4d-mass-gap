import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferGroundStateJointSixSpatialSweepStageSourceUpdateBackwardDirectMeanSplit
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic

/-!
# Exact Pythagorean split of backward direct fiber energy

PR #4867 places the physical target-law direct-difference L2 energy on the
backward reversible target heat-bath carrier.

At fixed background pair (C,D), write

  X(v) = F(left,C) - F(left,C[source <- v]).

Under the source law based at D this file proves exactly

  E[X^2] = E[(X - E[X])^2] + (E[X])^2.

The mean is the existing BackwardDirectMean from PR #4736. The centered
variance is exposed as a named real energy and the identity is lifted exactly
to the ENNReal backward fiber-energy presentation.

No Harnack comparison, response estimate, triangle inequality, factor two,
cardinality factor, or source/target symmetry is introduced.
-/

namespace MGAP4D.MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance backwardDirectFiberPythagoreanSpecialUnitaryIsTopologicalGroup
    (N : ℕ) :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance backwardDirectFiberPythagoreanSpecialUnitaryCompactSpace
    (N : ℕ) :
    CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance backwardDirectFiberPythagoreanSpecialUnitarySecondCountableTopology
    (N : ℕ) :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance backwardDirectFiberPythagoreanSpecialUnitaryMeasurableSpace
    (N : ℕ) :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance backwardDirectFiberPythagoreanSpecialUnitaryBorelSpace
    (N : ℕ) :
    BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

/-- Probability-space Pythagoras used below. This is kept local so the
backward-direct module does not depend on a private lemma from another theorem
unit. -/
private theorem
    backwardDirectFiber_probability_integral_sq_sub_const_eq_centered_mean_add_gap_sq
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ]
    (X : α → ℝ) (hX : MemLp X 2 μ) (c : ℝ) :
    (∫ x, (X x - c) ^ 2 ∂μ) =
      (∫ x, (X x - ∫ y, X y ∂μ) ^ 2 ∂μ) +
        ((∫ y, X y ∂μ) - c) ^ 2 := by
  have hShift : MemLp (fun x => X x - c) 2 μ :=
    hX.sub (memLp_const c)
  have hXIntegrable : Integrable X μ :=
    hX.integrable one_le_two
  have hMeanShift :
      (∫ x, X x - c ∂μ) = (∫ x, X x ∂μ) - c := by
    rw [integral_sub hXIntegrable (integrable_const c)]
    simp
  have hVarShift :
      variance (fun x => X x - c) μ =
        (∫ x, (X x - c) ^ 2 ∂μ) -
          (∫ x, X x - c ∂μ) ^ 2 := by
    simpa only [Pi.pow_apply] using
      (variance_eq_sub hShift)
  have hVarInvariant :
      variance (fun x => X x - c) μ = variance X μ :=
    variance_sub_const hX.aestronglyMeasurable c
  have hVarBase :
      variance X μ =
        ∫ x, (X x - ∫ y, X y ∂μ) ^ 2 ∂μ := by
    exact variance_eq_integral hX.aestronglyMeasurable.aemeasurable
  rw [hVarInvariant, hVarBase, hMeanShift] at hVarShift
  linarith

/-- Centered source-update variance on the backward carrier. The observable is
read from the first background and the source conditional law from the second. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (left B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (CD :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) : ℝ :=
  ∫ v,
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateFullConfigurationDifference
        H N source F left CD.1 v -
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectMean
        H N hN beta hbeta source F left B distinguishedSource k g₂ CD) ^ 2
    ∂periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalKernel
      H N hN beta hbeta B source distinguishedSource source k g₂ CD.2

/-- The centered backward direct variance energy is nonnegative. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy_nonneg
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (left B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (CD :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    0 ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy
        H N hN beta hbeta source F left B distinguishedSource k g₂ CD := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy
  exact integral_nonneg fun _ => sq_nonneg _

/-- Exact ENNReal Pythagorean decomposition of the backward source direct fiber
energy into centered variance plus squared backward direct mean. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectFiberEnergy_eq_variance_add_meanSq_of_bounded
    (H N : ℕ) (hN : 0 < N) (beta : ℝ) (hbeta : 0 ≤ beta)
    (source : PeriodicHypercubicEvenSpatialSliceLink H)
    (F :
      (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) → ℝ)
    (hF : StronglyMeasurable F)
    (bound : ℝ)
    (hbound : ∀ z, ‖F z‖ ≤ bound)
    (left B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (distinguishedSource : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (CD :
      PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N ×
        PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectFiberEnergy
        H N hN beta hbeta source F left B distinguishedSource k g₂ CD =
      ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy
            H N hN beta hbeta source F left B distinguishedSource k g₂ CD) +
        ENNReal.ofReal
          ((periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectMean
            H N hN beta hbeta source F left B distinguishedSource k g₂ CD) ^ 2) := by
  let μ :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkConditionalKernel
      H N hN beta hbeta B source distinguishedSource source k g₂ CD.2
  let X : Matrix.specialUnitaryGroup (Fin N) ℂ → ℝ :=
    fun v =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateFullConfigurationDifference
        H N source F left CD.1 v
  let m :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectMean
      H N hN beta hbeta source F left B distinguishedSource k g₂ CD
  letI : IsProbabilityMeasure μ := by
    dsimp [μ]
    infer_instance
  have hUpdate :
      Measurable
        (fun v : Matrix.specialUnitaryGroup (Fin N) ℂ =>
          Function.update CD.1 source v) :=
    measurable_update CD.1
  have hRight :
      StronglyMeasurable
        (fun D : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
          F (left, D)) :=
    hF.comp_measurable (measurable_const.prodMk measurable_id)
  have hUpdated :
      StronglyMeasurable
        (fun v : Matrix.specialUnitaryGroup (Fin N) ℂ =>
          F (left, Function.update CD.1 source v)) :=
    hRight.comp_measurable hUpdate
  have hXStrong : StronglyMeasurable X := by
    dsimp [X,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateFullConfigurationDifference]
    exact stronglyMeasurable_const.sub hUpdated
  have hXBound : ∀ v, ‖X v‖ ≤ 2 * |bound| := by
    intro v
    have hFirst :
        |F (left, CD.1)| ≤ |bound| := by
      simpa [Real.norm_eq_abs] using
        (hbound (left, CD.1)).trans (le_abs_self bound)
    have hSecond :
        |F (left, Function.update CD.1 source v)| ≤ |bound| := by
      simpa [Real.norm_eq_abs] using
        (hbound (left, Function.update CD.1 source v)).trans (le_abs_self bound)
    rw [Real.norm_eq_abs]
    dsimp [X,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateFullConfigurationDifference]
    calc
      |F (left, CD.1) - F (left, Function.update CD.1 source v)| ≤
          |F (left, CD.1)| + |F (left, Function.update CD.1 source v)| :=
        abs_sub _ _
      _ ≤ |bound| + |bound| := add_le_add hFirst hSecond
      _ = 2 * |bound| := by ring
  have hXLp : MemLp X 2 μ :=
    MemLp.of_bound hXStrong.aestronglyMeasurable (2 * |bound|)
      (Filter.Eventually.of_forall hXBound)
  have hMean :
      (∫ v, X v ∂μ) = m := by
    rfl
  have hPyth :=
    backwardDirectFiber_probability_integral_sq_sub_const_eq_centered_mean_add_gap_sq
      μ X hXLp 0
  have hReal :
      (∫ v, X v ^ 2 ∂μ) =
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy
            H N hN beta hbeta source F left B distinguishedSource k g₂ CD +
          m ^ 2 := by
    unfold
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy
    simpa [sub_zero, hMean, X, μ, m] using hPyth
  have hSqInt : Integrable (fun v => X v ^ 2) μ :=
    hXLp.integrable_sq
  have hOfRealIntegral :
      ENNReal.ofReal (∫ v, X v ^ 2 ∂μ) =
        ∫⁻ v, ENNReal.ofReal (X v ^ 2) ∂μ :=
    ofReal_integral_eq_lintegral_ofReal hSqInt
      (Filter.Eventually.of_forall fun v => sq_nonneg (X v))
  have hFiber :
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectFiberEnergy
          H N hN beta hbeta source F left B distinguishedSource k g₂ CD =
        ENNReal.ofReal (∫ v, X v ^ 2 ∂μ) := by
    rw [
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectFiberEnergy_eq]
    simpa [
      X, μ,
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateFullConfigurationDifferenceSquare_eq_sq] using
      hOfRealIntegral.symm
  have hVar0 :
      0 ≤
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy
          H N hN beta hbeta source F left B distinguishedSource k g₂ CD :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy_nonneg
      H N hN beta hbeta source F left B distinguishedSource k g₂ CD
  calc
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectFiberEnergy
        H N hN beta hbeta source F left B distinguishedSource k g₂ CD =
      ENNReal.ofReal (∫ v, X v ^ 2 ∂μ) := hFiber
    _ =
      ENNReal.ofReal
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy
            H N hN beta hbeta source F left B distinguishedSource k g₂ CD +
          m ^ 2) := by rw [hReal]
    _ =
      ENNReal.ofReal
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabGroundStateJointSourceUpdateBackwardDirectVarianceEnergy
            H N hN beta hbeta source F left B distinguishedSource k g₂ CD) +
        ENNReal.ofReal (m ^ 2) := by
      exact ENNReal.ofReal_add hVar0 (sq_nonneg m)
    _ = _ := by rfl

end

end MGAP4D.MathlibAnalytic
