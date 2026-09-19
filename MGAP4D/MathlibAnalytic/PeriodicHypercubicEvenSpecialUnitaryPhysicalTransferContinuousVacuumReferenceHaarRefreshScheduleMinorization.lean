import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceOneLinkHaarRefreshKernel
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceDeterministicScheduleKernel
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

/-- The one-link Doeblin coefficient supplied by the literal C5 pairwise
Harnack estimate. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHaarMinorizationCoefficient
    (beta : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (Real.exp (32 * beta)))⁻¹

/-- The one-link Haar refresh is itself a Markov kernel. -/
noncomputable instance
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHaarRefreshKernel_isMarkovKernel
    (H N : ℕ)
    (fiber : PeriodicHypercubicEvenSpatialSliceLink H) :
    IsMarkovKernel
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHaarRefreshKernel
        H N fiber) := by
  unfold
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHaarRefreshKernel
  exact
    IsMarkovKernel.map
      (Kernel.id ×ₖ
        Kernel.const
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
          (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkUpdate_uncurry_measurable
        H N fiber)

/-- Ordered composition of independent one-link Haar refreshes.  The head
fiber is refreshed first, matching the actual deterministic heat-bath schedule
orientation. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceHaarRefreshScheduleKernel
    (H N : ℕ) :
    List (PeriodicHypercubicEvenSpatialSliceLink H) →
      Kernel
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
        (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
  | [] => Kernel.id
  | fiber :: fibers =>
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceHaarRefreshScheduleKernel
          H N fibers ∘ₖ
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHaarRefreshKernel
          H N fiber

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceHaarRefreshScheduleKernel_nil
    (H N : ℕ) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceHaarRefreshScheduleKernel
        H N [] = Kernel.id := by
  rfl

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceHaarRefreshScheduleKernel_cons
    (H N : ℕ)
    (fiber : PeriodicHypercubicEvenSpatialSliceLink H)
    (fibers : List (PeriodicHypercubicEvenSpatialSliceLink H)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceHaarRefreshScheduleKernel
        H N (fiber :: fibers) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceHaarRefreshScheduleKernel
          H N fibers ∘ₖ
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHaarRefreshKernel
          H N fiber := by
  rfl

/-- Every finite Haar-refresh schedule is a Markov kernel. -/
noncomputable instance
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceHaarRefreshScheduleKernel_isMarkovKernel
    (H N : ℕ)
    (fibers : List (PeriodicHypercubicEvenSpatialSliceLink H)) :
    IsMarkovKernel
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceHaarRefreshScheduleKernel
        H N fibers) := by
  induction fibers with
  | nil =>
      simp only [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceHaarRefreshScheduleKernel_nil]
      infer_instance
  | cons fiber fibers ih =>
      simp only [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceHaarRefreshScheduleKernel_cons]
      letI : IsMarkovKernel
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceHaarRefreshScheduleKernel
            H N fibers) := ih
      infer_instance

/-- Generic two-stage minorization composition at the measure level. -/
theorem finiteMarkovKernel_comp_measure_minorization
    {X : Type*}
    [MeasurableSpace X]
    (Khead Ktail Rhead Rtail : Kernel X X)
    (a b : ℝ≥0∞)
    (A : X)
    (hHead : a • Rhead A ≤ Khead A)
    (hTail : ∀ C : X, b • Rtail C ≤ Ktail C) :
    (a * b) • ((Rtail ∘ₖ Rhead) A) ≤
      (Ktail ∘ₖ Khead) A := by
  apply Measure.le_iff.2
  intro s hs
  have hTailPoint :
      ∀ C : X, b * Rtail C s ≤ Ktail C s := by
    intro C
    have h := Measure.le_iff.1 (hTail C) s hs
    simpa only [Measure.smul_apply, smul_eq_mul] using h
  have hFunction :
      (∫⁻ C : X, b * Rtail C s ∂Rhead A) ≤
        ∫⁻ C : X, Ktail C s ∂Rhead A := by
    exact lintegral_mono hTailPoint
  have hMeasure :
      (∫⁻ C : X, Ktail C s ∂(a • Rhead A)) ≤
        ∫⁻ C : X, Ktail C s ∂Khead A := by
    exact lintegral_mono' hHead le_rfl
  rw [
    Measure.smul_apply,
    Kernel.comp_apply' _ _ _ hs,
    Kernel.comp_apply' _ _ _ hs,
    smul_eq_mul]
  calc
    (a * b) * (∫⁻ C : X, Rtail C s ∂Rhead A) =
        a * (b * (∫⁻ C : X, Rtail C s ∂Rhead A)) := by
          ac_rfl
    _ = a * (∫⁻ C : X, b * Rtail C s ∂Rhead A) := by
          rw [lintegral_const_mul b (Kernel.measurable_coe Rtail hs)]
    _ ≤ a * (∫⁻ C : X, Ktail C s ∂Rhead A) := by
          exact mul_le_mul_left' hFunction a
    _ = ∫⁻ C : X, Ktail C s ∂(a • Rhead A) := by
          rw [lintegral_smul_measure]
          rfl
    _ ≤ ∫⁻ C : X, Ktail C s ∂Khead A := hMeasure

/-- Every finite literal C5 deterministic heat-bath schedule dominates the
corresponding independent Haar-refresh schedule.  The coefficient is exactly
the product of the one-link Harnack minorization coefficients.

This statement is finite-volume and non-circular: it uses neither terminal
covariance decay nor a remote-residual smallness estimate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDeterministicScheduleKernel_lower_bound_haarRefreshSchedule
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (fibers : List (PeriodicHypercubicEvenSpatialSliceLink H))
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHaarMinorizationCoefficient
        beta) ^ fibers.length •
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceHaarRefreshScheduleKernel
        H N fibers A ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDeterministicScheduleKernel
        H N hN beta hbeta B target source k g₂ fibers A := by
  induction fibers generalizing A with
  | nil =>
      simp
  | cons fiber fibers ih =>
      let eps : ℝ≥0∞ :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHaarMinorizationCoefficient
          beta
      let Rhead :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHaarRefreshKernel
          H N fiber
      let Khead :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
          H N hN beta hbeta B target source fiber k g₂
      let Rtail :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceHaarRefreshScheduleKernel
          H N fibers
      let Ktail :=
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDeterministicScheduleKernel
          H N hN beta hbeta B target source k g₂ fibers
      have hHead : eps • Rhead A ≤ Khead A := by
        dsimp [eps, Rhead, Khead]
        simpa [
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHaarMinorizationCoefficient] using
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_lower_bound_haarRefreshKernel
            H N hN beta hbeta B target source fiber k g₂ A
      have hTail :
          ∀ C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
            eps ^ fibers.length • Rtail C ≤ Ktail C := by
        intro C
        dsimp [eps, Rtail, Ktail]
        exact ih C
      have hComp :=
        finiteMarkovKernel_comp_measure_minorization
          Khead Ktail Rhead Rtail eps (eps ^ fibers.length) A hHead hTail
      simpa [
        eps,
        Rhead,
        Khead,
        Rtail,
        Ktail,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceHaarRefreshScheduleKernel_cons,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDeterministicScheduleKernel_cons,
        pow_succ,
        mul_comm,
        mul_left_comm,
        mul_assoc] using hComp

end

end MathlibAnalytic
end MGAP4D
