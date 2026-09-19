import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceOneLinkHaarRefreshKernel
import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceDeterministicScheduleKernel
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

/-- The single-coordinate Haar refresh is an actual Markov kernel. -/
noncomputable instance
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHaarRefreshKernel_isMarkovKernel
    (H N : ℕ)
    (fiber : PeriodicHypercubicEvenSpatialSliceLink H) :
    IsMarkovKernel
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHaarRefreshKernel
        H N fiber) := by
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHaarRefreshKernel]
  exact
    IsMarkovKernel.map
      (Kernel.id ×ₖ
        Kernel.const
          (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
          (normalizedCompactHaar (Matrix.specialUnitaryGroup (Fin N) ℂ)))
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkUpdate_uncurry_measurable
        H N fiber)

/-- Pure Haar-refresh comparison kernel for a finite ordered list of spatial
links. The head coordinate is refreshed first, matching the convention used by
the literal reference deterministic heat-bath schedule. -/
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

/-- Every finite pure Haar-refresh schedule is a Markov kernel. -/
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

/-- The schedule construction is compatible with append: running xs first
and then ys is kernel composition in the same convention as the physical
schedule. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceHaarRefreshScheduleKernel_append
    (H N : ℕ)
    (xs ys : List (PeriodicHypercubicEvenSpatialSliceLink H)) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceHaarRefreshScheduleKernel
        H N (xs ++ ys) =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceHaarRefreshScheduleKernel
          H N ys ∘ₖ
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceHaarRefreshScheduleKernel
          H N xs := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [
        List.cons_append,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceHaarRefreshScheduleKernel_cons,
        ih]
      rw [Kernel.comp_assoc]


/-- Pointwise lower bounds compose multiplicatively through Markov-kernel
composition.  This is the positive-kernel algebra used to iterate one-link
Doeblin minorization through a finite schedule. -/
theorem kernel_comp_pointwise_smul_lower_bound
    {α : Type*}
    [MeasurableSpace α]
    (c d : ℝ≥0∞)
    (K K' L L' : Kernel α α)
    (hK : ∀ a, c • K' a ≤ K a)
    (hL : ∀ a, d • L' a ≤ L a)
    (a : α) :
    (c * d) • ((L' ∘ₖ K') a) ≤ (L ∘ₖ K) a := by
  apply Measure.le_iff.2
  intro s hs
  simp only [Measure.smul_apply, smul_eq_mul, Kernel.comp_apply' _ _ _ hs]
  calc
    (c * d) * ∫⁻ b, L' b s ∂K' a =
        ∫⁻ b, d * L' b s ∂(c • K' a) := by
      rw [lintegral_smul_measure, smul_eq_mul,
        lintegral_const_mul d (L'.measurable_coe hs)]
      ac_rfl
    _ ≤ ∫⁻ b, d * L' b s ∂K a := by
      exact lintegral_mono' (hK a) le_rfl
    _ ≤ ∫⁻ b, L b s ∂K a := by
      apply lintegral_mono
      intro b
      simpa only [Measure.smul_apply, smul_eq_mul] using
        Measure.le_iff'.1 (hL b) s

/-- The literal reference heat-bath schedule dominates the corresponding pure
Haar-refresh schedule with the product of the one-link Doeblin coefficients.

The coefficient is exactly exp(-32 beta) to the schedule length.  It may decay
with finite volume once a full sweep is chosen; no volume-uniform mixing rate is
claimed or needed here.  In particular this theorem is independent of terminal
covariance decay and of the remote-residual route. -/
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
    ((ENNReal.ofReal (Real.exp (32 * beta)))⁻¹ ^ fibers.length) •
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceHaarRefreshScheduleKernel
          H N fibers A ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDeterministicScheduleKernel
        H N hN beta hbeta B target source k g₂ fibers A := by
  induction fibers with
  | nil =>
      simp
  | cons fiber fibers ih =>
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceHaarRefreshScheduleKernel_cons,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDeterministicScheduleKernel_cons]
      have hStep :
          ∀ X : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
            (ENNReal.ofReal (Real.exp (32 * beta)))⁻¹ •
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHaarRefreshKernel
                  H N fiber X ≤
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
                H N hN beta hbeta B target source fiber k g₂ X := by
        intro X
        exact
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel_lower_bound_haarRefreshKernel
            H N hN beta hbeta B target source fiber k g₂ X
      have hTail :
          ∀ X : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N,
            ((ENNReal.ofReal (Real.exp (32 * beta)))⁻¹ ^ fibers.length) •
                periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceHaarRefreshScheduleKernel
                  H N fibers X ≤
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDeterministicScheduleKernel
                H N hN beta hbeta B target source k g₂ fibers X := by
        intro X
        exact ih X
      have hComp :=
        kernel_comp_pointwise_smul_lower_bound
          (c := (ENNReal.ofReal (Real.exp (32 * beta)))⁻¹)
          (d := (ENNReal.ofReal (Real.exp (32 * beta)))⁻¹ ^ fibers.length)
          (K :=
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHeatBathKernel
              H N hN beta hbeta B target source fiber k g₂)
          (K' :=
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHaarRefreshKernel
              H N fiber)
          (L :=
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDeterministicScheduleKernel
              H N hN beta hbeta B target source k g₂ fibers)
          (L' :=
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceHaarRefreshScheduleKernel
              H N fibers)
          hStep hTail A
      simpa [List.length_cons, pow_succ, mul_comm] using hComp

end

end MathlibAnalytic
end MGAP4D
