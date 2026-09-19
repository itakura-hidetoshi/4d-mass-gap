import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceOneLinkHaarRefreshKernel
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
  infer_instance

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

end

end MathlibAnalytic
end MGAP4D
