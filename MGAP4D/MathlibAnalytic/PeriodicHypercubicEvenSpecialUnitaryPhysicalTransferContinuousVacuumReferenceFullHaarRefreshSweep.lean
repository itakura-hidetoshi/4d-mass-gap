import MGAP4D.MathlibAnalytic.PeriodicHypercubicEvenSpecialUnitaryPhysicalTransferContinuousVacuumReferenceHaarRefreshScheduleMinorization
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

local instance referenceFullHaarRefreshSweepSpecialUnitaryIsTopologicalGroup
    (N : ℕ) : IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupIsTopologicalGroup N

local instance referenceFullHaarRefreshSweepSpecialUnitaryCompactSpace
    (N : ℕ) : CompactSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupCompactSpace N

local instance referenceFullHaarRefreshSweepSpecialUnitarySecondCountableTopology
    (N : ℕ) : SecondCountableTopology (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupSecondCountableTopology N

local instance referenceFullHaarRefreshSweepSpecialUnitaryMeasurableSpace
    (N : ℕ) : MeasurableSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupMeasurableSpace N

local instance referenceFullHaarRefreshSweepSpecialUnitaryBorelSpace
    (N : ℕ) : BorelSpace (Matrix.specialUnitaryGroup (Fin N) ℂ) :=
  specialUnitaryGroupBorelSpace N

local instance referenceFullHaarRefreshSweepSpatialLinkFintype
    (H : ℕ) : Fintype (PeriodicHypercubicEvenSpatialSliceLink H) :=
  Fintype.ofFinite _

/-- A Haar-refresh schedule only remembers coordinates not refreshed by the
schedule.  If two starting configurations agree off the listed fibers, the
final schedule laws are exactly equal.

This is a purely finite-product Markov-kernel statement.  No covariance decay,
remote-residual estimate, or sweep contraction is used. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceHaarRefreshScheduleKernel_apply_eq_of_eq_off_schedule
    (H N : ℕ)
    (fibers : List (PeriodicHypercubicEvenSpatialSliceLink H))
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (hAB :
      ∀ e : PeriodicHypercubicEvenSpatialSliceLink H,
        e ∉ fibers → A e = B e) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceHaarRefreshScheduleKernel
        H N fibers A =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceHaarRefreshScheduleKernel
        H N fibers B := by
  induction fibers generalizing A B with
  | nil =>
      have hEq : A = B := by
        funext e
        exact hAB e (by simp)
      subst B
      rfl
  | cons fiber fibers ih =>
      ext s hs
      rw [
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceHaarRefreshScheduleKernel_cons,
        Kernel.comp_apply' _ _ A hs,
        Kernel.comp_apply' _ _ B hs,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHaarRefreshKernel_apply
          H N fiber A,
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHaarRefreshKernel_apply
          H N fiber B]
      unfold
        periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHaarRefreshMeasure
      have hUpdateA :
          Measurable
            (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
              Function.update A fiber g) := by
        exact
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkUpdate_uncurry_measurable
            H N fiber).comp (measurable_const.prodMk measurable_id)
      have hUpdateB :
          Measurable
            (fun g : Matrix.specialUnitaryGroup (Fin N) ℂ =>
              Function.update B fiber g) := by
        exact
          (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkUpdate_uncurry_measurable
            H N fiber).comp (measurable_const.prodMk measurable_id)
      have hTailMeas :
          Measurable
            (fun C : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N =>
              periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceHaarRefreshScheduleKernel
                H N fibers C s) :=
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceHaarRefreshScheduleKernel
          H N fibers).measurable_coe hs
      rw [
        lintegral_map hTailMeas hUpdateA,
        lintegral_map hTailMeas hUpdateB]
      apply lintegral_congr
      intro g
      have hTailEq :
          periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceHaarRefreshScheduleKernel
              H N fibers (Function.update A fiber g) =
            periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceHaarRefreshScheduleKernel
              H N fibers (Function.update B fiber g) := by
        apply ih
        intro e he
        by_cases hef : e = fiber
        · subst e
          simp
        · simp [Function.update, hef]
          exact hAB e (by simp [hef, he])
      rw [hTailEq]

/-- Canonical finite schedule listing every actual spatial link exactly once. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
    (H : ℕ) : List (PeriodicHypercubicEvenSpatialSliceLink H) := by
  classical
  exact Finset.univ.toList

@[simp] theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReference_mem_allSpatialLinkSchedule
    (H : ℕ)
    (e : PeriodicHypercubicEvenSpatialSliceLink H) :
    e ∈
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
        H := by
  classical
  simp [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule]

/-- A complete Haar-refresh sweep forgets the initial configuration exactly. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFullHaarRefreshSweep_apply_eq
    (H N : ℕ)
    (A B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceHaarRefreshScheduleKernel
        H N
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
          H) A =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceHaarRefreshScheduleKernel
        H N
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
          H) B := by
  apply
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceHaarRefreshScheduleKernel_apply_eq_of_eq_off_schedule
  intro e he
  exact False.elim (he
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReference_mem_allSpatialLinkSchedule
      H e))

/-- Common reference measure generated by one complete independent Haar-refresh
sweep.  The previous theorem shows that the chosen constant starting
configuration is immaterial. -/
noncomputable def
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFullHaarRefreshMeasure
    (H N : ℕ) :
    Measure (PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :=
  periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceHaarRefreshScheduleKernel
    H N
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
      H)
    (fun _ => 1)

theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFullHaarRefreshSweep_apply_eq_measure
    (H N : ℕ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceHaarRefreshScheduleKernel
        H N
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
          H) A =
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFullHaarRefreshMeasure
        H N := by
  exact
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFullHaarRefreshSweep_apply_eq
      H N A (fun _ => 1)

/-- The actual deterministic heat-bath sweep through every spatial link
dominates one common, initial-state-independent probability law.

The coefficient may depend strongly on the finite volume through the number of
links.  That is sufficient for fixed-volume ergodicity and does not assert a
volume-uniform mixing rate. -/
theorem
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFullDeterministicSweep_lower_bound_commonHaarRefresh
    (H N : ℕ)
    (hN : 0 < N)
    (beta : ℝ)
    (hbeta : 0 ≤ beta)
    (B : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N)
    (target source : PeriodicHypercubicEvenSpatialSliceLink H)
    (k g₂ : Matrix.specialUnitaryGroup (Fin N) ℂ)
    (A : PeriodicHypercubicEvenSpecialUnitarySpatialSliceConfiguration H N) :
    (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceOneLinkHaarMinorizationCoefficient
        beta) ^
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
          H).length •
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFullHaarRefreshMeasure
        H N ≤
      periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDeterministicScheduleKernel
        H N hN beta hbeta B target source k g₂
        (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
          H) A := by
  have h :=
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceDeterministicScheduleKernel_lower_bound_haarRefreshSchedule
      H N hN beta hbeta B target source k g₂
      (periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceAllSpatialLinkSchedule
        H) A
  rw [
    periodicHypercubicEvenSpecialUnitaryPhysicalOneSlabContinuousVacuumReferenceFullHaarRefreshSweep_apply_eq_measure]
    at h
  exact h

end

end MathlibAnalytic
end MGAP4D
