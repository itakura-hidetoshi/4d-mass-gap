import MGAP4D.MathlibAnalytic.FinitePositiveWeightReciprocalInfluenceKernelResponse
import MGAP4D.MathlibAnalytic.ContinuousCompactOrientedGaugeWilsonFiniteHeatBathScheduleInfluenceKernel
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Ordered deterministic iteration of one-target influence-kernel variation
updates.  The tail schedule acts first, matching the observable-action and
finite heat-bath schedule conventions already used in this repository. -/
def finiteInfluenceKernelDeterministicScheduleVariation
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (variation : ι → ℝ) : List ι → ι → ℝ
  | [], source => variation source
  | target :: targets, source =>
      finiteInfluenceKernelUpdatedVariation
        K
        (finiteInfluenceKernelDeterministicScheduleVariation K variation targets)
        target source

@[simp] theorem finiteInfluenceKernelDeterministicScheduleVariation_nil
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (variation : ι → ℝ)
    (source : ι) :
    finiteInfluenceKernelDeterministicScheduleVariation K variation [] source =
      variation source := by
  rfl

@[simp] theorem finiteInfluenceKernelDeterministicScheduleVariation_cons
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (variation : ι → ℝ)
    (target : ι)
    (targets : List ι)
    (source : ι) :
    finiteInfluenceKernelDeterministicScheduleVariation
        K variation (target :: targets) source =
      finiteInfluenceKernelUpdatedVariation
        K
        (finiteInfluenceKernelDeterministicScheduleVariation K variation targets)
        target source := by
  rfl

/-- Deterministic schedules preserve nonnegative variation profiles. -/
theorem finiteInfluenceKernelDeterministicScheduleVariation_nonneg
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (variation : ι → ℝ)
    (hVariation : ∀ e : ι, 0 ≤ variation e) :
    ∀ (targets : List ι) (source : ι),
      0 ≤ finiteInfluenceKernelDeterministicScheduleVariation
        K variation targets source := by
  intro targets
  induction targets with
  | nil =>
      intro source
      exact hVariation source
  | cons target targets ih =>
      intro source
      rw [finiteInfluenceKernelDeterministicScheduleVariation_cons]
      exact
        finiteInfluenceKernelUpdatedVariation_nonneg
          K
          (finiteInfluenceKernelDeterministicScheduleVariation K variation targets)
          ih target source

/-- Concatenating ordered schedules is exactly composition of their deterministic
variation actions.  Because tails act first, the right schedule is propagated
first and the left schedule acts outside it. -/
theorem finiteInfluenceKernelDeterministicScheduleVariation_append
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (variation : ι → ℝ)
    (left right : List ι)
    (source : ι) :
    finiteInfluenceKernelDeterministicScheduleVariation
        K variation (left ++ right) source =
      finiteInfluenceKernelDeterministicScheduleVariation
        K
        (finiteInfluenceKernelDeterministicScheduleVariation K variation right)
        left source := by
  induction left generalizing source with
  | nil =>
      simp
  | cons target left ih =>
      rw [List.cons_append]
      rw [finiteInfluenceKernelDeterministicScheduleVariation_cons]
      rw [finiteInfluenceKernelDeterministicScheduleVariation_cons]
      unfold finiteInfluenceKernelUpdatedVariation
      by_cases h : source = target
      · simp [h]
      · simp only [h, if_false]
        rw [ih source, ih target]

/-- The ordered deterministic update profile is exactly the linear action of the
already-defined finite heat-bath schedule influence kernel. -/
theorem finiteInfluenceKernelDeterministicScheduleVariation_eq_sum_scheduleInfluenceKernel
    {ι : Type}
    [DecidableEq ι]
    [Fintype ι]
    (K : FiniteNonnegativeInfluenceKernelData ι)
    (variation : ι → ℝ)
    (targets : List ι)
    (source : ι) :
    finiteInfluenceKernelDeterministicScheduleVariation
        K variation targets source =
      ∑ initial : ι,
        finiteHeatBathScheduleInfluenceKernel
            K.influence targets initial source * variation initial := by
  classical
  induction targets generalizing source with
  | nil =>
      simp [finiteInfluenceKernelDeterministicScheduleVariation,
        finiteHeatBathScheduleInfluenceKernel]
  | cons target targets ih =>
      rw [finiteInfluenceKernelDeterministicScheduleVariation_cons]
      unfold finiteInfluenceKernelUpdatedVariation
      by_cases h : source = target
      · subst source
        simp [finiteHeatBathScheduleInfluenceKernel]
      · simp only [h, if_false]
        rw [ih source, ih target]
        simp only [finiteHeatBathScheduleInfluenceKernel_cons, h, if_false]
        rw [Finset.mul_sum]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro initial _
        ring

end

end MathlibAnalytic
end MGAP4D
