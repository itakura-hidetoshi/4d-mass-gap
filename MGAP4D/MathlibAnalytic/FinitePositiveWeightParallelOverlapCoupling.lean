import MGAP4D.MathlibAnalytic.FinitePositiveWeightSingleSiteOverlapCoupling
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Parallel conditional-resampling kernel: every output coordinate is sampled
independently from its one-site conditional law in the common input
environment. -/
def finitePositiveWeightParallelKernel
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (environment output : ι → G) : ℝ :=
  ∏ target : ι,
    finitePositiveWeightSingleSiteProbability
      weight environment target (output target)

/-- The parallel kernel is nonnegative for a strictly positive weight. -/
theorem finitePositiveWeightParallelKernel_nonneg
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ configuration : ι → G, 0 < weight configuration)
    (environment output : ι → G) :
    0 ≤ finitePositiveWeightParallelKernel weight environment output := by
  unfold finitePositiveWeightParallelKernel
  exact Finset.prod_nonneg fun target _hTarget =>
    le_of_lt
      (finitePositiveWeightSingleSiteProbability_pos
        weight hweight environment target (output target))

/-- The parallel conditional-resampling kernel has total mass one. -/
theorem finitePositiveWeightParallelKernel_sum_eq_one
    {ι G : Type}
    [DecidableEq ι]
    [DecidableEq G]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ configuration : ι → G, 0 < weight configuration)
    (environment : ι → G) :
    ∑ output : ι → G,
      finitePositiveWeightParallelKernel weight environment output = 1 := by
  classical
  unfold finitePositiveWeightParallelKernel
  change
    ∑ output ∈ (Finset.univ : Finset (ι → G)),
      ∏ target : ι,
        finitePositiveWeightSingleSiteProbability
          weight environment target (output target) = 1
  rw [← Fintype.piFinset_univ]
  rw [Finset.sum_prod_piFinset]
  simp_rw [finitePositiveWeightSingleSiteProbability_sum_eq_one
    weight hweight environment]
  exact Finset.prod_const_one

/-- The parallel kernel packaged as a finite real probability law. -/
noncomputable def finitePositiveWeightParallelProbabilityData
    {ι G : Type}
    [DecidableEq ι]
    [DecidableEq G]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ configuration : ι → G, 0 < weight configuration)
    (environment : ι → G) :
    FiniteRealProbabilityData (ι → G) :=
  { probability := finitePositiveWeightParallelKernel weight environment
    probability_nonneg :=
      finitePositiveWeightParallelKernel_nonneg weight hweight environment
    probability_sum_eq_one :=
      finitePositiveWeightParallelKernel_sum_eq_one
        weight hweight environment }

/-- Coordinatewise product of the canonical one-site overlap couplings. -/
def finitePositiveWeightParallelOverlapCoupling
    {ι G : Type}
    [DecidableEq ι]
    [DecidableEq G]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ configuration : ι → G, 0 < weight configuration)
    (leftEnvironment rightEnvironment : ι → G)
    (leftOutput rightOutput : ι → G) : ℝ :=
  ∏ target : ι,
    (finitePositiveWeightSingleSiteOverlapCouplingData
      weight hweight leftEnvironment rightEnvironment target).joint
      (leftOutput target) (rightOutput target)

/-- The coordinatewise product coupling is nonnegative. -/
theorem finitePositiveWeightParallelOverlapCoupling_nonneg
    {ι G : Type}
    [DecidableEq ι]
    [DecidableEq G]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ configuration : ι → G, 0 < weight configuration)
    (leftEnvironment rightEnvironment : ι → G)
    (leftOutput rightOutput : ι → G) :
    0 ≤ finitePositiveWeightParallelOverlapCoupling
      weight hweight leftEnvironment rightEnvironment
      leftOutput rightOutput := by
  unfold finitePositiveWeightParallelOverlapCoupling
  exact Finset.prod_nonneg fun target _hTarget =>
    (finitePositiveWeightSingleSiteOverlapCouplingData
      weight hweight leftEnvironment rightEnvironment target).joint_nonneg
      (leftOutput target) (rightOutput target)

/-- Summing the product coupling over the right output gives exactly the left
parallel conditional-resampling kernel. -/
theorem finitePositiveWeightParallelOverlapCoupling_leftMarginal
    {ι G : Type}
    [DecidableEq ι]
    [DecidableEq G]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ configuration : ι → G, 0 < weight configuration)
    (leftEnvironment rightEnvironment : ι → G)
    (leftOutput : ι → G) :
    ∑ rightOutput : ι → G,
      finitePositiveWeightParallelOverlapCoupling
        weight hweight leftEnvironment rightEnvironment
        leftOutput rightOutput =
      finitePositiveWeightParallelKernel
        weight leftEnvironment leftOutput := by
  classical
  unfold finitePositiveWeightParallelOverlapCoupling
    finitePositiveWeightParallelKernel
  rw [show (Finset.univ : Finset (ι → G)) =
      Fintype.piFinset (fun _ : ι => (Finset.univ : Finset G)) by
    exact Fintype.piFinset_univ.symm]
  rw [Finset.sum_prod_piFinset]
  simp_rw [finitePositiveWeightSingleSiteOverlapCoupling_leftMarginal]

/-- Summing the product coupling over the left output gives exactly the right
parallel conditional-resampling kernel. -/
theorem finitePositiveWeightParallelOverlapCoupling_rightMarginal
    {ι G : Type}
    [DecidableEq ι]
    [DecidableEq G]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ configuration : ι → G, 0 < weight configuration)
    (leftEnvironment rightEnvironment : ι → G)
    (rightOutput : ι → G) :
    ∑ leftOutput : ι → G,
      finitePositiveWeightParallelOverlapCoupling
        weight hweight leftEnvironment rightEnvironment
        leftOutput rightOutput =
      finitePositiveWeightParallelKernel
        weight rightEnvironment rightOutput := by
  classical
  unfold finitePositiveWeightParallelOverlapCoupling
    finitePositiveWeightParallelKernel
  rw [show (Finset.univ : Finset (ι → G)) =
      Fintype.piFinset (fun _ : ι => (Finset.univ : Finset G)) by
    exact Fintype.piFinset_univ.symm]
  calc
    (∑ leftOutput ∈ Fintype.piFinset
        (fun _ : ι => (Finset.univ : Finset G)),
      ∏ target : ι,
        (finitePositiveWeightSingleSiteOverlapCouplingData
          weight hweight leftEnvironment rightEnvironment target).joint
          (leftOutput target) (rightOutput target)) =
        ∏ target : ι, ∑ g : G,
          (finitePositiveWeightSingleSiteOverlapCouplingData
            weight hweight leftEnvironment rightEnvironment target).joint
            g (rightOutput target) := by
      simpa using
        (Finset.sum_prod_piFinset
          (s := (Finset.univ : Finset G))
          (g := fun target g =>
            (finitePositiveWeightSingleSiteOverlapCouplingData
              weight hweight leftEnvironment rightEnvironment target).joint
              g (rightOutput target)))
    _ = ∏ target : ι,
        finitePositiveWeightSingleSiteProbability
          weight rightEnvironment target (rightOutput target) := by
      apply Finset.prod_congr rfl
      intro target _hTarget
      exact finitePositiveWeightSingleSiteOverlapCoupling_rightMarginal
        weight hweight leftEnvironment rightEnvironment target
          (rightOutput target)

/-- The canonical correct-marginal coupling of the two parallel conditional
kernels. -/
noncomputable def finitePositiveWeightParallelOverlapCouplingData
    {ι G : Type}
    [DecidableEq ι]
    [DecidableEq G]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ configuration : ι → G, 0 < weight configuration)
    (leftEnvironment rightEnvironment : ι → G) :
    FiniteRealCouplingData
      (finitePositiveWeightParallelProbabilityData
        weight hweight leftEnvironment)
      (finitePositiveWeightParallelProbabilityData
        weight hweight rightEnvironment) :=
  { joint := finitePositiveWeightParallelOverlapCoupling
      weight hweight leftEnvironment rightEnvironment
    joint_nonneg :=
      finitePositiveWeightParallelOverlapCoupling_nonneg
        weight hweight leftEnvironment rightEnvironment
    left_marginal :=
      finitePositiveWeightParallelOverlapCoupling_leftMarginal
        weight hweight leftEnvironment rightEnvironment
    right_marginal :=
      finitePositiveWeightParallelOverlapCoupling_rightMarginal
        weight hweight leftEnvironment rightEnvironment }

end

end MathlibAnalytic
end MGAP4D
