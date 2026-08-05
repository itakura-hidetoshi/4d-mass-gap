import MGAP4D.MathlibAnalytic.FinitePositiveWeightConditionalL1Telescoping
import MGAP4D.MathlibAnalytic.FinitePositiveWeightParallelDisagreementProfile
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Unit cost of a disagreement in a finite pair. -/
def finitePairDisagreementIndicator
    {G : Type}
    [DecidableEq G]
    (z : G × G) : ℝ :=
  if z.1 = z.2 then 0 else 1

/-- Hamming cost of a pair-valued finite product configuration. -/
def finitePairHammingCost
    {ι G : Type}
    [DecidableEq ι]
    [DecidableEq G]
    [Fintype ι]
    (output : ι → G × G) : ℝ :=
  ∑ target : ι, finitePairDisagreementIndicator (output target)

/-- Pair-valued Hamming cost is exactly the existing real Hamming distance of
the two coordinate projections. -/
theorem finitePairHammingCost_eq_finiteProductHammingDistanceReal
    {ι G : Type}
    [DecidableEq ι]
    [DecidableEq G]
    [Fintype ι]
    (output : ι → G × G) :
    finitePairHammingCost output =
      finiteProductHammingDistanceReal
        (fun i => (output i).1) (fun i => (output i).2) := by
  classical
  symm
  unfold finiteProductHammingDistanceReal finiteProductDisagreementFinset
    finitePairHammingCost finitePairDisagreementIndicator
  calc
    ((Finset.univ.filter fun i : ι =>
        (output i).1 ≠ (output i).2).card : ℝ) =
      ∑ i in Finset.univ.filter (fun i : ι =>
        (output i).1 ≠ (output i).2), (1 : ℝ) := by simp
    _ = ∑ i in (Finset.univ : Finset ι),
        if (output i).1 ≠ (output i).2 then (1 : ℝ) else 0 := by
      rw [Finset.sum_filter]
    _ = ∑ i : ι,
        if (output i).1 = (output i).2 then 0 else 1 := by
      apply Finset.sum_congr rfl
      intro i _hi
      by_cases hEq : (output i).1 = (output i).2 <;> simp [hEq]

namespace FiniteRealCouplingData

variable {G : Type} [DecidableEq G] [Fintype G]
variable {P Q : FiniteRealProbabilityData G}

/-- The expected pair-disagreement indicator under an arbitrary finite
coupling is exactly its disagreement mass. -/
theorem pairDisagreementExpectation_eq_disagreementMass
    (C : FiniteRealCouplingData P Q) :
    (∑ z : G × G,
      C.joint z.1 z.2 * finitePairDisagreementIndicator z) =
      C.disagreementMass := by
  classical
  rw [Fintype.sum_prod_type]
  unfold finitePairDisagreementIndicator
  calc
    (∑ g : G, ∑ h : G,
      C.joint g h * if g = h then 0 else 1) =
        ∑ g : G, ∑ h : G,
          (C.joint g h - if g = h then C.joint g h else 0) := by
      apply Finset.sum_congr rfl
      intro g _hg
      apply Finset.sum_congr rfl
      intro h _hh
      by_cases hEq : g = h <;> simp [hEq]
    _ = ∑ g : G,
        ((∑ h : G, C.joint g h) -
          ∑ h : G, if g = h then C.joint g h else 0) := by
      apply Finset.sum_congr rfl
      intro g _hg
      rw [Finset.sum_sub_distrib]
    _ = (∑ g : G, ∑ h : G, C.joint g h) -
        ∑ g : G, ∑ h : G,
          if g = h then C.joint g h else 0 := by
      rw [Finset.sum_sub_distrib]
    _ = 1 - ∑ g : G, C.joint g g := by
      rw [C.totalMass_eq_one]
      congr 1
      apply Finset.sum_congr rfl
      intro g _hg
      simp
    _ = C.disagreementMass := by
      rfl

end FiniteRealCouplingData

/-- Product joint law of a finite family of couplings, represented as a
pair-valued output configuration. -/
def finiteRealCouplingProductJoint
    {ι G : Type}
    [DecidableEq ι]
    [DecidableEq G]
    [Fintype ι]
    [Fintype G]
    {P Q : ι → FiniteRealProbabilityData G}
    (C : ∀ target : ι, FiniteRealCouplingData (P target) (Q target))
    (output : ι → G × G) : ℝ :=
  ∏ target : ι,
    (C target).joint (output target).1 (output target).2

/-- The product joint law has total mass one. -/
theorem finiteRealCouplingProductJoint_sum_eq_one
    {ι G : Type}
    [DecidableEq ι]
    [DecidableEq G]
    [Fintype ι]
    [Fintype G]
    {P Q : ι → FiniteRealProbabilityData G}
    (C : ∀ target : ι, FiniteRealCouplingData (P target) (Q target)) :
    ∑ output : ι → G × G,
      finiteRealCouplingProductJoint C output = 1 := by
  classical
  unfold finiteRealCouplingProductJoint
  change
    ∑ output ∈ (Finset.univ : Finset (ι → G × G)),
      ∏ target : ι,
        (C target).joint (output target).1 (output target).2 = 1
  rw [show (Finset.univ : Finset (ι → G × G)) =
      Fintype.piFinset
        (fun _ : ι => (Finset.univ : Finset (G × G))) by
    exact Fintype.piFinset_univ.symm]
  rw [Finset.sum_prod_piFinset]
  have hLocal (target : ι) :
      ∑ z : G × G, (C target).joint z.1 z.2 = 1 := by
    rw [Fintype.sum_prod_type]
    exact (C target).totalMass_eq_one
  simp_rw [hLocal]
  exact Finset.prod_const_one

/-- At one target coordinate, expectation under the product joint law reduces
to expectation under that target's coupling. -/
theorem finiteRealCouplingProduct_coordinateDisagreementExpectation
    {ι G : Type}
    [DecidableEq ι]
    [DecidableEq G]
    [Fintype ι]
    [Fintype G]
    {P Q : ι → FiniteRealProbabilityData G}
    (C : ∀ target : ι, FiniteRealCouplingData (P target) (Q target))
    (target : ι) :
    (∑ output : ι → G × G,
      finiteRealCouplingProductJoint C output *
        finitePairDisagreementIndicator (output target)) =
      (C target).disagreementMass := by
  classical
  let modified : ι → (G × G) → ℝ := fun i z =>
    if i = target then
      (C i).joint z.1 z.2 * finitePairDisagreementIndicator z
    else
      (C i).joint z.1 z.2
  have hIndicatorProd (output : ι → G × G) :
      (∏ i : ι,
        if i = target then
          finitePairDisagreementIndicator (output i)
        else 1) =
      finitePairDisagreementIndicator (output target) := by
    calc
      (∏ i : ι,
        if i = target then
          finitePairDisagreementIndicator (output i)
        else 1) =
          (if target = target then
            finitePairDisagreementIndicator (output target)
          else 1) :=
        Fintype.prod_eq_single target (by
          intro i hi
          simp [hi])
      _ = finitePairDisagreementIndicator (output target) := by simp
  have hProduct (output : ι → G × G) :
      finiteRealCouplingProductJoint C output *
          finitePairDisagreementIndicator (output target) =
        ∏ i : ι, modified i (output i) := by
    unfold finiteRealCouplingProductJoint
    rw [← hIndicatorProd output, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _hi
    by_cases hit : i = target <;> simp [modified, hit]
  calc
    (∑ output : ι → G × G,
      finiteRealCouplingProductJoint C output *
        finitePairDisagreementIndicator (output target)) =
        ∑ output : ι → G × G,
          ∏ i : ι, modified i (output i) := by
      apply Finset.sum_congr rfl
      intro output _hOutput
      exact hProduct output
    _ = ∏ i : ι, ∑ z : G × G, modified i z := by
      change
        ∑ output ∈ (Finset.univ : Finset (ι → G × G)),
          ∏ i : ι, modified i (output i) = _
      rw [show (Finset.univ : Finset (ι → G × G)) =
          Fintype.piFinset
            (fun _ : ι => (Finset.univ : Finset (G × G))) by
        exact Fintype.piFinset_univ.symm]
      rw [Finset.sum_prod_piFinset]
    _ = ∏ i : ι,
        if i = target then (C i).disagreementMass else 1 := by
      apply Finset.prod_congr rfl
      intro i _hi
      by_cases hit : i = target
      · subst i
        simp only [modified, if_pos rfl]
        exact (C target).pairDisagreementExpectation_eq_disagreementMass
      · simp only [modified, if_neg hit]
        rw [Fintype.sum_prod_type]
        exact (C i).totalMass_eq_one
    _ = (C target).disagreementMass := by
      calc
        (∏ i : ι,
          if i = target then (C i).disagreementMass else 1) =
            (if target = target then
              (C target).disagreementMass else 1) :=
          Fintype.prod_eq_single target (by
            intro i hi
            simp [hi])
        _ = (C target).disagreementMass := by simp

/-- Expected pair-Hamming cost under a product coupling. -/
def finiteRealCouplingProductExpectedHamming
    {ι G : Type}
    [DecidableEq ι]
    [DecidableEq G]
    [Fintype ι]
    [Fintype G]
    {P Q : ι → FiniteRealProbabilityData G}
    (C : ∀ target : ι, FiniteRealCouplingData (P target) (Q target)) : ℝ :=
  ∑ output : ι → G × G,
    finiteRealCouplingProductJoint C output * finitePairHammingCost output

/-- Expected Hamming cost under the product joint law is exactly the sum of
the coordinate coupling disagreement masses. -/
theorem finiteRealCouplingProductExpectedHamming_eq_sum_disagreementMass
    {ι G : Type}
    [DecidableEq ι]
    [DecidableEq G]
    [Fintype ι]
    [Fintype G]
    {P Q : ι → FiniteRealProbabilityData G}
    (C : ∀ target : ι, FiniteRealCouplingData (P target) (Q target)) :
    finiteRealCouplingProductExpectedHamming C =
      ∑ target : ι, (C target).disagreementMass := by
  unfold finiteRealCouplingProductExpectedHamming finitePairHammingCost
  calc
    (∑ output : ι → G × G,
      finiteRealCouplingProductJoint C output *
        ∑ target : ι,
          finitePairDisagreementIndicator (output target)) =
      ∑ output : ι → G × G, ∑ target : ι,
        finiteRealCouplingProductJoint C output *
          finitePairDisagreementIndicator (output target) := by
        apply Finset.sum_congr rfl
        intro output _hOutput
        rw [Finset.mul_sum]
    _ = ∑ target : ι, ∑ output : ι → G × G,
        finiteRealCouplingProductJoint C output *
          finitePairDisagreementIndicator (output target) := by
      rw [Finset.sum_comm]
    _ = ∑ target : ι, (C target).disagreementMass := by
      apply Finset.sum_congr rfl
      intro target _hTarget
      exact finiteRealCouplingProduct_coordinateDisagreementExpectation C target

/-- Pair-valued form of the canonical parallel positive-weight overlap joint. -/
def finitePositiveWeightParallelOverlapPairJoint
    {ι G : Type}
    [DecidableEq ι]
    [DecidableEq G]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ configuration : ι → G, 0 < weight configuration)
    (leftEnvironment rightEnvironment : ι → G)
    (output : ι → G × G) : ℝ :=
  finiteRealCouplingProductJoint
    (fun target =>
      finitePositiveWeightSingleSiteOverlapCouplingData
        weight hweight leftEnvironment rightEnvironment target)
    output

/-- The pair-valued product joint is pointwise the existing two-output
parallel overlap coupling. -/
theorem finitePositiveWeightParallelOverlapPairJoint_eq
    {ι G : Type}
    [DecidableEq ι]
    [DecidableEq G]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ configuration : ι → G, 0 < weight configuration)
    (leftEnvironment rightEnvironment : ι → G)
    (output : ι → G × G) :
    finitePositiveWeightParallelOverlapPairJoint
        weight hweight leftEnvironment rightEnvironment output =
      finitePositiveWeightParallelOverlapCoupling
        weight hweight leftEnvironment rightEnvironment
        (fun i => (output i).1) (fun i => (output i).2) := by
  rfl

/-- The pair-valued parallel overlap joint has total mass one. -/
theorem finitePositiveWeightParallelOverlapPairJoint_sum_eq_one
    {ι G : Type}
    [DecidableEq ι]
    [DecidableEq G]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ configuration : ι → G, 0 < weight configuration)
    (leftEnvironment rightEnvironment : ι → G) :
    ∑ output : ι → G × G,
      finitePositiveWeightParallelOverlapPairJoint
        weight hweight leftEnvironment rightEnvironment output = 1 := by
  exact finiteRealCouplingProductJoint_sum_eq_one
    (fun target =>
      finitePositiveWeightSingleSiteOverlapCouplingData
        weight hweight leftEnvironment rightEnvironment target)

/-- Actual expected Hamming cost of the canonical parallel overlap joint. -/
def finitePositiveWeightParallelOverlapPairExpectedHamming
    {ι G : Type}
    [DecidableEq ι]
    [DecidableEq G]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ configuration : ι → G, 0 < weight configuration)
    (leftEnvironment rightEnvironment : ι → G) : ℝ :=
  finiteRealCouplingProductExpectedHamming
    (fun target =>
      finitePositiveWeightSingleSiteOverlapCouplingData
        weight hweight leftEnvironment rightEnvironment target)

/-- The true expected Hamming cost under the correct-marginal parallel product
joint law is exactly the previously defined total coordinate disagreement. -/
theorem finitePositiveWeightParallelOverlapPairExpectedHamming_eq_totalCoordinateDisagreement
    {ι G : Type}
    [DecidableEq ι]
    [DecidableEq G]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ configuration : ι → G, 0 < weight configuration)
    (leftEnvironment rightEnvironment : ι → G) :
    finitePositiveWeightParallelOverlapPairExpectedHamming
        weight hweight leftEnvironment rightEnvironment =
      finitePositiveWeightParallelTotalCoordinateDisagreement
        weight hweight leftEnvironment rightEnvironment := by
  unfold finitePositiveWeightParallelOverlapPairExpectedHamming
  rw [finiteRealCouplingProductExpectedHamming_eq_sum_disagreementMass]
  rfl

end

end MathlibAnalytic
end MGAP4D
