import MGAP4D.MathlibAnalytic.FinitePositiveWeightsRandomScanOverlapCoupling
import MGAP4D.MathlibAnalytic.FiniteRealProbabilityMixtureCouplingCost
import MGAP4D.MathlibAnalytic.FiniteRealProbabilityOverlapCouplingDisagreement
import Mathlib.Data.Finset.CastCard
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators
noncomputable section

/-- Real indicator that two coordinate values disagree. -/
def finiteRealDisagreementIndicator
    {G : Type} [DecidableEq G]
    (g h : G) : ℝ :=
  if g ≠ h then 1 else 0

/-- Hamming contribution away from one distinguished coordinate. -/
def finiteProductHammingAwayReal
    {ι G : Type} [DecidableEq ι] [DecidableEq G] [Fintype ι]
    (A B : ι → G) (target : ι) : ℝ :=
  (((finiteProductDisagreementFinset A B).erase target).card : ℝ)

/-- The full Hamming distance is the away-from-target contribution plus the
old target disagreement indicator. -/
theorem finiteProductHammingDistanceReal_eq_away_add_indicator
    {ι G : Type} [DecidableEq ι] [DecidableEq G] [Fintype ι]
    (A B : ι → G) (target : ι) :
    finiteProductHammingDistanceReal A B =
      finiteProductHammingAwayReal A B target +
        finiteRealDisagreementIndicator (A target) (B target) := by
  by_cases hEq : A target = B target
  · have hNotMem : target ∉ finiteProductDisagreementFinset A B := by
      simp [finiteProductDisagreementFinset, hEq]
    unfold finiteProductHammingDistanceReal
      finiteProductHammingAwayReal finiteRealDisagreementIndicator
    rw [Finset.erase_eq_of_notMem hNotMem]
    simp [hEq]
  · have hMem : target ∈ finiteProductDisagreementFinset A B := by
      simp [finiteProductDisagreementFinset, hEq]
    have hCard :
        (((finiteProductDisagreementFinset A B).erase target).card : ℝ) =
          ((finiteProductDisagreementFinset A B).card : ℝ) - 1 :=
      Finset.cast_card_erase_of_mem hMem
    unfold finiteProductHammingDistanceReal
      finiteProductHammingAwayReal finiteRealDisagreementIndicator
    rw [hCard]
    simp [hEq]

/-- Updating the same target on two configurations replaces only the target
membership of the disagreement set. -/
theorem finiteProductDisagreementFinset_update_sameTarget
    {ι G : Type} [DecidableEq ι] [DecidableEq G] [Fintype ι]
    (A B : ι → G) (target : ι) (g h : G) :
    finiteProductDisagreementFinset
        (Function.update A target g) (Function.update B target h) =
      if g ≠ h then
        insert target ((finiteProductDisagreementFinset A B).erase target)
      else
        (finiteProductDisagreementFinset A B).erase target := by
  ext i
  by_cases hi : i = target
  · subst i
    by_cases hgh : g = h
    · simp [finiteProductDisagreementFinset, hgh]
    · simp [finiteProductDisagreementFinset, hgh]
  · by_cases hgh : g = h
    · simp [finiteProductDisagreementFinset, Function.update, hi, hgh]
    · simp [finiteProductDisagreementFinset, Function.update, hi, hgh]

/-- Exact same-target Hamming update identity. -/
theorem finiteProductHammingDistanceReal_update_sameTarget
    {ι G : Type} [DecidableEq ι] [DecidableEq G] [Fintype ι]
    (A B : ι → G) (target : ι) (g h : G) :
    finiteProductHammingDistanceReal
        (Function.update A target g) (Function.update B target h) =
      finiteProductHammingAwayReal A B target +
        finiteRealDisagreementIndicator g h := by
  rw [finiteProductHammingDistanceReal,
    finiteProductDisagreementFinset_update_sameTarget]
  unfold finiteProductHammingAwayReal finiteRealDisagreementIndicator
  by_cases hgh : g = h
  · simp [hgh]
  · simp [hgh]

namespace FiniteRealCouplingData

variable {G : Type} [DecidableEq G] [Fintype G]
variable {P Q : FiniteRealProbabilityData G}

/-- Every finite exact coupling has total joint mass one. -/
theorem joint_sum_eq_one
    (C : FiniteRealCouplingData P Q) :
    ∑ x : G, ∑ y : G, C.joint x y = 1 := by
  calc
    (∑ x : G, ∑ y : G, C.joint x y) =
        ∑ x : G, P.probability x := by
      apply Finset.sum_congr rfl
      intro x _
      exact C.left_marginal x
    _ = 1 := P.probability_sum_eq_one

/-- The expected real disagreement indicator under a finite coupling equals
its disagreement mass. -/
theorem expectedDisagreementIndicator_eq_disagreementMass
    (C : FiniteRealCouplingData P Q) :
    (∑ x : G, ∑ y : G,
      C.joint x y * finiteRealDisagreementIndicator x y) =
      C.disagreementMass := by
  have hRow (x : G) :
      (∑ y : G, C.joint x y * finiteRealDisagreementIndicator x y) =
        P.probability x - C.joint x x := by
    calc
      (∑ y : G,
        C.joint x y * finiteRealDisagreementIndicator x y) =
          ∑ y : G,
            (C.joint x y - if y = x then C.joint x x else 0) := by
        apply Finset.sum_congr rfl
        intro y _
        by_cases hyx : y = x
        · subst y
          simp [finiteRealDisagreementIndicator]
        · have hxy : x ≠ y := Ne.symm hyx
          simp [finiteRealDisagreementIndicator, hyx, hxy]
      _ = (∑ y : G, C.joint x y) -
          ∑ y : G, if y = x then C.joint x x else 0 := by
        rw [Finset.sum_sub_distrib]
      _ = P.probability x - C.joint x x := by
        rw [C.left_marginal x]
        simp
  unfold disagreementMass diagonalMass
  calc
    (∑ x : G, ∑ y : G,
      C.joint x y * finiteRealDisagreementIndicator x y) =
        ∑ x : G, (P.probability x - C.joint x x) := by
      apply Finset.sum_congr rfl
      intro x _
      exact hRow x
    _ = (∑ x : G, P.probability x) - ∑ x : G, C.joint x x := by
      rw [Finset.sum_sub_distrib]
    _ = 1 - ∑ x : G, C.joint x x := by
      rw [P.probability_sum_eq_one]

end FiniteRealCouplingData

/-- Push-forward expectation identity for the full-configuration one-site
joint update kernel. -/
theorem finitePositiveWeightsSingleSiteJointUpdateKernel_expectedCost
    {ι G : Type} [DecidableEq ι] [DecidableEq G]
    [Fintype ι] [Fintype G] [Nonempty G]
    (leftWeight rightWeight : (ι → G) → ℝ)
    (hLeftWeight : ∀ A : ι → G, 0 < leftWeight A)
    (hRightWeight : ∀ A : ι → G, 0 < rightWeight A)
    (leftInput rightInput : ι → G) (target : ι)
    (cost : (ι → G) → (ι → G) → ℝ) :
    (∑ leftOutput : ι → G, ∑ rightOutput : ι → G,
      finitePositiveWeightsSingleSiteJointUpdateKernel
          leftWeight rightWeight hLeftWeight hRightWeight
          leftInput rightInput target leftOutput rightOutput *
        cost leftOutput rightOutput) =
      ∑ g : G, ∑ h : G,
        (finitePositiveWeightsSingleSiteOverlapCouplingData
          leftWeight rightWeight hLeftWeight hRightWeight
          leftInput rightInput target).joint g h *
        cost (Function.update leftInput target g)
          (Function.update rightInput target h) := by
  classical
  let C := finitePositiveWeightsSingleSiteOverlapCouplingData
    leftWeight rightWeight hLeftWeight hRightWeight
    leftInput rightInput target
  unfold finitePositiveWeightsSingleSiteJointUpdateKernel
  calc
    (∑ leftOutput : ι → G, ∑ rightOutput : ι → G,
      (∑ g : G, ∑ h : G,
        if Function.update leftInput target g = leftOutput ∧
            Function.update rightInput target h = rightOutput then
          C.joint g h else 0) * cost leftOutput rightOutput) =
      ∑ leftOutput : ι → G, ∑ rightOutput : ι → G,
        ∑ g : G, ∑ h : G,
          (if Function.update leftInput target g = leftOutput ∧
              Function.update rightInput target h = rightOutput then
            C.joint g h else 0) * cost leftOutput rightOutput := by
      apply Finset.sum_congr rfl
      intro leftOutput _
      apply Finset.sum_congr rfl
      intro rightOutput _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro g _
      rw [Finset.sum_mul]
    _ = ∑ leftOutput : ι → G, ∑ g : G,
        ∑ rightOutput : ι → G, ∑ h : G,
          (if Function.update leftInput target g = leftOutput ∧
              Function.update rightInput target h = rightOutput then
            C.joint g h else 0) * cost leftOutput rightOutput := by
      apply Finset.sum_congr rfl
      intro leftOutput _
      rw [Finset.sum_comm]
    _ = ∑ g : G, ∑ leftOutput : ι → G,
        ∑ rightOutput : ι → G, ∑ h : G,
          (if Function.update leftInput target g = leftOutput ∧
              Function.update rightInput target h = rightOutput then
            C.joint g h else 0) * cost leftOutput rightOutput := by
      rw [Finset.sum_comm]
    _ = ∑ g : G, ∑ leftOutput : ι → G,
        ∑ h : G, ∑ rightOutput : ι → G,
          (if Function.update leftInput target g = leftOutput ∧
              Function.update rightInput target h = rightOutput then
            C.joint g h else 0) * cost leftOutput rightOutput := by
      apply Finset.sum_congr rfl
      intro g _
      apply Finset.sum_congr rfl
      intro leftOutput _
      rw [Finset.sum_comm]
    _ = ∑ g : G, ∑ h : G,
        ∑ leftOutput : ι → G, ∑ rightOutput : ι → G,
          (if Function.update leftInput target g = leftOutput ∧
              Function.update rightInput target h = rightOutput then
            C.joint g h else 0) * cost leftOutput rightOutput := by
      apply Finset.sum_congr rfl
      intro g _
      rw [Finset.sum_comm]
    _ = ∑ g : G, ∑ h : G,
        C.joint g h *
          cost (Function.update leftInput target g)
            (Function.update rightInput target h) := by
      apply Finset.sum_congr rfl
      intro g _
      apply Finset.sum_congr rfl
      intro h _
      calc
        (∑ leftOutput : ι → G, ∑ rightOutput : ι → G,
          (if Function.update leftInput target g = leftOutput ∧
              Function.update rightInput target h = rightOutput then
            C.joint g h else 0) * cost leftOutput rightOutput) =
          ∑ leftOutput : ι → G,
            if Function.update leftInput target g = leftOutput then
              C.joint g h * cost leftOutput
                (Function.update rightInput target h)
            else 0 := by
          apply Finset.sum_congr rfl
          intro leftOutput _
          by_cases hLeft :
              Function.update leftInput target g = leftOutput
          · simp [hLeft]
          · simp [hLeft]
        _ = C.joint g h *
            cost (Function.update leftInput target g)
              (Function.update rightInput target h) := by
          simp

/-- Exact expected Hamming cost of one pushed-forward overlap update. -/
theorem finitePositiveWeightsSingleSiteJointUpdateCoupling_expectedHammingCost_eq
    {ι G : Type} [DecidableEq ι] [DecidableEq G]
    [Fintype ι] [Fintype G] [Nonempty G]
    (leftWeight rightWeight : (ι → G) → ℝ)
    (hLeftWeight : ∀ A : ι → G, 0 < leftWeight A)
    (hRightWeight : ∀ A : ι → G, 0 < rightWeight A)
    (leftInput rightInput : ι → G) (target : ι) :
    (finitePositiveWeightsSingleSiteJointUpdateCouplingData
      leftWeight rightWeight hLeftWeight hRightWeight
      leftInput rightInput target).expectedCost
        finiteProductHammingDistanceReal =
      finiteProductHammingAwayReal leftInput rightInput target +
        (finitePositiveWeightsSingleSiteOverlapCouplingData
          leftWeight rightWeight hLeftWeight hRightWeight
          leftInput rightInput target).disagreementMass := by
  let C := finitePositiveWeightsSingleSiteOverlapCouplingData
    leftWeight rightWeight hLeftWeight hRightWeight
    leftInput rightInput target
  unfold FiniteRealCouplingData.expectedCost
    finitePositiveWeightsSingleSiteJointUpdateCouplingData
  rw [finitePositiveWeightsSingleSiteJointUpdateKernel_expectedCost]
  simp_rw [finiteProductHammingDistanceReal_update_sameTarget]
  calc
    (∑ g : G, ∑ h : G,
      C.joint g h *
        (finiteProductHammingAwayReal leftInput rightInput target +
          finiteRealDisagreementIndicator g h)) =
      finiteProductHammingAwayReal leftInput rightInput target *
          (∑ g : G, ∑ h : G, C.joint g h) +
        ∑ g : G, ∑ h : G,
          C.joint g h * finiteRealDisagreementIndicator g h := by
      simp_rw [mul_add, Finset.sum_add_distrib]
      ring_nf
    _ = finiteProductHammingAwayReal leftInput rightInput target +
        C.disagreementMass := by
      rw [C.joint_sum_eq_one,
        C.expectedDisagreementIndicator_eq_disagreementMass]
      ring

/-- Influence and cross-weight source control the exact expected Hamming cost
of one shared-target overlap update. -/
theorem finitePositiveWeightsSingleSiteJointUpdateCoupling_expectedHammingCost_le
    {ι G : Type} [DecidableEq ι] [DecidableEq G]
    [Fintype ι] [Fintype G] [Nonempty G]
    (leftWeight rightWeight : (ι → G) → ℝ)
    (hLeftWeight : ∀ A : ι → G, 0 < leftWeight A)
    (hRightWeight : ∀ A : ι → G, 0 < rightWeight A)
    (D : FinitePositiveWeightNonstrictL1MatrixData leftWeight)
    (sourceBound : ι → ℝ)
    (hCross : ∀ (environment : ι → G) (target : ι),
      finitePositiveWeightSingleSiteConditionalCrossL1
          leftWeight rightWeight environment target ≤ sourceBound target)
    (leftInput rightInput : ι → G) (target : ι) :
    (finitePositiveWeightsSingleSiteJointUpdateCouplingData
      leftWeight rightWeight hLeftWeight hRightWeight
      leftInput rightInput target).expectedCost
        finiteProductHammingDistanceReal ≤
      finiteProductHammingAwayReal leftInput rightInput target +
        (2 : ℝ)⁻¹ *
          ((∑ source ∈ finiteProductDisagreementFinset
              leftInput rightInput,
              D.influence target source) + sourceBound target) := by
  rw [finitePositiveWeightsSingleSiteJointUpdateCoupling_expectedHammingCost_eq]
  exact add_le_add_right
    (finitePositiveWeightsSingleSiteOverlapCoupling_disagreementMass_le_half_mul_influence_add_source
      leftWeight rightWeight hLeftWeight hRightWeight D sourceBound hCross
      leftInput rightInput target)
    _

end
end MathlibAnalytic
end MGAP4D
