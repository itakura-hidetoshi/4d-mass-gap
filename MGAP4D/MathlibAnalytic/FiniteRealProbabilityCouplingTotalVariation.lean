import MGAP4D.MathlibAnalytic.FinitePositiveWeightRandomScanStationaryMixing
import MGAP4D.MathlibAnalytic.FiniteRealProbabilityOverlapCouplingDisagreement
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

namespace FiniteRealProbabilityData

variable {G : Type} [DecidableEq G] [Fintype G]

/-- Total-variation distance in the standard half-`L¹` normalization. -/
def totalVariationDistance
    (P Q : FiniteRealProbabilityData G) : ℝ :=
  (2 : ℝ)⁻¹ * P.l1Distance Q

/-- Total-variation distance is nonnegative. -/
theorem totalVariationDistance_nonneg
    (P Q : FiniteRealProbabilityData G) :
    0 ≤ P.totalVariationDistance Q := by
  exact mul_nonneg (by norm_num) (P.l1Distance_nonneg Q)

end FiniteRealProbabilityData

namespace FiniteRealCouplingData

variable {G : Type} [DecidableEq G] [Fintype G]
variable {P Q : FiniteRealProbabilityData G}

/-- Every finite coupling has total joint mass one. -/
theorem sum_joint_eq_one
    (C : FiniteRealCouplingData P Q) :
    ∑ x : G, ∑ y : G, C.joint x y = 1 := by
  calc
    (∑ x : G, ∑ y : G, C.joint x y) =
        ∑ x : G, P.probability x := by
      apply Finset.sum_congr rfl
      intro x _hx
      exact C.left_marginal x
    _ = 1 := P.probability_sum_eq_one

/-- Coupling diagonal mass cannot exceed the pointwise overlap mass of its
prescribed marginals. -/
theorem diagonalMass_le_overlapMass
    (C : FiniteRealCouplingData P Q) :
    C.diagonalMass ≤ P.overlapMass Q := by
  unfold diagonalMass FiniteRealProbabilityData.overlapMass
  apply Finset.sum_le_sum
  intro g _hg
  unfold FiniteRealProbabilityData.overlap
  apply le_min
  · rw [← C.left_marginal g]
    exact Finset.single_le_sum
      (fun h _hh => C.joint_nonneg g h)
      (Finset.mem_univ g)
  · rw [← C.right_marginal g]
    exact Finset.single_le_sum
      (fun h _hh => C.joint_nonneg h g)
      (Finset.mem_univ g)

/-- The common residual mass of the marginals is bounded by disagreement mass
under every prescribed-marginal coupling. -/
theorem residualMass_le_disagreementMass
    (C : FiniteRealCouplingData P Q) :
    P.residualMass Q ≤ C.disagreementMass := by
  unfold FiniteRealProbabilityData.residualMass disagreementMass
  linarith [C.diagonalMass_le_overlapMass]

/-- The unhalved `L¹` distance between the marginals is at most twice the
coupling disagreement mass. -/
theorem l1Distance_le_two_mul_disagreementMass
    (C : FiniteRealCouplingData P Q) :
    P.l1Distance Q ≤ 2 * C.disagreementMass := by
  rw [P.l1Distance_eq_two_mul_residualMass Q]
  exact mul_le_mul_of_nonneg_left
    C.residualMass_le_disagreementMass (by norm_num)

/-- The standard total-variation distance between the marginals is at most
the coupling disagreement mass. -/
theorem totalVariationDistance_le_disagreementMass
    (C : FiniteRealCouplingData P Q) :
    P.totalVariationDistance Q ≤ C.disagreementMass := by
  unfold FiniteRealProbabilityData.totalVariationDistance
  have h := C.l1Distance_le_two_mul_disagreementMass
  nlinarith

end FiniteRealCouplingData

/-- Discrete zero-one disagreement cost on a finite carrier. -/
def finiteDiscreteDisagreementCost
    {G : Type} [DecidableEq G]
    (left right : G) : ℝ :=
  if left = right then 0 else 1

namespace FiniteRealCouplingData

variable {G : Type} [DecidableEq G] [Fintype G]
variable {P Q : FiniteRealProbabilityData G}

/-- Expected discrete disagreement cost is exactly coupling disagreement mass. -/
theorem expectedCost_finiteDiscreteDisagreementCost_eq_disagreementMass
    (C : FiniteRealCouplingData P Q) :
    C.expectedCost finiteDiscreteDisagreementCost = C.disagreementMass := by
  classical
  have hRow (x : G) :
      (∑ y : G,
        C.joint x y * finiteDiscreteDisagreementCost x y) =
        (∑ y : G, C.joint x y) - C.joint x x := by
    calc
      (∑ y : G,
        C.joint x y * finiteDiscreteDisagreementCost x y) =
          ∑ y : G,
            (C.joint x y -
              if y = x then C.joint x x else 0) := by
        apply Finset.sum_congr rfl
        intro y _hy
        by_cases h : y = x
        · subst y
          simp [finiteDiscreteDisagreementCost]
        · have hxy : x ≠ y := Ne.symm h
          simp [finiteDiscreteDisagreementCost, h, hxy]
      _ = (∑ y : G, C.joint x y) -
          ∑ y : G, (if y = x then C.joint x x else 0) := by
        rw [Finset.sum_sub_distrib]
      _ = (∑ y : G, C.joint x y) - C.joint x x := by
        simp
  unfold expectedCost disagreementMass diagonalMass
  rw [← C.sum_joint_eq_one]
  calc
    (∑ x : G, ∑ y : G,
      C.joint x y * finiteDiscreteDisagreementCost x y) =
        ∑ x : G,
          ((∑ y : G, C.joint x y) - C.joint x x) := by
      apply Finset.sum_congr rfl
      intro x _hx
      exact hRow x
    _ = (∑ x : G, ∑ y : G, C.joint x y) -
          ∑ x : G, C.joint x x := by
      rw [Finset.sum_sub_distrib]

/-- Discrete disagreement is pointwise bounded by real Hamming distance on a
finite product carrier. -/
theorem finiteDiscreteDisagreementCost_le_finiteProductHammingDistanceReal
    {ι A : Type} [DecidableEq ι] [DecidableEq A] [Fintype ι]
    (left right : ι → A) :
    finiteDiscreteDisagreementCost left right ≤
      finiteProductHammingDistanceReal left right := by
  by_cases hEq : left = right
  · subst right
    simp [finiteDiscreteDisagreementCost,
      finiteProductHammingDistanceReal,
      finiteProductDisagreementFinset]
  · have hExists : ∃ i : ι, left i ≠ right i := by
      by_contra hNo
      apply hEq
      funext i
      by_contra hNe
      exact hNo ⟨i, hNe⟩
    obtain ⟨i, hi⟩ := hExists
    have hMem : i ∈ finiteProductDisagreementFinset left right := by
      simp [finiteProductDisagreementFinset, hi]
    have hOneLeCard :
        1 ≤ (finiteProductDisagreementFinset left right).card :=
      Finset.one_le_card.mpr ⟨i, hMem⟩
    have hOneLeHamming :
        (1 : ℝ) ≤ finiteProductHammingDistanceReal left right := by
      unfold finiteProductHammingDistanceReal
      exact_mod_cast hOneLeCard
    simpa [finiteDiscreteDisagreementCost, hEq] using hOneLeHamming

/-- Coupling disagreement mass on a finite product carrier is bounded by
expected Hamming distance. -/
theorem disagreementMass_le_expectedFiniteProductHamming
    {ι A : Type} [DecidableEq ι] [DecidableEq A]
    [Fintype ι] [Fintype A]
    {P Q : FiniteRealProbabilityData (ι → A)}
    (C : FiniteRealCouplingData P Q) :
    C.disagreementMass ≤
      C.expectedCost finiteProductHammingDistanceReal := by
  rw [← C.expectedCost_finiteDiscreteDisagreementCost_eq_disagreementMass]
  unfold expectedCost
  apply Finset.sum_le_sum
  intro left _hleft
  apply Finset.sum_le_sum
  intro right _hright
  exact mul_le_mul_of_nonneg_left
    (finiteDiscreteDisagreementCost_le_finiteProductHammingDistanceReal
      left right)
    (C.joint_nonneg left right)

/-- Unhalved `L¹` distance between product-law marginals is at most twice the
expected Hamming cost of any coupling. -/
theorem l1Distance_le_two_mul_expectedFiniteProductHamming
    {ι A : Type} [DecidableEq ι] [DecidableEq A]
    [Fintype ι] [Fintype A]
    {P Q : FiniteRealProbabilityData (ι → A)}
    (C : FiniteRealCouplingData P Q) :
    P.l1Distance Q ≤
      2 * C.expectedCost finiteProductHammingDistanceReal := by
  calc
    P.l1Distance Q ≤ 2 * C.disagreementMass :=
      C.l1Distance_le_two_mul_disagreementMass
    _ ≤ 2 * C.expectedCost finiteProductHammingDistanceReal :=
      mul_le_mul_of_nonneg_left
        C.disagreementMass_le_expectedFiniteProductHamming (by norm_num)

/-- Total-variation distance between product-law marginals is at most expected
Hamming cost of any coupling. -/
theorem totalVariationDistance_le_expectedFiniteProductHamming
    {ι A : Type} [DecidableEq ι] [DecidableEq A]
    [Fintype ι] [Fintype A]
    {P Q : FiniteRealProbabilityData (ι → A)}
    (C : FiniteRealCouplingData P Q) :
    P.totalVariationDistance Q ≤
      C.expectedCost finiteProductHammingDistanceReal := by
  exact C.totalVariationDistance_le_disagreementMass.trans
    C.disagreementMass_le_expectedFiniteProductHamming

end FiniteRealCouplingData

/-- Explicit unhalved `L¹` mixing from an arbitrary finite initial law to the
stationary normalized Gibbs law under strict bidirectional random-scan
contraction. -/
theorem FinitePositiveWeightBidirectionalDobrushinL1MatrixData.randomScanIterate_l1Distance_stationary_le_two_mul_pow_mul_card
    {ι A : Type} [DecidableEq ι] [DecidableEq A]
    [Fintype ι] [Fintype A] [Nonempty A]
    {weight : (ι → A) → ℝ}
    (B : FinitePositiveWeightBidirectionalDobrushinL1MatrixData weight)
    (hweight : ∀ X : ι → A, 0 < weight X)
    (hCard : 0 < Fintype.card ι)
    (initialLaw : FiniteRealProbabilityData (ι → A))
    (n : ℕ) :
    (finiteRealProbabilityKernelIterateData
      (finitePositiveWeightRandomScanProbabilityData weight hweight hCard)
      n initialLaw).l1Distance
        (finitePositiveWeightGlobalProbabilityData weight hweight) ≤
      2 * (finitePositiveWeightBidirectionalRandomScanHammingRate B ^ n *
        (Fintype.card ι : ℝ)) := by
  let stationaryIterate :=
    finiteRealProbabilityKernelIterateData
      (finitePositiveWeightRandomScanProbabilityData weight hweight hCard)
      n (finitePositiveWeightGlobalProbabilityData weight hweight)
  let C := finitePositiveWeightRandomScanToStationaryOverlapCouplingIterateData
    weight hweight hCard initialLaw n
  have hL1 :
      (finiteRealProbabilityKernelIterateData
        (finitePositiveWeightRandomScanProbabilityData weight hweight hCard)
        n initialLaw).l1Distance stationaryIterate ≤
        2 * C.expectedCost finiteProductHammingDistanceReal :=
    C.l1Distance_le_two_mul_expectedFiniteProductHamming
  have hStationaryL1 :
      (finiteRealProbabilityKernelIterateData
        (finitePositiveWeightRandomScanProbabilityData weight hweight hCard)
        n initialLaw).l1Distance
          (finitePositiveWeightGlobalProbabilityData weight hweight) =
      (finiteRealProbabilityKernelIterateData
        (finitePositiveWeightRandomScanProbabilityData weight hweight hCard)
        n initialLaw).l1Distance stationaryIterate := by
    unfold FiniteRealProbabilityData.l1Distance stationaryIterate
    apply Finset.sum_congr rfl
    intro configuration _hconfiguration
    rw [finitePositiveWeightGlobalProbabilityData_randomScan_iterate_probability
      weight hweight hCard n configuration]
  rw [hStationaryL1]
  exact hL1.trans
    (mul_le_mul_of_nonneg_left
      (B.randomScanToStationaryOverlapCouplingIterate_expectedHamming_le_pow_mul_card
        hweight hCard initialLaw n)
      (by norm_num))

/-- Standard total-variation mixing from an arbitrary finite initial law to
the stationary normalized Gibbs law with no configuration-space cardinality
loss. -/
theorem FinitePositiveWeightBidirectionalDobrushinL1MatrixData.randomScanIterate_totalVariationDistance_stationary_le_pow_mul_card
    {ι A : Type} [DecidableEq ι] [DecidableEq A]
    [Fintype ι] [Fintype A] [Nonempty A]
    {weight : (ι → A) → ℝ}
    (B : FinitePositiveWeightBidirectionalDobrushinL1MatrixData weight)
    (hweight : ∀ X : ι → A, 0 < weight X)
    (hCard : 0 < Fintype.card ι)
    (initialLaw : FiniteRealProbabilityData (ι → A))
    (n : ℕ) :
    (finiteRealProbabilityKernelIterateData
      (finitePositiveWeightRandomScanProbabilityData weight hweight hCard)
      n initialLaw).totalVariationDistance
        (finitePositiveWeightGlobalProbabilityData weight hweight) ≤
      finitePositiveWeightBidirectionalRandomScanHammingRate B ^ n *
        (Fintype.card ι : ℝ) := by
  let stationaryIterate :=
    finiteRealProbabilityKernelIterateData
      (finitePositiveWeightRandomScanProbabilityData weight hweight hCard)
      n (finitePositiveWeightGlobalProbabilityData weight hweight)
  let C := finitePositiveWeightRandomScanToStationaryOverlapCouplingIterateData
    weight hweight hCard initialLaw n
  have hTV :
      (finiteRealProbabilityKernelIterateData
        (finitePositiveWeightRandomScanProbabilityData weight hweight hCard)
        n initialLaw).totalVariationDistance stationaryIterate ≤
        C.expectedCost finiteProductHammingDistanceReal :=
    C.totalVariationDistance_le_expectedFiniteProductHamming
  have hStationaryTV :
      (finiteRealProbabilityKernelIterateData
        (finitePositiveWeightRandomScanProbabilityData weight hweight hCard)
        n initialLaw).totalVariationDistance
          (finitePositiveWeightGlobalProbabilityData weight hweight) =
      (finiteRealProbabilityKernelIterateData
        (finitePositiveWeightRandomScanProbabilityData weight hweight hCard)
        n initialLaw).totalVariationDistance stationaryIterate := by
    unfold FiniteRealProbabilityData.totalVariationDistance
      FiniteRealProbabilityData.l1Distance stationaryIterate
    congr 1
    apply Finset.sum_congr rfl
    intro configuration _hconfiguration
    rw [finitePositiveWeightGlobalProbabilityData_randomScan_iterate_probability
      weight hweight hCard n configuration]
  rw [hStationaryTV]
  exact hTV.trans
    (B.randomScanToStationaryOverlapCouplingIterate_expectedHamming_le_pow_mul_card
      hweight hCard initialLaw n)

end
end MathlibAnalytic
end MGAP4D
