import MGAP4D.MathlibAnalytic.FinitePositiveWeightCrossWeightRandomScanComparison
import MGAP4D.MathlibAnalytic.FinitePositiveWeightHilbertRealization
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Total mass of a finite product weight. -/
def finitePositiveWeightTotalMass
    {ι G : Type}
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ) : ℝ :=
  ∑ A : ι → G, weight A

/-- A pointwise-positive finite product weight has strictly positive total
mass. -/
theorem finitePositiveWeightTotalMass_pos
    {ι G : Type}
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A) :
    0 < finitePositiveWeightTotalMass weight := by
  classical
  let g₀ : G := Classical.choice (inferInstance : Nonempty G)
  let A₀ : ι → G := fun _ => g₀
  unfold finitePositiveWeightTotalMass
  exact Finset.sum_pos
    (fun A _hA => hweight A)
    ⟨A₀, Finset.mem_univ A₀⟩

/-- Normalized global probability associated with a positive finite product
weight. -/
def finitePositiveWeightGlobalProbability
    {ι G : Type}
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (A : ι → G) : ℝ :=
  weight A / finitePositiveWeightTotalMass weight

/-- Every normalized global atom is nonnegative. -/
theorem finitePositiveWeightGlobalProbability_nonneg
    {ι G : Type}
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (A : ι → G) :
    0 ≤ finitePositiveWeightGlobalProbability weight A := by
  exact div_nonneg (le_of_lt (hweight A))
    (le_of_lt (finitePositiveWeightTotalMass_pos weight hweight))

/-- The normalized global atoms have total mass one. -/
theorem finitePositiveWeightGlobalProbability_sum_eq_one
    {ι G : Type}
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A) :
    ∑ A : ι → G, finitePositiveWeightGlobalProbability weight A = 1 := by
  classical
  unfold finitePositiveWeightGlobalProbability
  rw [← Finset.sum_div]
  unfold finitePositiveWeightTotalMass
  exact div_self
    (ne_of_gt (finitePositiveWeightTotalMass_pos weight hweight))

/-- Normalized global expectation associated with a positive finite product
weight. -/
def finitePositiveWeightGlobalExpectation
    {ι G : Type}
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (f : (ι → G) → ℝ) : ℝ :=
  ∑ A : ι → G,
    finitePositiveWeightGlobalProbability weight A * f A

/-- The global expectation is the normalized positive-weight pairing against
the constant-one observable. -/
theorem finitePositiveWeightGlobalExpectation_eq_inv_mul_pairing
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (f : (ι → G) → ℝ) :
    finitePositiveWeightGlobalExpectation weight f =
      (finitePositiveWeightTotalMass weight)⁻¹ *
        finitePositiveWeightPairing weight f
          (fun _ : ι → G => (1 : ℝ)) := by
  classical
  unfold finitePositiveWeightGlobalExpectation
    finitePositiveWeightGlobalProbability finitePositiveWeightPairing
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _hA
  ring

/-- Global expectation is additive under subtraction of observables. -/
theorem finitePositiveWeightGlobalExpectation_sub
    {ι G : Type}
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (f g : (ι → G) → ℝ) :
    finitePositiveWeightGlobalExpectation weight (fun A => f A - g A) =
      finitePositiveWeightGlobalExpectation weight f -
        finitePositiveWeightGlobalExpectation weight g := by
  classical
  unfold finitePositiveWeightGlobalExpectation
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro A _hA
  ring

/-- A global expectation of a uniformly bounded observable is bounded by the
same uniform constant. -/
theorem finitePositiveWeightGlobalExpectation_abs_le
    {ι G : Type}
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (f : (ι → G) → ℝ)
    (bound : ℝ)
    (hBound : ∀ A : ι → G, |f A| ≤ bound) :
    |finitePositiveWeightGlobalExpectation weight f| ≤ bound := by
  unfold finitePositiveWeightGlobalExpectation
  exact finiteRealProbability_abs_expectation_le
    (finitePositiveWeightGlobalProbability weight)
    (finitePositiveWeightGlobalProbability_nonneg weight hweight)
    (finitePositiveWeightGlobalProbability_sum_eq_one weight hweight)
    hBound

/-- The normalized positive-weight expectation is stationary for its exact
uniform random-scan heat-bath operator. -/
theorem finitePositiveWeightGlobalExpectation_randomScan
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (hCard : 0 < Fintype.card ι)
    (f : (ι → G) → ℝ) :
    finitePositiveWeightGlobalExpectation weight
        (finitePositiveWeightRandomScanConditionalExpectation weight f) =
      finitePositiveWeightGlobalExpectation weight f := by
  rw [finitePositiveWeightGlobalExpectation_eq_inv_mul_pairing,
    finitePositiveWeightGlobalExpectation_eq_inv_mul_pairing]
  apply congrArg
    (fun x : ℝ => (finitePositiveWeightTotalMass weight)⁻¹ * x)
  calc
    finitePositiveWeightPairing weight
        (finitePositiveWeightRandomScanConditionalExpectation weight f)
        (fun _ : ι → G => (1 : ℝ)) =
      finitePositiveWeightPairing weight f
        (finitePositiveWeightRandomScanConditionalExpectation weight
          (fun _ : ι → G => (1 : ℝ))) :=
      finitePositiveWeightRandomScan_pairing_symm weight f
        (fun _ : ι → G => (1 : ℝ))
    _ = finitePositiveWeightPairing weight f
        (fun _ : ι → G => (1 : ℝ)) := by
      rw [finitePositiveWeightRandomScan_one weight hweight hCard]

/-- One stationary comparison step.  The difference of two global Gibbs
expectations is bounded by the local cross-weight random-scan source pairing
plus the same expectation discrepancy applied to one right-weight random-scan
iterate.  No coupling is assumed. -/
theorem FiniteProductVariationBound.globalExpectation_crossWeight_le_oneStep
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (leftWeight rightWeight : (ι → G) → ℝ)
    (hLeftWeight : ∀ A : ι → G, 0 < leftWeight A)
    (hRightWeight : ∀ A : ι → G, 0 < rightWeight A)
    (hCard : 0 < Fintype.card ι)
    {f : (ι → G) → ℝ)
    (P : FiniteProductVariationBound f)
    (sourceBound : ι → ℝ)
    (hSourceBound : ∀ target : ι, 0 ≤ sourceBound target)
    (hCrossL1 :
      ∀ (A : ι → G) (target : ι),
        finitePositiveWeightSingleSiteConditionalCrossL1
            leftWeight rightWeight A target ≤
          sourceBound target) :
    |finitePositiveWeightGlobalExpectation leftWeight f -
        finitePositiveWeightGlobalExpectation rightWeight f| ≤
      (Fintype.card ι : ℝ)⁻¹ *
          ∑ target : ι,
            sourceBound target * P.variation target +
        |finitePositiveWeightGlobalExpectation leftWeight
              (finitePositiveWeightRandomScanConditionalExpectation
                rightWeight f) -
          finitePositiveWeightGlobalExpectation rightWeight
              (finitePositiveWeightRandomScanConditionalExpectation
                rightWeight f)| := by
  let error : ℝ :=
    (Fintype.card ι : ℝ)⁻¹ *
      ∑ target : ι, sourceBound target * P.variation target
  have hErrorNonneg : 0 ≤ error := by
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun target _htarget =>
        mul_nonneg (hSourceBound target) (P.variation_nonneg target))
  have hPointwise (A : ι → G) :
      |finitePositiveWeightRandomScanConditionalExpectation leftWeight f A -
          finitePositiveWeightRandomScanConditionalExpectation rightWeight f A| ≤
        error := by
    exact P.randomScan_crossWeight_difference_abs_le_sourcePairing
      leftWeight rightWeight hLeftWeight hRightWeight
      sourceBound hCrossL1 A
  have hFirst :
      |finitePositiveWeightGlobalExpectation leftWeight
          (fun A =>
            finitePositiveWeightRandomScanConditionalExpectation leftWeight f A -
              finitePositiveWeightRandomScanConditionalExpectation rightWeight f A)| ≤
        error := by
    exact finitePositiveWeightGlobalExpectation_abs_le
      leftWeight hLeftWeight _ error hPointwise
  have hLeftStationary :=
    finitePositiveWeightGlobalExpectation_randomScan
      leftWeight hLeftWeight hCard f
  have hRightStationary :=
    finitePositiveWeightGlobalExpectation_randomScan
      rightWeight hRightWeight hCard f
  have hDecomposition :
      finitePositiveWeightGlobalExpectation leftWeight f -
          finitePositiveWeightGlobalExpectation rightWeight f =
        finitePositiveWeightGlobalExpectation leftWeight
            (fun A =>
              finitePositiveWeightRandomScanConditionalExpectation leftWeight f A -
                finitePositiveWeightRandomScanConditionalExpectation rightWeight f A) +
          (finitePositiveWeightGlobalExpectation leftWeight
              (finitePositiveWeightRandomScanConditionalExpectation
                rightWeight f) -
            finitePositiveWeightGlobalExpectation rightWeight
              (finitePositiveWeightRandomScanConditionalExpectation
                rightWeight f)) := by
    rw [← hLeftStationary, ← hRightStationary,
      finitePositiveWeightGlobalExpectation_sub]
    ring
  rw [hDecomposition]
  exact le_trans (abs_add_le _ _)
    (add_le_add hFirst (le_refl _))

end

end MathlibAnalytic
end MGAP4D
