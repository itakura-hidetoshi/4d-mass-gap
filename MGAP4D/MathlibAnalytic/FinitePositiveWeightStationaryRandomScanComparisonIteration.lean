import MGAP4D.MathlibAnalytic.FinitePositiveWeightStationaryRandomScanComparison
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Proof-relevant data for iterating the stationary cross-weight comparison
with the right-weight exact random-scan Gibbs operator. -/
structure FinitePositiveWeightStationaryRandomScanComparisonData
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (leftWeight rightWeight : (ι → G) → ℝ) where
  leftWeight_pos : ∀ A : ι → G, 0 < leftWeight A
  rightWeight_pos : ∀ A : ι → G, 0 < rightWeight A
  coordinateCard_pos : 0 < Fintype.card ι
  sourceBound : ι → ℝ
  conditionalCrossL1_le_sourceBound :
    ∀ (A : ι → G) (target : ι),
      finitePositiveWeightSingleSiteConditionalCrossL1
          leftWeight rightWeight A target ≤
        sourceBound target
  rightDobrushin :
    FinitePositiveWeightDobrushinL1MatrixData rightWeight

namespace FinitePositiveWeightStationaryRandomScanComparisonData

variable
  {ι G : Type}
  [DecidableEq ι]
  [Fintype ι]
  [Fintype G]
  [Nonempty G]
  {leftWeight rightWeight : (ι → G) → ℝ}

/-- The observable obtained after `n` applications of the right-weight exact
random-scan Gibbs operator. -/
def rightRandomScanObservableIterate
    (C : FinitePositiveWeightStationaryRandomScanComparisonData
      leftWeight rightWeight)
    (f : (ι → G) → ℝ) : ℕ → ((ι → G) → ℝ)
  | 0 => f
  | n + 1 =>
      finitePositiveWeightRandomScanConditionalExpectation rightWeight
        (C.rightRandomScanObservableIterate f n)

@[simp] theorem rightRandomScanObservableIterate_zero
    (C : FinitePositiveWeightStationaryRandomScanComparisonData
      leftWeight rightWeight)
    (f : (ι → G) → ℝ) :
    C.rightRandomScanObservableIterate f 0 = f :=
  rfl

@[simp] theorem rightRandomScanObservableIterate_succ
    (C : FinitePositiveWeightStationaryRandomScanComparisonData
      leftWeight rightWeight)
    (f : (ι → G) → ℝ)
    (n : ℕ) :
    C.rightRandomScanObservableIterate f (n + 1) =
      finitePositiveWeightRandomScanConditionalExpectation rightWeight
        (C.rightRandomScanObservableIterate f n) :=
  rfl

/-- Absolute discrepancy of the two normalized global expectations. -/
def expectationDiscrepancy
    (C : FinitePositiveWeightStationaryRandomScanComparisonData
      leftWeight rightWeight)
    (f : (ι → G) → ℝ) : ℝ :=
  |finitePositiveWeightGlobalExpectation leftWeight f -
    finitePositiveWeightGlobalExpectation rightWeight f|

/-- Local cross-weight source functional evaluated on one declared variation
profile. -/
def sourceError
    (C : FinitePositiveWeightStationaryRandomScanComparisonData
      leftWeight rightWeight)
    (variation : ι → ℝ) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ *
    ∑ target : ι, C.sourceBound target * variation target

/-- Iterated proof-relevant variation bound along the right-weight random-scan
orbit of an observable. -/
noncomputable def rightRandomScanIterateVariationBound
    {f : (ι → G) → ℝ}
    (P : FiniteProductVariationBound f)
    (C : FinitePositiveWeightStationaryRandomScanComparisonData
      leftWeight rightWeight) :
    (n : ℕ) →
      FiniteProductVariationBound (C.rightRandomScanObservableIterate f n)
  | 0 => P
  | n + 1 =>
      (rightRandomScanIterateVariationBound P C n).randomScanVariationBound
        C.rightWeight_pos C.rightDobrushin

@[simp] theorem rightRandomScanIterateVariationBound_zero
    {f : (ι → G) → ℝ}
    (P : FiniteProductVariationBound f)
    (C : FinitePositiveWeightStationaryRandomScanComparisonData
      leftWeight rightWeight) :
    rightRandomScanIterateVariationBound P C 0 = P :=
  rfl

@[simp] theorem rightRandomScanIterateVariationBound_succ
    {f : (ι → G) → ℝ}
    (P : FiniteProductVariationBound f)
    (C : FinitePositiveWeightStationaryRandomScanComparisonData
      leftWeight rightWeight)
    (n : ℕ) :
    rightRandomScanIterateVariationBound P C (n + 1) =
      (rightRandomScanIterateVariationBound P C n).randomScanVariationBound
        C.rightWeight_pos C.rightDobrushin :=
  rfl

/-- Total declared variation of the iterated observable contracts at the
standard right-weight Dobrushin random-scan rate. -/
theorem rightRandomScanIterate_totalVariation_le_rate_pow
    {f : (ι → G) → ℝ}
    (P : FiniteProductVariationBound f)
    (C : FinitePositiveWeightStationaryRandomScanComparisonData
      leftWeight rightWeight)
    (n : ℕ) :
    finiteProductVariationTotal
        (rightRandomScanIterateVariationBound P C n).variation ≤
      finitePositiveWeightDobrushinRandomScanRate C.rightDobrushin ^ n *
        finiteProductVariationTotal P.variation := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hStep :=
        (rightRandomScanIterateVariationBound P C n).randomScan_totalVariation_le_rate_mul
          C.rightWeight_pos C.rightDobrushin C.coordinateCard_pos
      have hRateNonneg :
          0 ≤ finitePositiveWeightDobrushinRandomScanRate C.rightDobrushin :=
        finitePositiveWeightDobrushinRandomScanRate_nonneg
          C.rightDobrushin C.coordinateCard_pos
      calc
        finiteProductVariationTotal
            (rightRandomScanIterateVariationBound P C (n + 1)).variation ≤
          finitePositiveWeightDobrushinRandomScanRate C.rightDobrushin *
            finiteProductVariationTotal
              (rightRandomScanIterateVariationBound P C n).variation := by
                simpa using hStep
        _ ≤ finitePositiveWeightDobrushinRandomScanRate C.rightDobrushin *
            (finitePositiveWeightDobrushinRandomScanRate C.rightDobrushin ^ n *
              finiteProductVariationTotal P.variation) :=
          mul_le_mul_of_nonneg_left ih hRateNonneg
        _ = finitePositiveWeightDobrushinRandomScanRate C.rightDobrushin ^ (n + 1) *
            finiteProductVariationTotal P.variation := by
          rw [pow_succ]
          ring

/-- Accumulated exact source contribution through the first `n` right-weight
random-scan variation profiles. -/
noncomputable def partialStationarySource
    {f : (ι → G) → ℝ}
    (P : FiniteProductVariationBound f)
    (C : FinitePositiveWeightStationaryRandomScanComparisonData
      leftWeight rightWeight) : ℕ → ℝ
  | 0 => 0
  | n + 1 =>
      partialStationarySource P C n +
        C.sourceError
          (rightRandomScanIterateVariationBound P C n).variation

@[simp] theorem partialStationarySource_zero
    {f : (ι → G) → ℝ}
    (P : FiniteProductVariationBound f)
    (C : FinitePositiveWeightStationaryRandomScanComparisonData
      leftWeight rightWeight) :
    partialStationarySource P C 0 = 0 :=
  rfl

@[simp] theorem partialStationarySource_succ
    {f : (ι → G) → ℝ}
    (P : FiniteProductVariationBound f)
    (C : FinitePositiveWeightStationaryRandomScanComparisonData
      leftWeight rightWeight)
    (n : ℕ) :
    partialStationarySource P C (n + 1) =
      partialStationarySource P C n +
        C.sourceError
          (rightRandomScanIterateVariationBound P C n).variation :=
  rfl

/-- One comparison step at the `n`th right-weight random-scan iterate. -/
theorem expectationDiscrepancy_iterate_le_oneStep
    {f : (ι → G) → ℝ}
    (P : FiniteProductVariationBound f)
    (C : FinitePositiveWeightStationaryRandomScanComparisonData
      leftWeight rightWeight)
    (n : ℕ) :
    C.expectationDiscrepancy (C.rightRandomScanObservableIterate f n) ≤
      C.sourceError
          (rightRandomScanIterateVariationBound P C n).variation +
        C.expectationDiscrepancy
          (C.rightRandomScanObservableIterate f (n + 1)) := by
  unfold expectationDiscrepancy sourceError
  simpa using
    (rightRandomScanIterateVariationBound P C n).globalExpectation_crossWeight_le_oneStep
      leftWeight rightWeight C.leftWeight_pos C.rightWeight_pos
      C.coordinateCard_pos C.sourceBound
      C.conditionalCrossL1_le_sourceBound

/-- Exact finite stationary comparison iteration.  The local source pairing is
retained at every stage, and the only remainder is the expectation discrepancy
of the `n`th right-weight random-scan iterate. -/
theorem expectationDiscrepancy_le_partialSource_add_iterateResidual
    {f : (ι → G) → ℝ}
    (P : FiniteProductVariationBound f)
    (C : FinitePositiveWeightStationaryRandomScanComparisonData
      leftWeight rightWeight)
    (n : ℕ) :
    C.expectationDiscrepancy f ≤
      partialStationarySource P C n +
        C.expectationDiscrepancy
          (C.rightRandomScanObservableIterate f n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hStep := expectationDiscrepancy_iterate_le_oneStep P C n
      calc
        C.expectationDiscrepancy f ≤
            partialStationarySource P C n +
              C.expectationDiscrepancy
                (C.rightRandomScanObservableIterate f n) := ih
        _ ≤ partialStationarySource P C n +
            (C.sourceError
                (rightRandomScanIterateVariationBound P C n).variation +
              C.expectationDiscrepancy
                (C.rightRandomScanObservableIterate f (n + 1))) :=
          add_le_add (le_refl (partialStationarySource P C n)) hStep
        _ = partialStationarySource P C (n + 1) +
            C.expectationDiscrepancy
              (C.rightRandomScanObservableIterate f (n + 1)) := by
          rw [partialStationarySource_succ]
          ring

end FinitePositiveWeightStationaryRandomScanComparisonData

end

end MathlibAnalytic
end MGAP4D
