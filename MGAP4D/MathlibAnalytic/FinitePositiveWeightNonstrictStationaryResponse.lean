import MGAP4D.MathlibAnalytic.FinitePositiveWeightNonstrictInfluenceMatrix
import MGAP4D.MathlibAnalytic.FinitePositiveWeightStationaryRandomScanComparisonGeometricResidual
import MGAP4D.MathlibAnalytic.FinitePositiveWeightLocalTiltConditional
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- One exact target update of a declared variation profile using a non-strict
influence matrix.  No row or column contraction hypothesis is used. -/
def finitePositiveWeightNonstrictUpdatedVariation
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    {weight : (ι → G) → ℝ}
    (D : FinitePositiveWeightNonstrictL1MatrixData weight)
    (variation : ι → ℝ)
    (target source : ι) : ℝ :=
  if source = target then 0
  else variation source + D.influence target source * variation target

/-- Nonnegative profiles remain nonnegative after one non-strict target
update. -/
theorem finitePositiveWeightNonstrictUpdatedVariation_nonneg
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    {weight : (ι → G) → ℝ}
    (D : FinitePositiveWeightNonstrictL1MatrixData weight)
    (variation : ι → ℝ)
    (hVariation : ∀ e : ι, 0 ≤ variation e)
    (target source : ι) :
    0 ≤ finitePositiveWeightNonstrictUpdatedVariation
      D variation target source := by
  by_cases hEq : source = target
  · simp [finitePositiveWeightNonstrictUpdatedVariation, hEq]
  · simp only [finitePositiveWeightNonstrictUpdatedVariation, hEq, if_false]
    exact add_nonneg (hVariation source)
      (mul_nonneg (D.influence_nonneg target source)
        (hVariation target))

/-- Generic local propagation of a declared observable variation profile using
only non-strict conditional influence data. -/
theorem FiniteProductVariationBound.singleSiteExpectation_difference_abs_le_nonstrict
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    {weight : (ι → G) → ℝ}
    (hweight : ∀ A : ι → G, 0 < weight A)
    {f : (ι → G) → ℝ}
    (P : FiniteProductVariationBound f)
    (D : FinitePositiveWeightNonstrictL1MatrixData weight)
    (target source : ι)
    (A B : ι → G)
    (hAgree : FiniteProductAgreeOff A B source) :
    |finitePositiveWeightSingleSiteExpectation weight f A target -
        finitePositiveWeightSingleSiteExpectation weight f B target| ≤
      finitePositiveWeightNonstrictUpdatedVariation
        D P.variation target source := by
  classical
  by_cases hst : source = target
  · subst source
    rw [finitePositiveWeightSingleSiteExpectation_eq_of_agreeOff
      weight f A B target hAgree]
    simp [finitePositiveWeightNonstrictUpdatedVariation]
  · simp only [finitePositiveWeightNonstrictUpdatedVariation,
      hst, if_false]
    let pA := finitePositiveWeightSingleSiteProbability weight A target
    let pB := finitePositiveWeightSingleSiteProbability weight B target
    let uA : G → ℝ := fun g => f (Function.update A target g)
    let uB : G → ℝ := fun g => f (Function.update B target g)
    have hpA_nonneg : ∀ g : G, 0 ≤ pA g := by
      intro g
      exact le_of_lt
        (finitePositiveWeightSingleSiteProbability_pos
          weight hweight A target g)
    have hpA_sum : ∑ g : G, pA g = 1 := by
      simpa [pA] using
        finitePositiveWeightSingleSiteProbability_sum_eq_one
          weight hweight A target
    have hpB_sum : ∑ g : G, pB g = 1 := by
      simpa [pB] using
        finitePositiveWeightSingleSiteProbability_sum_eq_one
          weight hweight B target
    have hDirect :
        |∑ g : G, pA g * (uA g - uB g)| ≤
          P.variation source := by
      apply finiteRealProbability_abs_expectation_le
        pA hpA_nonneg hpA_sum
      intro g
      exact P.variation_bound source
        (Function.update A target g)
        (Function.update B target g)
        (finiteProductUpdate_agreeOff A B target source g hAgree)
    have hLaw :
        |(∑ g : G, pA g * uB g) -
            ∑ g : G, pB g * uB g| ≤
          D.influence target source * P.variation target := by
      have hOsc : ∀ g h : G, |uB g - uB h| ≤ P.variation target := by
        intro g h
        exact P.variation_bound target
          (Function.update B target g)
          (Function.update B target h)
          (finiteProductUpdates_sameBase_agreeOff B target g h)
      have hL1 := D.conditionalL1_le target source A B hAgree
      calc
        |(∑ g : G, pA g * uB g) -
            ∑ g : G, pB g * uB g| ≤
          finitePositiveWeightSingleSiteConditionalL1 weight A B target *
            P.variation target := by
          simpa [pA, pB, uB,
            finitePositiveWeightSingleSiteConditionalL1] using
            finiteRealProbability_expectation_difference_abs_le_l1_mul
              pA pB uB (P.variation target) hOsc hpA_sum hpB_sum
        _ ≤ D.influence target source * P.variation target :=
          mul_le_mul_of_nonneg_right hL1 (P.variation_nonneg target)
    unfold finitePositiveWeightSingleSiteExpectation
    change
      |(∑ g : G, pA g * uA g) -
          ∑ g : G, pB g * uB g| ≤ _
    have hSplit :
        (∑ g : G, pA g * uA g) -
            ∑ g : G, pB g * uB g =
          (∑ g : G, pA g * (uA g - uB g)) +
            ((∑ g : G, pA g * uB g) -
              ∑ g : G, pB g * uB g) := by
      calc
        (∑ g : G, pA g * uA g) -
            ∑ g : G, pB g * uB g =
          ((∑ g : G, pA g * uA g) -
            ∑ g : G, pA g * uB g) +
            ((∑ g : G, pA g * uB g) -
              ∑ g : G, pB g * uB g) := by ring
        _ = (∑ g : G, pA g * (uA g - uB g)) +
            ((∑ g : G, pA g * uB g) -
              ∑ g : G, pB g * uB g) := by
          congr 1
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro g _hg
          ring
    rw [hSplit]
    exact le_trans (abs_add_le _ _)
      (add_le_add hDirect hLaw)

/-- Uniform average of all non-strict single-target profile updates. -/
def finitePositiveWeightNonstrictRandomScanUpdatedVariation
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    {weight : (ι → G) → ℝ}
    (D : FinitePositiveWeightNonstrictL1MatrixData weight)
    (variation : ι → ℝ)
    (source : ι) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ *
    ∑ target : ι,
      finitePositiveWeightNonstrictUpdatedVariation
        D variation target source

/-- Non-strict random-scan profile updating preserves nonnegativity. -/
theorem finitePositiveWeightNonstrictRandomScanUpdatedVariation_nonneg
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    {weight : (ι → G) → ℝ}
    (D : FinitePositiveWeightNonstrictL1MatrixData weight)
    (variation : ι → ℝ)
    (hVariation : ∀ e : ι, 0 ≤ variation e)
    (source : ι) :
    0 ≤ finitePositiveWeightNonstrictRandomScanUpdatedVariation
      D variation source := by
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun target _hTarget =>
      finitePositiveWeightNonstrictUpdatedVariation_nonneg
        D variation hVariation target source)

/-- A declared variation bound propagates through one exact random-scan step
under a non-strict influence matrix. -/
noncomputable def
    FiniteProductVariationBound.randomScanNonstrictVariationBound
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    {weight : (ι → G) → ℝ}
    (hweight : ∀ A : ι → G, 0 < weight A)
    {f : (ι → G) → ℝ}
    (P : FiniteProductVariationBound f)
    (D : FinitePositiveWeightNonstrictL1MatrixData weight) :
    FiniteProductVariationBound
      (finitePositiveWeightRandomScanConditionalExpectation weight f) := by
  refine
    { variation :=
        finitePositiveWeightNonstrictRandomScanUpdatedVariation D P.variation
      variation_nonneg :=
        finitePositiveWeightNonstrictRandomScanUpdatedVariation_nonneg
          D P.variation P.variation_nonneg
      variation_bound := ?_ }
  intro source A B hAgree
  have hInvNonneg : 0 ≤ (Fintype.card ι : ℝ)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg _)
  have hTarget (target : ι) :
      |finitePositiveWeightSingleSiteExpectation weight f A target -
          finitePositiveWeightSingleSiteExpectation weight f B target| ≤
        finitePositiveWeightNonstrictUpdatedVariation
          D P.variation target source :=
    P.singleSiteExpectation_difference_abs_le_nonstrict
      hweight D target source A B hAgree
  have hSum :
      |∑ target : ι,
        (finitePositiveWeightSingleSiteExpectation weight f A target -
          finitePositiveWeightSingleSiteExpectation weight f B target)| ≤
        ∑ target : ι,
          finitePositiveWeightNonstrictUpdatedVariation
            D P.variation target source := by
    calc
      |∑ target : ι,
        (finitePositiveWeightSingleSiteExpectation weight f A target -
          finitePositiveWeightSingleSiteExpectation weight f B target)| ≤
        ∑ target : ι,
          |finitePositiveWeightSingleSiteExpectation weight f A target -
            finitePositiveWeightSingleSiteExpectation weight f B target| := by
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ target : ι,
          finitePositiveWeightNonstrictUpdatedVariation
            D P.variation target source := by
        apply Finset.sum_le_sum
        intro target _hTarget
        exact hTarget target
  unfold finitePositiveWeightRandomScanConditionalExpectation
  unfold finitePositiveWeightNonstrictRandomScanUpdatedVariation
  calc
    |(Fintype.card ι : ℝ)⁻¹ *
          (∑ target : ι,
            finitePositiveWeightSingleSiteExpectation weight f A target) -
        (Fintype.card ι : ℝ)⁻¹ *
          (∑ target : ι,
            finitePositiveWeightSingleSiteExpectation weight f B target)| =
      (Fintype.card ι : ℝ)⁻¹ *
        |∑ target : ι,
          (finitePositiveWeightSingleSiteExpectation weight f A target -
            finitePositiveWeightSingleSiteExpectation weight f B target)| := by
      rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
        abs_of_nonneg hInvNonneg]
    _ ≤ (Fintype.card ι : ℝ)⁻¹ *
        ∑ target : ι,
          finitePositiveWeightNonstrictUpdatedVariation
            D P.variation target source :=
      mul_le_mul_of_nonneg_left hSum hInvNonneg

/-- Stationary cross-weight comparison data whose right-hand specification is
controlled only by a non-strict influence matrix. -/
structure FinitePositiveWeightStationaryNonstrictComparisonData
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
  sourceBound_nonneg : ∀ target : ι, 0 ≤ sourceBound target
  conditionalCrossL1_le_sourceBound :
    ∀ (A : ι → G) (target : ι),
      finitePositiveWeightSingleSiteConditionalCrossL1
          leftWeight rightWeight A target ≤
        sourceBound target
  rightInfluence :
    FinitePositiveWeightNonstrictL1MatrixData rightWeight

namespace FinitePositiveWeightStationaryNonstrictComparisonData

variable
  {ι G : Type}
  [DecidableEq ι]
  [Fintype ι]
  [Fintype G]
  [Nonempty G]
  {leftWeight rightWeight : (ι → G) → ℝ}

/-- Right-weight exact random-scan observable iterate. -/
def rightRandomScanObservableIterate
    (C : FinitePositiveWeightStationaryNonstrictComparisonData
      leftWeight rightWeight)
    (f : (ι → G) → ℝ) : ℕ → ((ι → G) → ℝ)
  | 0 => f
  | n + 1 =>
      finitePositiveWeightRandomScanConditionalExpectation rightWeight
        (C.rightRandomScanObservableIterate f n)

@[simp] theorem rightRandomScanObservableIterate_zero
    (C : FinitePositiveWeightStationaryNonstrictComparisonData
      leftWeight rightWeight)
    (f : (ι → G) → ℝ) :
    C.rightRandomScanObservableIterate f 0 = f := rfl

@[simp] theorem rightRandomScanObservableIterate_succ
    (C : FinitePositiveWeightStationaryNonstrictComparisonData
      leftWeight rightWeight)
    (f : (ι → G) → ℝ)
    (n : ℕ) :
    C.rightRandomScanObservableIterate f (n + 1) =
      finitePositiveWeightRandomScanConditionalExpectation rightWeight
        (C.rightRandomScanObservableIterate f n) := rfl

/-- Proof-relevant variation profiles along the non-strict right random-scan
orbit. -/
noncomputable def rightRandomScanIterateVariationBound
    {f : (ι → G) → ℝ}
    (P : FiniteProductVariationBound f)
    (C : FinitePositiveWeightStationaryNonstrictComparisonData
      leftWeight rightWeight) :
    (n : ℕ) →
      FiniteProductVariationBound (C.rightRandomScanObservableIterate f n)
  | 0 => P
  | n + 1 =>
      (rightRandomScanIterateVariationBound P C n).randomScanNonstrictVariationBound
        C.rightWeight_pos C.rightInfluence

@[simp] theorem rightRandomScanIterateVariationBound_zero
    {f : (ι → G) → ℝ}
    (P : FiniteProductVariationBound f)
    (C : FinitePositiveWeightStationaryNonstrictComparisonData
      leftWeight rightWeight) :
    rightRandomScanIterateVariationBound P C 0 = P := rfl

@[simp] theorem rightRandomScanIterateVariationBound_succ
    {f : (ι → G) → ℝ}
    (P : FiniteProductVariationBound f)
    (C : FinitePositiveWeightStationaryNonstrictComparisonData
      leftWeight rightWeight)
    (n : ℕ) :
    rightRandomScanIterateVariationBound P C (n + 1) =
      (rightRandomScanIterateVariationBound P C n).randomScanNonstrictVariationBound
        C.rightWeight_pos C.rightInfluence := rfl

/-- Absolute normalized expectation discrepancy. -/
def expectationDiscrepancy
    (C : FinitePositiveWeightStationaryNonstrictComparisonData
      leftWeight rightWeight)
    (f : (ι → G) → ℝ) : ℝ :=
  |finitePositiveWeightGlobalExpectation leftWeight f -
    finitePositiveWeightGlobalExpectation rightWeight f|

/-- Local cross-weight source functional. -/
def sourceError
    (C : FinitePositiveWeightStationaryNonstrictComparisonData
      leftWeight rightWeight)
    (variation : ι → ℝ) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ *
    ∑ target : ι, C.sourceBound target * variation target

/-- Accumulated exact source contribution through `n` non-strict right-weight
random-scan variation profiles. -/
noncomputable def partialStationarySource
    {f : (ι → G) → ℝ}
    (P : FiniteProductVariationBound f)
    (C : FinitePositiveWeightStationaryNonstrictComparisonData
      leftWeight rightWeight) : ℕ → ℝ
  | 0 => 0
  | n + 1 =>
      partialStationarySource P C n +
        C.sourceError
          (rightRandomScanIterateVariationBound P C n).variation

@[simp] theorem partialStationarySource_zero
    {f : (ι → G) → ℝ}
    (P : FiniteProductVariationBound f)
    (C : FinitePositiveWeightStationaryNonstrictComparisonData
      leftWeight rightWeight) :
    partialStationarySource P C 0 = 0 := rfl

@[simp] theorem partialStationarySource_succ
    {f : (ι → G) → ℝ}
    (P : FiniteProductVariationBound f)
    (C : FinitePositiveWeightStationaryNonstrictComparisonData
      leftWeight rightWeight)
    (n : ℕ) :
    partialStationarySource P C (n + 1) =
      partialStationarySource P C n +
        C.sourceError
          (rightRandomScanIterateVariationBound P C n).variation := rfl

/-- One exact stationary comparison step with no contraction assumption. -/
theorem expectationDiscrepancy_iterate_le_oneStep
    {f : (ι → G) → ℝ}
    (P : FiniteProductVariationBound f)
    (C : FinitePositiveWeightStationaryNonstrictComparisonData
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

/-- Exact finite stationary comparison iteration under non-strict influence
data. -/
theorem expectationDiscrepancy_le_partialSource_add_iterateResidual
    {f : (ι → G) → ℝ}
    (P : FiniteProductVariationBound f)
    (C : FinitePositiveWeightStationaryNonstrictComparisonData
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
          add_le_add (le_refl _) hStep
        _ = partialStationarySource P C (n + 1) +
            C.expectationDiscrepancy
              (C.rightRandomScanObservableIterate f (n + 1)) := by
          rw [partialStationarySource_succ]
          ring

/-- Two normalized positive expectations differ by at most twice a declared
total variation radius. -/
theorem expectationDiscrepancy_le_two_mul_totalVariation
    {f : (ι → G) → ℝ}
    (P : FiniteProductVariationBound f)
    (C : FinitePositiveWeightStationaryNonstrictComparisonData
      leftWeight rightWeight) :
    C.expectationDiscrepancy f ≤
      2 * finiteProductVariationTotal P.variation := by
  let g₀ : G := Classical.choice (inferInstance : Nonempty G)
  let A₀ : ι → G := fun _ => g₀
  let centered : (ι → G) → ℝ := fun A => f A - f A₀
  have hCentered (A : ι → G) :
      |centered A| ≤ finiteProductVariationTotal P.variation := by
    simpa [centered] using P.difference_abs_le_totalVariation A A₀
  have hLeft :
      |finitePositiveWeightGlobalExpectation leftWeight centered| ≤
        finiteProductVariationTotal P.variation :=
    finitePositiveWeightGlobalExpectation_abs_le
      leftWeight C.leftWeight_pos centered
      (finiteProductVariationTotal P.variation) hCentered
  have hRight :
      |finitePositiveWeightGlobalExpectation rightWeight centered| ≤
        finiteProductVariationTotal P.variation :=
    finitePositiveWeightGlobalExpectation_abs_le
      rightWeight C.rightWeight_pos centered
      (finiteProductVariationTotal P.variation) hCentered
  have hLeftCenter :
      finitePositiveWeightGlobalExpectation leftWeight centered =
        finitePositiveWeightGlobalExpectation leftWeight f - f A₀ := by
    calc
      finitePositiveWeightGlobalExpectation leftWeight centered =
          finitePositiveWeightGlobalExpectation leftWeight
            (fun A => f A - (fun _ : ι → G => f A₀) A) := rfl
      _ = finitePositiveWeightGlobalExpectation leftWeight f -
          finitePositiveWeightGlobalExpectation leftWeight
            (fun _ : ι → G => f A₀) :=
        finitePositiveWeightGlobalExpectation_sub leftWeight f
          (fun _ : ι → G => f A₀)
      _ = finitePositiveWeightGlobalExpectation leftWeight f - f A₀ := by
        rw [finitePositiveWeightGlobalExpectation_const
          leftWeight C.leftWeight_pos]
  have hRightCenter :
      finitePositiveWeightGlobalExpectation rightWeight centered =
        finitePositiveWeightGlobalExpectation rightWeight f - f A₀ := by
    calc
      finitePositiveWeightGlobalExpectation rightWeight centered =
          finitePositiveWeightGlobalExpectation rightWeight
            (fun A => f A - (fun _ : ι → G => f A₀) A) := rfl
      _ = finitePositiveWeightGlobalExpectation rightWeight f -
          finitePositiveWeightGlobalExpectation rightWeight
            (fun _ : ι → G => f A₀) :=
        finitePositiveWeightGlobalExpectation_sub rightWeight f
          (fun _ : ι → G => f A₀)
      _ = finitePositiveWeightGlobalExpectation rightWeight f - f A₀ := by
        rw [finitePositiveWeightGlobalExpectation_const
          rightWeight C.rightWeight_pos]
  have hTranslate :
      finitePositiveWeightGlobalExpectation leftWeight f -
          finitePositiveWeightGlobalExpectation rightWeight f =
        finitePositiveWeightGlobalExpectation leftWeight centered -
          finitePositiveWeightGlobalExpectation rightWeight centered := by
    rw [hLeftCenter, hRightCenter]
    ring
  unfold expectationDiscrepancy
  rw [hTranslate]
  calc
    |finitePositiveWeightGlobalExpectation leftWeight centered -
        finitePositiveWeightGlobalExpectation rightWeight centered| ≤
      |finitePositiveWeightGlobalExpectation leftWeight centered| +
        |finitePositiveWeightGlobalExpectation rightWeight centered| := by
      simpa [sub_eq_add_neg] using
        abs_add_le
          (finitePositiveWeightGlobalExpectation leftWeight centered)
          (-finitePositiveWeightGlobalExpectation rightWeight centered)
    _ ≤ finiteProductVariationTotal P.variation +
        finiteProductVariationTotal P.variation :=
      add_le_add hLeft hRight
    _ = 2 * finiteProductVariationTotal P.variation := by ring

/-- Complete finite-step response estimate: accumulated local source plus the
exact non-strict propagated terminal variation. -/
theorem expectationDiscrepancy_le_partialSource_add_two_mul_terminalVariation
    {f : (ι → G) → ℝ}
    (P : FiniteProductVariationBound f)
    (C : FinitePositiveWeightStationaryNonstrictComparisonData
      leftWeight rightWeight)
    (n : ℕ) :
    C.expectationDiscrepancy f ≤
      partialStationarySource P C n +
        2 * finiteProductVariationTotal
          (rightRandomScanIterateVariationBound P C n).variation := by
  have hFinite :=
    expectationDiscrepancy_le_partialSource_add_iterateResidual P C n
  have hResidual :=
    expectationDiscrepancy_le_two_mul_totalVariation
      (rightRandomScanIterateVariationBound P C n) C
  exact hFinite.trans
    (add_le_add (le_refl _) hResidual)

end FinitePositiveWeightStationaryNonstrictComparisonData

/-- A bounded positive finite-support multiplicative tilt canonically gives
non-strict stationary comparison data. -/
def finitePositiveWeightLocalTiltStationaryNonstrictComparisonData
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight tilt : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (htilt : ∀ A : ι → G, 0 < tilt A)
    (support : Finset ι)
    (htiltSupport : FiniteProductFunctionSupportedOn support tilt)
    (lower upper : ℝ)
    (hLower : 0 < lower)
    (hUpper : 0 < upper)
    (hLowerUpper : lower ≤ upper)
    (htiltLower : ∀ A : ι → G, lower ≤ tilt A)
    (htiltUpper : ∀ A : ι → G, tilt A ≤ upper)
    (hCard : 0 < Fintype.card ι)
    (D : FinitePositiveWeightNonstrictL1MatrixData weight) :
    FinitePositiveWeightStationaryNonstrictComparisonData
      (finitePositiveWeightMultiplicativeTilt weight tilt) weight :=
  { leftWeight_pos :=
      finitePositiveWeightMultiplicativeTilt_pos weight tilt hweight htilt
    rightWeight_pos := hweight
    coordinateCard_pos := hCard
    sourceBound :=
      finitePositiveWeightLocalTiltConditionalSourceBound
        support lower upper
    sourceBound_nonneg := by
      intro target
      unfold finitePositiveWeightLocalTiltConditionalSourceBound
      split
      · have hRatioOne : 1 ≤ upper / lower :=
          (le_div_iff₀ hLower).2 hLowerUpper
        have hRatioPos : 0 < upper / lower := div_pos hUpper hLower
        have hInvLeOne : (upper / lower)⁻¹ ≤ 1 :=
          (inv_le_one₀ hRatioPos).2 hRatioOne
        nlinarith
      · exact le_rfl
    conditionalCrossL1_le_sourceBound := by
      intro A target
      exact
        finitePositiveWeightMultiplicativeTilt_singleSiteConditionalCrossL1_le_sourceBound
          weight tilt hweight htilt support htiltSupport
          lower upper hLower hUpper hLowerUpper
          htiltLower htiltUpper A target
    rightInfluence := D }

end

end MathlibAnalytic
end MGAP4D
