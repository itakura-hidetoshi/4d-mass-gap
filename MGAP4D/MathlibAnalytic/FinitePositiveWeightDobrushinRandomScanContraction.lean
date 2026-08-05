import MGAP4D.MathlibAnalytic.FinitePositiveWeightDobrushinInfluence
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A proof-relevant coordinatewise oscillation bound for an observable on a
finite product space. -/
structure FiniteProductVariationBound
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (f : (ι → G) → ℝ) where
  variation : ι → ℝ
  variation_nonneg : ∀ e : ι, 0 ≤ variation e
  variation_bound :
    ∀ (source : ι) (A B : ι → G),
      FiniteProductAgreeOff A B source →
        |f A - f B| ≤ variation source

/-- The canonical coordinate oscillations provide a variation bound. -/
noncomputable def finiteProductCanonicalVariationBound
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (f : (ι → G) → ℝ) :
    FiniteProductVariationBound f :=
  { variation := finiteProductCanonicalVariation f
    variation_nonneg := finiteProductCanonicalVariation_nonneg f
    variation_bound := fun source A B hAgree =>
      finiteProduct_difference_abs_le_canonicalVariation
        f source A B hAgree }

/-- Two updates of the same base configuration agree away from their updated
coordinate. -/
theorem finiteProductUpdates_sameBase_agreeOff
    {ι G : Type}
    [DecidableEq ι]
    (A : ι → G)
    (e : ι)
    (g h : G) :
    FiniteProductAgreeOff
      (Function.update A e g)
      (Function.update A e h)
      e := by
  intro i hie
  simp [Function.update, hie]

/-- Generic local Dobrushin propagation for an arbitrary declared variation
profile. -/
theorem FiniteProductVariationBound.singleSiteExpectation_difference_abs_le
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    {weight : (ι → G) → ℝ}
    (hweight : ∀ A : ι → G, 0 < weight A)
    {f : (ι → G) → ℝ}
    (P : FiniteProductVariationBound f)
    (D : FinitePositiveWeightDobrushinL1MatrixData weight)
    (target source : ι)
    (A B : ι → G)
    (hAgree : FiniteProductAgreeOff A B source) :
    |finitePositiveWeightSingleSiteExpectation weight f A target -
        finitePositiveWeightSingleSiteExpectation weight f B target| ≤
      if source = target then 0
      else P.variation source +
        D.influence target source * P.variation target := by
  classical
  by_cases hst : source = target
  · subst source
    rw [finitePositiveWeightSingleSiteExpectation_eq_of_agreeOff
      weight f A B target hAgree]
    simp
  · simp only [hst, if_false]
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
    exact le_trans (abs_add_le _ _) (add_le_add hDirect hLaw)

/-- Sharp single-target Dobrushin update of a declared variation profile. -/
def finitePositiveWeightDobrushinUpdatedVariation
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    {weight : (ι → G) → ℝ}
    (D : FinitePositiveWeightDobrushinL1MatrixData weight)
    (variation : ι → ℝ)
    (target source : ι) : ℝ :=
  if source = target then 0
  else variation source + D.influence target source * variation target

/-- A nonnegative profile remains nonnegative after one target update. -/
theorem finitePositiveWeightDobrushinUpdatedVariation_nonneg
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    {weight : (ι → G) → ℝ}
    (D : FinitePositiveWeightDobrushinL1MatrixData weight)
    (variation : ι → ℝ)
    (hVariation : ∀ e : ι, 0 ≤ variation e)
    (target source : ι) :
    0 ≤ finitePositiveWeightDobrushinUpdatedVariation
      D variation target source := by
  by_cases hst : source = target
  · simp [finitePositiveWeightDobrushinUpdatedVariation, hst]
  · simp only [finitePositiveWeightDobrushinUpdatedVariation, hst, if_false]
    exact add_nonneg (hVariation source)
      (mul_nonneg (D.influence_nonneg target source) (hVariation target))

/-- Total mass of a finite coordinate variation profile. -/
def finiteProductVariationTotal
    {ι : Type}
    [Fintype ι]
    (variation : ι → ℝ) : ℝ :=
  ∑ e : ι, variation e

/-- Exact single-target total-variation identity. -/
theorem finitePositiveWeightDobrushinUpdatedVariation_sum_eq
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    {weight : (ι → G) → ℝ}
    (D : FinitePositiveWeightDobrushinL1MatrixData weight)
    (variation : ι → ℝ)
    (target : ι) :
    (∑ source : ι,
      finitePositiveWeightDobrushinUpdatedVariation
        D variation target source) =
      (∑ source : ι, variation source) +
        (∑ source : ι, D.influence target source) * variation target -
          variation target := by
  classical
  have hPointwise (source : ι) :
      finitePositiveWeightDobrushinUpdatedVariation
          D variation target source =
        variation source + D.influence target source * variation target -
          (if source = target then variation target else 0) := by
    by_cases hst : source = target
    · subst source
      simp [finitePositiveWeightDobrushinUpdatedVariation,
        D.influence_diagonal_zero]
    · simp [finitePositiveWeightDobrushinUpdatedVariation, hst]
  calc
    (∑ source : ι,
      finitePositiveWeightDobrushinUpdatedVariation
        D variation target source) =
      ∑ source : ι,
        (variation source + D.influence target source * variation target -
          (if source = target then variation target else 0)) := by
      apply Finset.sum_congr rfl
      intro source _hsource
      exact hPointwise source
    _ = (∑ source : ι, variation source) +
        (∑ source : ι, D.influence target source) * variation target -
          variation target := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_mul]
      simp

/-- Strict Dobrushin heat-bath margin. -/
def finitePositiveWeightDobrushinHeatBathGap
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    {weight : (ι → G) → ℝ}
    (D : FinitePositiveWeightDobrushinL1MatrixData weight) : ℝ :=
  1 - D.coefficient

/-- The generic Dobrushin heat-bath margin is positive. -/
theorem finitePositiveWeightDobrushinHeatBathGap_pos
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    {weight : (ι → G) → ℝ}
    (D : FinitePositiveWeightDobrushinL1MatrixData weight) :
    0 < finitePositiveWeightDobrushinHeatBathGap D := by
  exact sub_pos.mpr D.coefficient_lt_one

/-- One exact target update decreases total variation by at least the
Dobrushin margin times the target variation. -/
theorem finitePositiveWeightDobrushinUpdatedVariation_total_le
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    {weight : (ι → G) → ℝ}
    (D : FinitePositiveWeightDobrushinL1MatrixData weight)
    (variation : ι → ℝ)
    (hVariation : ∀ e : ι, 0 ≤ variation e)
    (target : ι) :
    finiteProductVariationTotal
        (finitePositiveWeightDobrushinUpdatedVariation D variation target) ≤
      finiteProductVariationTotal variation -
        finitePositiveWeightDobrushinHeatBathGap D * variation target := by
  have hRowMul :
      (∑ source : ι, D.influence target source) * variation target ≤
        D.coefficient * variation target :=
    mul_le_mul_of_nonneg_right
      (D.rowSum_le_coefficient target) (hVariation target)
  unfold finiteProductVariationTotal
  rw [finitePositiveWeightDobrushinUpdatedVariation_sum_eq]
  calc
    (∑ source : ι, variation source) +
          (∑ source : ι, D.influence target source) * variation target -
            variation target ≤
      (∑ source : ι, variation source) +
          D.coefficient * variation target - variation target :=
      sub_le_sub_right (add_le_add (le_refl _) hRowMul) _
    _ = (∑ source : ι, variation source) -
        finitePositiveWeightDobrushinHeatBathGap D * variation target := by
      unfold finitePositiveWeightDobrushinHeatBathGap
      ring

/-- Standard normalized random-scan rate `1 - (1-alpha)/|ι|`. -/
def finitePositiveWeightDobrushinRandomScanRate
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    {weight : (ι → G) → ℝ}
    (D : FinitePositiveWeightDobrushinL1MatrixData weight) : ℝ :=
  1 - finitePositiveWeightDobrushinHeatBathGap D / (Fintype.card ι : ℝ)

/-- For a nonempty coordinate type, the random-scan rate is nonnegative. -/
theorem finitePositiveWeightDobrushinRandomScanRate_nonneg
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    {weight : (ι → G) → ℝ}
    (D : FinitePositiveWeightDobrushinL1MatrixData weight)
    (hCard : 0 < Fintype.card ι) :
    0 ≤ finitePositiveWeightDobrushinRandomScanRate D := by
  have hCardPos : (0 : ℝ) < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr hCard
  have hCardOne : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hCard
  have hGapLeOne : finitePositiveWeightDobrushinHeatBathGap D ≤ 1 := by
    unfold finitePositiveWeightDobrushinHeatBathGap
    linarith [D.coefficient_nonneg]
  have hGapLeCard :
      finitePositiveWeightDobrushinHeatBathGap D ≤ (Fintype.card ι : ℝ) :=
    le_trans hGapLeOne hCardOne
  have hDivLeOne :
      finitePositiveWeightDobrushinHeatBathGap D /
          (Fintype.card ι : ℝ) ≤ 1 :=
    (div_le_one hCardPos).2 hGapLeCard
  unfold finitePositiveWeightDobrushinRandomScanRate
  linarith

/-- For a nonempty coordinate type, the random-scan rate is strictly below
one. -/
theorem finitePositiveWeightDobrushinRandomScanRate_lt_one
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    {weight : (ι → G) → ℝ}
    (D : FinitePositiveWeightDobrushinL1MatrixData weight)
    (hCard : 0 < Fintype.card ι) :
    finitePositiveWeightDobrushinRandomScanRate D < 1 := by
  have hCardPos : (0 : ℝ) < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr hCard
  have hQuotPos :
      0 < finitePositiveWeightDobrushinHeatBathGap D /
        (Fintype.card ι : ℝ) :=
    div_pos (finitePositiveWeightDobrushinHeatBathGap_pos D) hCardPos
  unfold finitePositiveWeightDobrushinRandomScanRate
  linarith

/-- Uniform average of all single-target updated variation profiles. -/
def finitePositiveWeightDobrushinRandomScanUpdatedVariation
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    {weight : (ι → G) → ℝ}
    (D : FinitePositiveWeightDobrushinL1MatrixData weight)
    (variation : ι → ℝ)
    (source : ι) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ *
    ∑ target : ι,
      finitePositiveWeightDobrushinUpdatedVariation
        D variation target source

/-- Random-scan averaging preserves nonnegativity of variation profiles. -/
theorem finitePositiveWeightDobrushinRandomScanUpdatedVariation_nonneg
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    {weight : (ι → G) → ℝ}
    (D : FinitePositiveWeightDobrushinL1MatrixData weight)
    (variation : ι → ℝ)
    (hVariation : ∀ e : ι, 0 ≤ variation e)
    (source : ι) :
    0 ≤ finitePositiveWeightDobrushinRandomScanUpdatedVariation
      D variation source := by
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.sum_nonneg fun target _htarget =>
      finitePositiveWeightDobrushinUpdatedVariation_nonneg
        D variation hVariation target source)

/-- Total averaged variation is the normalized average of the single-target
totals. -/
theorem finitePositiveWeightDobrushinRandomScanUpdatedVariation_total_eq
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    {weight : (ι → G) → ℝ}
    (D : FinitePositiveWeightDobrushinL1MatrixData weight)
    (variation : ι → ℝ) :
    finiteProductVariationTotal
        (finitePositiveWeightDobrushinRandomScanUpdatedVariation D variation) =
      (Fintype.card ι : ℝ)⁻¹ *
        ∑ target : ι,
          finiteProductVariationTotal
            (finitePositiveWeightDobrushinUpdatedVariation
              D variation target) := by
  unfold finiteProductVariationTotal
  unfold finitePositiveWeightDobrushinRandomScanUpdatedVariation
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]

/-- Generic Dobrushin random-scan contraction of total declared variation. -/
theorem finitePositiveWeightDobrushinRandomScanUpdatedVariation_total_le_rate_mul
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    {weight : (ι → G) → ℝ}
    (D : FinitePositiveWeightDobrushinL1MatrixData weight)
    (variation : ι → ℝ)
    (hVariation : ∀ e : ι, 0 ≤ variation e)
    (hCard : 0 < Fintype.card ι) :
    finiteProductVariationTotal
        (finitePositiveWeightDobrushinRandomScanUpdatedVariation D variation) ≤
      finitePositiveWeightDobrushinRandomScanRate D *
        finiteProductVariationTotal variation := by
  let n : ℝ := Fintype.card ι
  let total : ℝ := finiteProductVariationTotal variation
  let gap : ℝ := finitePositiveWeightDobrushinHeatBathGap D
  have hCardPos : 0 < n := Nat.cast_pos.mpr hCard
  have hCardNe : n ≠ 0 := ne_of_gt hCardPos
  have hInvNonneg : 0 ≤ n⁻¹ := inv_nonneg.mpr hCardPos.le
  have hTargetSum :
      (∑ target : ι,
        finiteProductVariationTotal
          (finitePositiveWeightDobrushinUpdatedVariation D variation target)) ≤
      ∑ target : ι, (total - gap * variation target) := by
    apply Finset.sum_le_sum
    intro target _htarget
    exact finitePositiveWeightDobrushinUpdatedVariation_total_le
      D variation hVariation target
  have hConstSum : (∑ _target : ι, total) = n * total := by
    simp [n, nsmul_eq_mul]
  have hDropSum :
      (∑ target : ι, gap * variation target) = gap * total := by
    unfold total finiteProductVariationTotal
    rw [← Finset.mul_sum]
  rw [finitePositiveWeightDobrushinRandomScanUpdatedVariation_total_eq]
  change n⁻¹ *
      (∑ target : ι,
        finiteProductVariationTotal
          (finitePositiveWeightDobrushinUpdatedVariation D variation target)) ≤
    finitePositiveWeightDobrushinRandomScanRate D * total
  calc
    n⁻¹ *
        (∑ target : ι,
          finiteProductVariationTotal
            (finitePositiveWeightDobrushinUpdatedVariation
              D variation target)) ≤
      n⁻¹ * ∑ target : ι, (total - gap * variation target) :=
      mul_le_mul_of_nonneg_left hTargetSum hInvNonneg
    _ = n⁻¹ * (n * total - gap * total) := by
      rw [Finset.sum_sub_distrib, hConstSum, hDropSum]
    _ = finitePositiveWeightDobrushinRandomScanRate D * total := by
      dsimp [n, gap]
      unfold finitePositiveWeightDobrushinRandomScanRate
      field_simp [hCardNe]

/-- Uniform random-scan conditional expectation operator for an arbitrary
positive finite product weight. -/
def finitePositiveWeightRandomScanConditionalExpectation
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (f : (ι → G) → ℝ)
    (A : ι → G) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ *
    ∑ target : ι,
      finitePositiveWeightSingleSiteExpectation weight f A target

/-- A variation bound for `f` generates the sharp averaged Dobrushin variation
bound for its random-scan conditional expectation. -/
noncomputable def FiniteProductVariationBound.randomScanVariationBound
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    {weight : (ι → G) → ℝ}
    (hweight : ∀ A : ι → G, 0 < weight A)
    {f : (ι → G) → ℝ}
    (P : FiniteProductVariationBound f)
    (D : FinitePositiveWeightDobrushinL1MatrixData weight) :
    FiniteProductVariationBound
      (finitePositiveWeightRandomScanConditionalExpectation weight f) := by
  refine
    { variation :=
        finitePositiveWeightDobrushinRandomScanUpdatedVariation D P.variation
      variation_nonneg :=
        finitePositiveWeightDobrushinRandomScanUpdatedVariation_nonneg
          D P.variation P.variation_nonneg
      variation_bound := ?_ }
  intro source A B hAgree
  have hInvNonneg : 0 ≤ (Fintype.card ι : ℝ)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg _)
  have hTarget (target : ι) :
      |finitePositiveWeightSingleSiteExpectation weight f A target -
          finitePositiveWeightSingleSiteExpectation weight f B target| ≤
        finitePositiveWeightDobrushinUpdatedVariation
          D P.variation target source := by
    simpa [finitePositiveWeightDobrushinUpdatedVariation] using
      P.singleSiteExpectation_difference_abs_le
        hweight D target source A B hAgree
  have hSum :
      |∑ target : ι,
        (finitePositiveWeightSingleSiteExpectation weight f A target -
          finitePositiveWeightSingleSiteExpectation weight f B target)| ≤
        ∑ target : ι,
          finitePositiveWeightDobrushinUpdatedVariation
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
          finitePositiveWeightDobrushinUpdatedVariation
            D P.variation target source := by
        apply Finset.sum_le_sum
        intro target _htarget
        exact hTarget target
  unfold finitePositiveWeightRandomScanConditionalExpectation
  unfold finitePositiveWeightDobrushinRandomScanUpdatedVariation
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
          finitePositiveWeightDobrushinUpdatedVariation
            D P.variation target source :=
      mul_le_mul_of_nonneg_left hSum hInvNonneg

/-- The generic random-scan operator contracts the total declared variation at
the standard Dobrushin rate. -/
theorem FiniteProductVariationBound.randomScan_totalVariation_le_rate_mul
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    {weight : (ι → G) → ℝ}
    (hweight : ∀ A : ι → G, 0 < weight A)
    {f : (ι → G) → ℝ}
    (P : FiniteProductVariationBound f)
    (D : FinitePositiveWeightDobrushinL1MatrixData weight)
    (hCard : 0 < Fintype.card ι) :
    finiteProductVariationTotal
        (P.randomScanVariationBound hweight D).variation ≤
      finitePositiveWeightDobrushinRandomScanRate D *
        finiteProductVariationTotal P.variation := by
  change
    finiteProductVariationTotal
      (finitePositiveWeightDobrushinRandomScanUpdatedVariation D P.variation) ≤
    finitePositiveWeightDobrushinRandomScanRate D *
      finiteProductVariationTotal P.variation
  exact finitePositiveWeightDobrushinRandomScanUpdatedVariation_total_le_rate_mul
    D P.variation P.variation_nonneg hCard

end

end MathlibAnalytic
end MGAP4D
