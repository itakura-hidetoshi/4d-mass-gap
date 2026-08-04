import MGAP4D.MathlibAnalytic.FiniteProductParallelVariationContraction
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Coordinates on which two finite-product configurations disagree. -/
noncomputable def finiteProductMismatchSet
    {ι G : Type}
    [Fintype ι]
    (A B : ι → G) : Finset ι := by
  classical
  exact Finset.univ.filter fun e => A e ≠ B e

/-- Patching exactly the mismatch coordinates of `A` with values from `B`
returns `B`. -/
@[simp] theorem finiteProductPatch_mismatchSet
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    (A B : ι → G) :
    finiteProductPatch A B (finiteProductMismatchSet A B) = B := by
  classical
  funext e
  by_cases hEq : A e = B e
  · simp [finiteProductPatch, finiteProductMismatchSet, hEq]
  · simp [finiteProductPatch, finiteProductMismatchSet, hEq]

/-- A declared coordinate-variation profile telescopes along any finite patch
of coordinates. -/
theorem FiniteProductVariationBound.difference_abs_le_patch_sum
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    {f : (ι → G) → ℝ}
    (P : FiniteProductVariationBound f)
    (A B : ι → G)
    (s : Finset ι) :
    |f A - f (finiteProductPatch A B s)| ≤
      ∑ e ∈ s, P.variation e := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert e s he ih =>
      have hStep :
          |f (finiteProductPatch A B s) -
              f (finiteProductPatch A B (insert e s))| ≤
            P.variation e :=
        P.variation_bound e
          (finiteProductPatch A B s)
          (finiteProductPatch A B (insert e s))
          (finiteProductPatch_agreeOff_insert A B s e)
      have hSplit :
          f A - f (finiteProductPatch A B (insert e s)) =
            (f A - f (finiteProductPatch A B s)) +
              (f (finiteProductPatch A B s) -
                f (finiteProductPatch A B (insert e s))) := by
        ring
      rw [hSplit]
      calc
        |(f A - f (finiteProductPatch A B s)) +
            (f (finiteProductPatch A B s) -
              f (finiteProductPatch A B (insert e s)))| ≤
          |f A - f (finiteProductPatch A B s)| +
            |f (finiteProductPatch A B s) -
              f (finiteProductPatch A B (insert e s))| :=
          abs_add_le _ _
        _ ≤ (∑ i ∈ s, P.variation i) + P.variation e :=
          add_le_add ih hStep
        _ = ∑ i ∈ insert e s, P.variation i := by
          rw [Finset.sum_insert he]
          ring

/-- Indicator that two configurations disagree at one coordinate. -/
noncomputable def finiteProductMismatchIndicator
    {ι G : Type}
    (A B : ι → G)
    (e : ι) : ℝ :=
  if A e = B e then 0 else 1

/-- The mismatch indicator is nonnegative. -/
theorem finiteProductMismatchIndicator_nonneg
    {ι G : Type}
    (A B : ι → G)
    (e : ι) :
    0 ≤ finiteProductMismatchIndicator A B e := by
  classical
  by_cases hEq : A e = B e
  · simp [finiteProductMismatchIndicator, hEq]
  · simp [finiteProductMismatchIndicator, hEq]

/-- A finite patch telescoping bound can be written as a sum of coordinate
variations weighted by exact mismatch indicators. -/
theorem FiniteProductVariationBound.difference_abs_le_mismatch_sum
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    {f : (ι → G) → ℝ}
    (P : FiniteProductVariationBound f)
    (A B : ι → G) :
    |f A - f B| ≤
      ∑ e : ι,
        finiteProductMismatchIndicator A B e * P.variation e := by
  classical
  have hPatch :=
    P.difference_abs_le_patch_sum A B (finiteProductMismatchSet A B)
  rw [finiteProductPatch_mismatchSet] at hPatch
  calc
    |f A - f B| ≤
        ∑ e ∈ finiteProductMismatchSet A B, P.variation e := hPatch
    _ = ∑ e : ι,
        finiteProductMismatchIndicator A B e * P.variation e := by
      unfold finiteProductMismatchSet finiteProductMismatchIndicator
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro e _he
      by_cases hEq : A e = B e
      · simp [hEq]
      · simp [hEq]

/-- Observable operator associated with a finite transition kernel.  The first
kernel argument is the sampled output configuration and the second is the
input/environment configuration. -/
noncomputable def finiteProductKernelObservableLinearMap
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (kernel : (ι → G) → (ι → G) → ℝ) :
    ((ι → G) → ℝ) →ₗ[ℝ] ((ι → G) → ℝ) where
  toFun f := fun A => ∑ X : ι → G, kernel X A * f X
  map_add' f g := by
    funext A
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro X _hX
    ring
  map_smul' c f := by
    funext A
    simp only [Pi.smul_apply, smul_eq_mul]
    calc
      (∑ X : ι → G, kernel X A * (c * f X)) =
          ∑ X : ι → G, c * (kernel X A * f X) := by
        apply Finset.sum_congr rfl
        intro X _hX
        ring
      _ = c * ∑ X : ι → G, kernel X A * f X := by
        rw [Finset.mul_sum]

@[simp] theorem finiteProductKernelObservableLinearMap_apply
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (kernel : (ι → G) → (ι → G) → ℝ)
    (f : (ι → G) → ℝ)
    (A : ι → G) :
    finiteProductKernelObservableLinearMap kernel f A =
      ∑ X : ι → G, kernel X A * f X :=
  rfl

/-- Coordinatewise coupling data for a finite-product transition kernel.
For two inputs differing only at `target`, `coupling target A B` couples the
corresponding output laws.  Its expected output mismatch at `source` is
bounded by `influence target source`. -/
structure FiniteProductKernelCouplingVariationData
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (kernel : (ι → G) → (ι → G) → ℝ) where
  influence : ι → ι → ℝ
  influence_nonneg :
    ∀ target source : ι, 0 ≤ influence target source
  coupling :
    ι → (ι → G) → (ι → G) → (ι → G) → (ι → G) → ℝ
  coupling_nonneg :
    ∀ (target : ι) (A B X Y : ι → G),
      FiniteProductAgreeOff A B target →
        0 ≤ coupling target A B X Y
  left_marginal :
    ∀ (target : ι) (A B X : ι → G),
      FiniteProductAgreeOff A B target →
        (∑ Y : ι → G, coupling target A B X Y) = kernel X A
  right_marginal :
    ∀ (target : ι) (A B Y : ι → G),
      FiniteProductAgreeOff A B target →
        (∑ X : ι → G, coupling target A B X Y) = kernel Y B
  mismatchExpectation_le :
    ∀ (target source : ι) (A B : ι → G),
      FiniteProductAgreeOff A B target →
        (∑ X : ι → G, ∑ Y : ι → G,
          coupling target A B X Y *
            finiteProductMismatchIndicator X Y source) ≤
          influence target source
  coefficient : ℝ
  coefficient_nonneg : 0 ≤ coefficient
  columnSum_le_coefficient :
    ∀ source : ι,
      (∑ target : ι, influence target source) ≤ coefficient
  coefficient_lt_one : coefficient < 1

/-- Coupling marginals rewrite the difference of two kernel expectations as
one coupled expectation of `f(X)-f(Y)`. -/
theorem FiniteProductKernelCouplingVariationData.expectation_sub_eq_coupling_sum
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    {kernel : (ι → G) → (ι → G) → ℝ}
    (D : FiniteProductKernelCouplingVariationData kernel)
    (f : (ι → G) → ℝ)
    (target : ι)
    (A B : ι → G)
    (hAgree : FiniteProductAgreeOff A B target) :
    finiteProductKernelObservableLinearMap kernel f A -
        finiteProductKernelObservableLinearMap kernel f B =
      ∑ X : ι → G, ∑ Y : ι → G,
        D.coupling target A B X Y * (f X - f Y) := by
  classical
  have hLeft :
      (∑ X : ι → G, kernel X A * f X) =
        ∑ X : ι → G, ∑ Y : ι → G,
          D.coupling target A B X Y * f X := by
    calc
      (∑ X : ι → G, kernel X A * f X) =
          ∑ X : ι → G,
            (∑ Y : ι → G, D.coupling target A B X Y) * f X := by
        apply Finset.sum_congr rfl
        intro X _hX
        rw [D.left_marginal target A B X hAgree]
      _ = ∑ X : ι → G, ∑ Y : ι → G,
          D.coupling target A B X Y * f X := by
        apply Finset.sum_congr rfl
        intro X _hX
        rw [Finset.sum_mul]
  have hRight :
      (∑ Y : ι → G, kernel Y B * f Y) =
        ∑ X : ι → G, ∑ Y : ι → G,
          D.coupling target A B X Y * f Y := by
    calc
      (∑ Y : ι → G, kernel Y B * f Y) =
          ∑ Y : ι → G,
            (∑ X : ι → G, D.coupling target A B X Y) * f Y := by
        apply Finset.sum_congr rfl
        intro Y _hY
        rw [D.right_marginal target A B Y hAgree]
      _ = ∑ Y : ι → G, ∑ X : ι → G,
          D.coupling target A B X Y * f Y := by
        apply Finset.sum_congr rfl
        intro Y _hY
        rw [Finset.sum_mul]
      _ = ∑ X : ι → G, ∑ Y : ι → G,
          D.coupling target A B X Y * f Y := by
        rw [Finset.sum_comm]
  rw [finiteProductKernelObservableLinearMap_apply,
    finiteProductKernelObservableLinearMap_apply,
    hLeft, hRight, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro X _hX
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro Y _hY
  ring

/-- A coordinate coupling controls the kernel expectation change by the
influence matrix applied to any declared variation profile. -/
theorem FiniteProductKernelCouplingVariationData.expectation_difference_abs_le
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    {kernel : (ι → G) → (ι → G) → ℝ}
    (D : FiniteProductKernelCouplingVariationData kernel)
    {f : (ι → G) → ℝ}
    (P : FiniteProductVariationBound f)
    (target : ι)
    (A B : ι → G)
    (hAgree : FiniteProductAgreeOff A B target) :
    |finiteProductKernelObservableLinearMap kernel f A -
        finiteProductKernelObservableLinearMap kernel f B| ≤
      ∑ source : ι,
        D.influence target source * P.variation source := by
  classical
  rw [D.expectation_sub_eq_coupling_sum f target A B hAgree]
  calc
    |∑ X : ι → G, ∑ Y : ι → G,
        D.coupling target A B X Y * (f X - f Y)| ≤
      ∑ X : ι → G,
        |∑ Y : ι → G,
          D.coupling target A B X Y * (f X - f Y)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ X : ι → G, ∑ Y : ι → G,
        |D.coupling target A B X Y * (f X - f Y)| := by
      apply Finset.sum_le_sum
      intro X _hX
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ X : ι → G, ∑ Y : ι → G,
        D.coupling target A B X Y * |f X - f Y| := by
      apply Finset.sum_congr rfl
      intro X _hX
      apply Finset.sum_congr rfl
      intro Y _hY
      rw [abs_mul, abs_of_nonneg (D.coupling_nonneg target A B X Y hAgree)]
    _ ≤ ∑ X : ι → G, ∑ Y : ι → G,
        D.coupling target A B X Y *
          (∑ source : ι,
            finiteProductMismatchIndicator X Y source *
              P.variation source) := by
      apply Finset.sum_le_sum
      intro X _hX
      apply Finset.sum_le_sum
      intro Y _hY
      exact mul_le_mul_of_nonneg_left
        (P.difference_abs_le_mismatch_sum X Y)
        (D.coupling_nonneg target A B X Y hAgree)
    _ = ∑ source : ι,
        (∑ X : ι → G, ∑ Y : ι → G,
          D.coupling target A B X Y *
            finiteProductMismatchIndicator X Y source) *
          P.variation source := by
      calc
        (∑ X : ι → G, ∑ Y : ι → G,
          D.coupling target A B X Y *
            (∑ source : ι,
              finiteProductMismatchIndicator X Y source *
                P.variation source)) =
          ∑ X : ι → G, ∑ Y : ι → G, ∑ source : ι,
            (D.coupling target A B X Y *
              finiteProductMismatchIndicator X Y source) *
                P.variation source := by
            apply Finset.sum_congr rfl
            intro X _hX
            apply Finset.sum_congr rfl
            intro Y _hY
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro source _hsource
            ring
        _ = ∑ X : ι → G, ∑ source : ι, ∑ Y : ι → G,
            (D.coupling target A B X Y *
              finiteProductMismatchIndicator X Y source) *
                P.variation source := by
            apply Finset.sum_congr rfl
            intro X _hX
            rw [Finset.sum_comm]
        _ = ∑ source : ι, ∑ X : ι → G, ∑ Y : ι → G,
            (D.coupling target A B X Y *
              finiteProductMismatchIndicator X Y source) *
                P.variation source := by
            rw [Finset.sum_comm]
        _ = ∑ source : ι,
            (∑ X : ι → G, ∑ Y : ι → G,
              D.coupling target A B X Y *
                finiteProductMismatchIndicator X Y source) *
              P.variation source := by
            apply Finset.sum_congr rfl
            intro source _hsource
            calc
              (∑ X : ι → G, ∑ Y : ι → G,
                (D.coupling target A B X Y *
                  finiteProductMismatchIndicator X Y source) *
                    P.variation source) =
                ∑ X : ι → G,
                  (∑ Y : ι → G,
                    D.coupling target A B X Y *
                      finiteProductMismatchIndicator X Y source) *
                    P.variation source := by
                  apply Finset.sum_congr rfl
                  intro X _hX
                  rw [Finset.sum_mul]
              _ = (∑ X : ι → G, ∑ Y : ι → G,
                    D.coupling target A B X Y *
                      finiteProductMismatchIndicator X Y source) *
                    P.variation source := by
                  rw [Finset.sum_mul]
    _ ≤ ∑ source : ι,
        D.influence target source * P.variation source := by
      apply Finset.sum_le_sum
      intro source _hsource
      exact mul_le_mul_of_nonneg_right
        (D.mismatchExpectation_le target source A B hAgree)
        (P.variation_nonneg source)

/-- Coordinate coupling data generates the direct parallel variation matrix
consumed by the generic spectral package. -/
noncomputable def
    FiniteProductKernelCouplingVariationData.toParallelVariationMatrixData
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    {kernel : (ι → G) → (ι → G) → ℝ}
    (D : FiniteProductKernelCouplingVariationData kernel) :
    FiniteProductParallelVariationMatrixData
      (finiteProductKernelObservableLinearMap kernel) :=
  { influence := D.influence
    influence_nonneg := D.influence_nonneg
    canonicalVariation_le := by
      intro f target
      let P := finiteProductCanonicalVariationBound f
      let Q : FiniteProductVariationBound
          (finiteProductKernelObservableLinearMap kernel f) :=
        { variation := fun target =>
            ∑ source : ι,
              D.influence target source * P.variation source
          variation_nonneg := by
            intro target
            exact Finset.sum_nonneg fun source _hsource =>
              mul_nonneg (D.influence_nonneg target source)
                (P.variation_nonneg source)
          variation_bound := by
            intro target A B hAgree
            exact D.expectation_difference_abs_le
              P target A B hAgree }
      exact finiteProductCanonicalVariation_le_variationBound Q target
    coefficient := D.coefficient
    coefficient_nonneg := D.coefficient_nonneg
    columnSum_le_coefficient := D.columnSum_le_coefficient
    coefficient_lt_one := D.coefficient_lt_one }

end

end MathlibAnalytic
end MGAP4D