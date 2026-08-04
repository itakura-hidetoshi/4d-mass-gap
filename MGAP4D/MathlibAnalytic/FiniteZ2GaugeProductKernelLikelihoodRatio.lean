import MGAP4D.MathlibAnalytic.FiniteZ2GaugeConfigurationUniformTransfer
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Sharp one-coordinate likelihood-ratio majorant for the normalized `Z₂`
crossing kernel. -/
def finiteZ2CrossingLikelihoodRatio (q : ℝ) : ℝ :=
  (1 + q) / (1 - q)

/-- The likelihood-ratio majorant is positive for `0 ≤ q < 1`. -/
theorem finiteZ2CrossingLikelihoodRatio_pos
    {q : ℝ}
    (hq0 : 0 ≤ q)
    (hq1 : q < 1) :
    0 < finiteZ2CrossingLikelihoodRatio q := by
  unfold finiteZ2CrossingLikelihoodRatio
  exact div_pos (by linarith) (by linarith)

/-- The majorant is at least one. -/
theorem one_le_finiteZ2CrossingLikelihoodRatio
    {q : ℝ}
    (hq0 : 0 ≤ q)
    (hq1 : q < 1) :
    1 ≤ finiteZ2CrossingLikelihoodRatio q := by
  unfold finiteZ2CrossingLikelihoodRatio
  rw [le_div_iff₀ (by linarith : 0 < 1 - q)]
  linarith

/-- Changing the observed value of one normalized two-state crossing factor
changes every likelihood by at most the sharp ratio `(1+q)/(1-q)`. -/
theorem finiteZ2NormalizedLocalKernel_le_likelihoodRatio_mul
    {q : ℝ}
    (hq0 : 0 ≤ q)
    (hq1 : q < 1)
    (x y z : Bool) :
    finiteZ2NormalizedLocalKernel q x y ≤
      finiteZ2CrossingLikelihoodRatio q *
        finiteZ2NormalizedLocalKernel q x z := by
  have hden : 0 < 1 - q := by linarith
  cases x <;> cases y <;> cases z <;>
    simp [finiteZ2NormalizedLocalKernel,
      finiteZ2CrossingLikelihoodRatio] <;>
    field_simp [ne_of_gt hden] <;>
    nlinarith

/-- Replace one coordinate of an actual finite `Z₂` configuration. -/
def finiteZ2GaugeReplaceCoordinate
    {ι : Type}
    [DecidableEq ι]
    (B : ι → Z2Gauge)
    (e : ι)
    (g : Z2Gauge) : ι → Z2Gauge :=
  Function.update B e g

@[simp] theorem finiteZ2GaugeReplaceCoordinate_same
    {ι : Type}
    [DecidableEq ι]
    (B : ι → Z2Gauge)
    (e : ι)
    (g : Z2Gauge) :
    finiteZ2GaugeReplaceCoordinate B e g e = g := by
  simp [finiteZ2GaugeReplaceCoordinate]

@[simp] theorem finiteZ2GaugeReplaceCoordinate_noteq
    {ι : Type}
    [DecidableEq ι]
    (B : ι → Z2Gauge)
    (e i : ι)
    (g : Z2Gauge)
    (hie : i ≠ e) :
    finiteZ2GaugeReplaceCoordinate B e g i = B i := by
  simp [finiteZ2GaugeReplaceCoordinate, hie]

/-- The normalized product crossing kernel is entrywise nonnegative. -/
theorem finiteZ2GaugeNormalizedProductKernel_nonneg
    {q : ℝ}
    (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1)
    (ι : Type)
    [Fintype ι]
    [DecidableEq ι]
    (A B : ι → Z2Gauge) :
    0 ≤ finiteZ2GaugeNormalizedProductKernel q ι A B := by
  rw [finiteZ2GaugeNormalizedProductKernel_apply]
  apply Finset.prod_nonneg
  intro e _he
  exact finiteZ2NormalizedLocalKernel_nonneg (by linarith) hq1 _ _

/-- Dimension-free one-coordinate likelihood-ratio bound for the actual
finite-configuration product kernel. -/
theorem finiteZ2GaugeNormalizedProductKernel_le_likelihoodRatio_mul_replace
    {q : ℝ}
    (hq0 : 0 ≤ q)
    (hq1 : q < 1)
    (ι : Type)
    [Fintype ι]
    [DecidableEq ι]
    (A B : ι → Z2Gauge)
    (e : ι)
    (g : Z2Gauge) :
    finiteZ2GaugeNormalizedProductKernel q ι A B ≤
      finiteZ2CrossingLikelihoodRatio q *
        finiteZ2GaugeNormalizedProductKernel q ι A
          (finiteZ2GaugeReplaceCoordinate B e g) := by
  classical
  rw [finiteZ2GaugeNormalizedProductKernel_apply,
    finiteZ2GaugeNormalizedProductKernel_apply]
  let r := finiteZ2CrossingLikelihoodRatio q
  calc
    (∏ i : ι,
        finiteZ2NormalizedLocalKernel q
          (boolEquivZ2Gauge.symm (A i))
          (boolEquivZ2Gauge.symm (B i))) ≤
      ∏ i : ι,
        ((if i = e then r else 1) *
          finiteZ2NormalizedLocalKernel q
            (boolEquivZ2Gauge.symm (A i))
            (boolEquivZ2Gauge.symm
              (finiteZ2GaugeReplaceCoordinate B e g i))) := by
      apply Finset.prod_le_prod
      · intro i _hi
        exact finiteZ2NormalizedLocalKernel_nonneg
          (by linarith) hq1.le _ _
      · intro i _hi
        by_cases hie : i = e
        · subst i
          simp only [if_pos rfl, finiteZ2GaugeReplaceCoordinate_same]
          exact finiteZ2NormalizedLocalKernel_le_likelihoodRatio_mul
            hq0 hq1 _ _ _
        · simp [hie, finiteZ2GaugeReplaceCoordinate_noteq, r]
    _ = (∏ i : ι, if i = e then r else 1) *
        ∏ i : ι,
          finiteZ2NormalizedLocalKernel q
            (boolEquivZ2Gauge.symm (A i))
            (boolEquivZ2Gauge.symm
              (finiteZ2GaugeReplaceCoordinate B e g i)) := by
      rw [Finset.prod_mul_distrib]
    _ = r *
        ∏ i : ι,
          finiteZ2NormalizedLocalKernel q
            (boolEquivZ2Gauge.symm (A i))
            (boolEquivZ2Gauge.symm
              (finiteZ2GaugeReplaceCoordinate B e g i)) := by
      simp
    _ = finiteZ2CrossingLikelihoodRatio q *
        ∏ i : ι,
          finiteZ2NormalizedLocalKernel q
            (boolEquivZ2Gauge.symm (A i))
            (boolEquivZ2Gauge.symm
              (finiteZ2GaugeReplaceCoordinate B e g i)) := by
      rfl

/-- The same dimension-free ratio survives summation against every
pointwise-nonnegative input weight. -/
theorem finiteZ2GaugeNormalizedProductKernel_operator_le_likelihoodRatio_mul_replace
    {q : ℝ}
    (hq0 : 0 ≤ q)
    (hq1 : q < 1)
    (ι : Type)
    [Fintype ι]
    [DecidableEq ι]
    (f : FiniteBoundaryHilbert (ι → Z2Gauge))
    (hf : FiniteBoundaryPointwiseNonnegative f)
    (B : ι → Z2Gauge)
    (e : ι)
    (g : Z2Gauge) :
    finiteKernelOperator
        (finiteZ2GaugeNormalizedProductKernel q ι) f B ≤
      finiteZ2CrossingLikelihoodRatio q *
        finiteKernelOperator
          (finiteZ2GaugeNormalizedProductKernel q ι) f
          (finiteZ2GaugeReplaceCoordinate B e g) := by
  rw [finiteKernelOperator_apply, finiteKernelOperator_apply,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro A _hA
  calc
    finiteZ2GaugeNormalizedProductKernel q ι A B * f A ≤
      (finiteZ2CrossingLikelihoodRatio q *
          finiteZ2GaugeNormalizedProductKernel q ι A
            (finiteZ2GaugeReplaceCoordinate B e g)) * f A :=
      mul_le_mul_of_nonneg_right
        (finiteZ2GaugeNormalizedProductKernel_le_likelihoodRatio_mul_replace
          hq0 hq1 ι A B e g)
        (hf A)
    _ = finiteZ2CrossingLikelihoodRatio q *
        (finiteZ2GaugeNormalizedProductKernel q ι A
          (finiteZ2GaugeReplaceCoordinate B e g) * f A) := by
      ring

end

end MathlibAnalytic
end MGAP4D
