import MGAP4D.MathlibAnalytic.FinitePositiveWeightRandomScanHilbertSpectral
import MGAP4D.MathlibAnalytic.FinitePositiveWeightSingleSiteVarianceDirichlet
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- Updating one coordinate twice retains only the last value. -/
@[simp] theorem finiteProduct_update_update_same
    {ι G : Type}
    [DecidableEq ι]
    (A : ι → G)
    (e : ι)
    (g h : G) :
    Function.update (Function.update A e g) e h =
      Function.update A e h := by
  funext i
  by_cases hie : i = e
  · subst i
    simp
  · simp [Function.update, hie]

/-- The one-site conditional law is unchanged when only the currently stored
value at the conditioned coordinate is changed. -/
theorem finitePositiveWeightSingleSiteProbability_update
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (A : ι → G)
    (e : ι)
    (g h : G) :
    finitePositiveWeightSingleSiteProbability weight
        (Function.update A e g) e h =
      finitePositiveWeightSingleSiteProbability weight A e h := by
  unfold finitePositiveWeightSingleSiteProbability
  rw [finitePositiveWeightSingleSitePartition_update,
    finiteProduct_update_update_same]

/-- One-site conditional expectation is constant along the corresponding
conditioning fiber. -/
theorem finitePositiveWeightSingleSiteExpectation_update
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (f : (ι → G) → ℝ)
    (A : ι → G)
    (e : ι)
    (g : G) :
    finitePositiveWeightSingleSiteExpectation weight f
        (Function.update A e g) e =
      finitePositiveWeightSingleSiteExpectation weight f A e := by
  classical
  unfold finitePositiveWeightSingleSiteExpectation
  apply Finset.sum_congr rfl
  intro h _hh
  rw [finitePositiveWeightSingleSiteProbability_update,
    finiteProduct_update_update_same]

/-- Exact one-site conditional expectation is idempotent. -/
theorem finitePositiveWeightSingleSiteExpectation_idempotent
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (f : (ι → G) → ℝ)
    (e : ι) :
    (fun A => finitePositiveWeightSingleSiteExpectation weight
      (fun B => finitePositiveWeightSingleSiteExpectation weight f B e)
      A e) =
      (fun A => finitePositiveWeightSingleSiteExpectation weight f A e) := by
  funext A
  unfold finitePositiveWeightSingleSiteExpectation
  calc
    (∑ g : G,
      finitePositiveWeightSingleSiteProbability weight A e g *
        finitePositiveWeightSingleSiteExpectation weight f
          (Function.update A e g) e) =
      ∑ g : G,
        finitePositiveWeightSingleSiteProbability weight A e g *
          finitePositiveWeightSingleSiteExpectation weight f A e := by
      apply Finset.sum_congr rfl
      intro g _hg
      rw [finitePositiveWeightSingleSiteExpectation_update]
    _ = (∑ g : G,
          finitePositiveWeightSingleSiteProbability weight A e g) *
        finitePositiveWeightSingleSiteExpectation weight f A e := by
      rw [Finset.sum_mul]
    _ = finitePositiveWeightSingleSiteExpectation weight f A e := by
      rw [finitePositiveWeightSingleSiteProbability_sum_eq_one
        weight hweight A e]
      ring

/-- Weighted integration of a one-site conditional expectation preserves the
unnormalized first moment. -/
theorem finitePositiveWeightSum_singleSiteExpectation
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (f : (ι → G) → ℝ)
    (e : ι) :
    finitePositiveWeightSum weight
        (fun A => finitePositiveWeightSingleSiteExpectation weight f A e) =
      finitePositiveWeightSum weight f := by
  let one : (ι → G) → ℝ := fun _ => 1
  have hOne :
      (fun A => finitePositiveWeightSingleSiteExpectation weight one A e) =
        one := by
    funext A
    exact finitePositiveWeightSingleSiteExpectation_one
      weight hweight A e
  calc
    finitePositiveWeightSum weight
        (fun A => finitePositiveWeightSingleSiteExpectation weight f A e) =
      finitePositiveWeightPairing weight
        (fun A => finitePositiveWeightSingleSiteExpectation weight f A e)
        one := by
      classical
      unfold finitePositiveWeightSum finitePositiveWeightPairing one
      apply Finset.sum_congr rfl
      intro A _hA
      ring
    _ = finitePositiveWeightPairing weight f
        (fun A => finitePositiveWeightSingleSiteExpectation weight one A e) :=
      finitePositiveWeightSingleSiteExpectation_pairing_symm
        weight e f one
    _ = finitePositiveWeightPairing weight f one := by
      rw [hOne]
    _ = finitePositiveWeightSum weight f := by
      classical
      unfold finitePositiveWeightSum finitePositiveWeightPairing one
      apply Finset.sum_congr rfl
      intro A _hA
      ring

/-- For an exact one-site conditional projection, the squared projected norm
is its mixed pairing with the original observable. -/
theorem finitePositiveWeightSingleSiteExpectation_pairing_self_eq_mixed
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (f : (ι → G) → ℝ)
    (e : ι) :
    finitePositiveWeightPairing weight
        (fun A => finitePositiveWeightSingleSiteExpectation weight f A e)
        (fun A => finitePositiveWeightSingleSiteExpectation weight f A e) =
      finitePositiveWeightPairing weight
        (fun A => finitePositiveWeightSingleSiteExpectation weight f A e) f := by
  let p : (ι → G) → ℝ :=
    fun A => finitePositiveWeightSingleSiteExpectation weight f A e
  have hpIdem :
      (fun A => finitePositiveWeightSingleSiteExpectation weight p A e) = p := by
    exact finitePositiveWeightSingleSiteExpectation_idempotent
      weight hweight f e
  calc
    finitePositiveWeightPairing weight p p =
      finitePositiveWeightPairing weight f
        (fun A => finitePositiveWeightSingleSiteExpectation weight p A e) :=
      finitePositiveWeightSingleSiteExpectation_pairing_symm
        weight e f p
    _ = finitePositiveWeightPairing weight f p := by
      rw [hpIdem]
    _ = finitePositiveWeightPairing weight p f :=
      finitePositiveWeightPairing_symm weight f p

/-- The unnormalized average of the one-site conditional variance. -/
def finitePositiveWeightAveragedSingleSiteVariance
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (f : (ι → G) → ℝ)
    (e : ι) : ℝ :=
  ∑ A : ι → G,
    weight A * finitePositiveWeightSingleSiteVariance weight f A e

/-- Averaged one-site variance is nonnegative under a positive weight. -/
theorem finitePositiveWeightAveragedSingleSiteVariance_nonneg
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (f : (ι → G) → ℝ)
    (e : ι) :
    0 ≤ finitePositiveWeightAveragedSingleSiteVariance weight f e := by
  classical
  unfold finitePositiveWeightAveragedSingleSiteVariance
  exact Finset.sum_nonneg fun A _hA =>
    mul_nonneg (le_of_lt (hweight A))
      (finitePositiveWeightSingleSiteVariance_nonneg weight f A e)

/-- The averaged one-site conditional variance is exactly the weighted
quadratic defect of the corresponding conditional projection. -/
theorem finitePositiveWeightAveragedSingleSiteVariance_eq_pairing_sub
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (f : (ι → G) → ℝ)
    (e : ι) :
    finitePositiveWeightAveragedSingleSiteVariance weight f e =
      finitePositiveWeightPairing weight f f -
        finitePositiveWeightPairing weight
          (fun A => finitePositiveWeightSingleSiteExpectation weight f A e) f := by
  classical
  let f2 : (ι → G) → ℝ := fun A => f A ^ 2
  let p : (ι → G) → ℝ :=
    fun A => finitePositiveWeightSingleSiteExpectation weight f A e
  have hFirst :
      finitePositiveWeightSum weight
          (fun A => finitePositiveWeightSingleSiteExpectation weight f2 A e) =
        finitePositiveWeightSum weight f2 :=
    finitePositiveWeightSum_singleSiteExpectation
      weight hweight f2 e
  have hSecond :
      finitePositiveWeightPairing weight p p =
        finitePositiveWeightPairing weight p f := by
    simpa [p] using
      finitePositiveWeightSingleSiteExpectation_pairing_self_eq_mixed
        weight hweight f e
  calc
    finitePositiveWeightAveragedSingleSiteVariance weight f e =
      (∑ A : ι → G,
        weight A *
          finitePositiveWeightSingleSiteExpectation weight f2 A e) -
        ∑ A : ι → G, weight A * (p A) ^ 2 := by
      unfold finitePositiveWeightAveragedSingleSiteVariance
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro A _hA
      rw [finitePositiveWeightSingleSiteVariance_eq_secondMoment_sub_mean_sq
        weight hweight f A e]
      unfold finitePositiveWeightSingleSiteExpectation f2 p
      ring
    _ = finitePositiveWeightSum weight f2 -
        finitePositiveWeightPairing weight p p := by
      rw [← hFirst]
      congr 1
      · rfl
      · unfold finitePositiveWeightPairing
        apply Finset.sum_congr rfl
        intro A _hA
        ring
    _ = finitePositiveWeightSum weight f2 -
        finitePositiveWeightPairing weight p f := by
      rw [hSecond]
    _ = finitePositiveWeightPairing weight f f -
        finitePositiveWeightPairing weight p f := by
      congr 1
      unfold finitePositiveWeightSum finitePositiveWeightPairing f2
      apply Finset.sum_congr rfl
      intro A _hA
      ring
    _ = finitePositiveWeightPairing weight f f -
        finitePositiveWeightPairing weight
          (fun A => finitePositiveWeightSingleSiteExpectation weight f A e) f := by
      rfl

/-- Sum of all one-site conditional variances. -/
def finitePositiveWeightTotalSingleSiteVariance
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (f : (ι → G) → ℝ) : ℝ :=
  ∑ e : ι, finitePositiveWeightAveragedSingleSiteVariance weight f e

/-- The random-scan quadratic form is the normalized average of the one-site
conditional-projection quadratic forms. -/
theorem finitePositiveWeightPairing_randomScan_eq_inv_card_mul_sum
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (weight : (ι → G) → ℝ)
    (f : (ι → G) → ℝ) :
    finitePositiveWeightPairing weight
        (finitePositiveWeightRandomScanConditionalExpectation weight f) f =
      (Fintype.card ι : ℝ)⁻¹ *
        ∑ e : ι,
          finitePositiveWeightPairing weight
            (fun A => finitePositiveWeightSingleSiteExpectation weight f A e) f := by
  let leftPair := finitePositiveWeightPairingLeftLinearMap weight f
  calc
    finitePositiveWeightPairing weight
        (finitePositiveWeightRandomScanConditionalExpectation weight f) f =
      leftPair (finitePositiveWeightRandomScanLinearMap weight f) := by
        rw [finitePositiveWeightRandomScanLinearMap_apply]
        rfl
    _ = (Fintype.card ι : ℝ)⁻¹ *
        ∑ e : ι,
          finitePositiveWeightPairing weight
            (finitePositiveWeightSingleSiteExpectationLinearMap weight e f) f := by
      simp [leftPair, finitePositiveWeightRandomScanLinearMap]
    _ = (Fintype.card ι : ℝ)⁻¹ *
        ∑ e : ι,
          finitePositiveWeightPairing weight
            (fun A => finitePositiveWeightSingleSiteExpectation weight f A e) f := by
      rfl

/-- Exact identity between total local conditional variance and the
unnormalized random-scan Rayleigh defect. -/
theorem finitePositiveWeightTotalSingleSiteVariance_eq_card_mul_randomScan_defect
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (hCard : 0 < Fintype.card ι)
    (f : (ι → G) → ℝ) :
    finitePositiveWeightTotalSingleSiteVariance weight f =
      (Fintype.card ι : ℝ) *
        (finitePositiveWeightPairing weight f f -
          finitePositiveWeightPairing weight
            (finitePositiveWeightRandomScanConditionalExpectation weight f) f) := by
  classical
  let n : ℝ := Fintype.card ι
  let q : ℝ := finitePositiveWeightPairing weight f f
  let local : ι → ℝ := fun e =>
    finitePositiveWeightPairing weight
      (fun A => finitePositiveWeightSingleSiteExpectation weight f A e) f
  let scan : ℝ := finitePositiveWeightPairing weight
    (finitePositiveWeightRandomScanConditionalExpectation weight f) f
  have hn : n ≠ 0 := by
    exact ne_of_gt (Nat.cast_pos.mpr hCard)
  have hScan : scan = n⁻¹ * ∑ e : ι, local e := by
    simpa [scan, n, local] using
      finitePositiveWeightPairing_randomScan_eq_inv_card_mul_sum
        weight f
  have hLocalSum : (∑ e : ι, local e) = n * scan := by
    calc
      (∑ e : ι, local e) = n * (n⁻¹ * ∑ e : ι, local e) := by
        field_simp [hn]
      _ = n * scan := by rw [← hScan]
  calc
    finitePositiveWeightTotalSingleSiteVariance weight f =
      ∑ e : ι, (q - local e) := by
        unfold finitePositiveWeightTotalSingleSiteVariance
        apply Finset.sum_congr rfl
        intro e _he
        simpa [q, local] using
          finitePositiveWeightAveragedSingleSiteVariance_eq_pairing_sub
            weight hweight f e
    _ = n * q - ∑ e : ι, local e := by
      rw [Finset.sum_sub_distrib]
      simp [n]
    _ = n * q - n * scan := by rw [hLocalSum]
    _ = n * (q - scan) := by ring
    _ = (Fintype.card ι : ℝ) *
        (finitePositiveWeightPairing weight f f -
          finitePositiveWeightPairing weight
            (finitePositiveWeightRandomScanConditionalExpectation weight f) f) := by
      rfl

end

end MathlibAnalytic
end MGAP4D
