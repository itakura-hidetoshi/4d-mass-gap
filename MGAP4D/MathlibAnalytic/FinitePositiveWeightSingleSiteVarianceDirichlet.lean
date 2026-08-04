import MGAP4D.MathlibAnalytic.FinitePositiveWeightSingleSiteConditional
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- The weighted centered first moment of a one-site conditional law vanishes. -/
theorem finitePositiveWeightSingleSite_centered_sum_eq_zero
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (f : (ι → G) → ℝ)
    (A : ι → G)
    (e : ι) :
    ∑ g : G,
      finitePositiveWeightSingleSiteProbability weight A e g *
        (f (Function.update A e g) -
          finitePositiveWeightSingleSiteExpectation weight f A e) = 0 := by
  let prob := finitePositiveWeightSingleSiteProbability weight A e
  let mean := finitePositiveWeightSingleSiteExpectation weight f A e
  have hMass : ∑ g : G, prob g = 1 := by
    simpa [prob] using
      finitePositiveWeightSingleSiteProbability_sum_eq_one
        weight hweight A e
  change ∑ g : G, prob g * (f (Function.update A e g) - mean) = 0
  calc
    (∑ g : G, prob g * (f (Function.update A e g) - mean)) =
        (∑ g : G, prob g * f (Function.update A e g)) -
          (∑ g : G, prob g * mean) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro g _hg
      ring
    _ = mean - (∑ g : G, prob g) * mean := by
      rw [Finset.sum_mul]
      rfl
    _ = 0 := by rw [hMass]; ring

/-- Conditional variance equals the second moment minus the square of the
conditional mean. -/
theorem finitePositiveWeightSingleSiteVariance_eq_secondMoment_sub_mean_sq
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (f : (ι → G) → ℝ)
    (A : ι → G)
    (e : ι) :
    finitePositiveWeightSingleSiteVariance weight f A e =
      (∑ g : G,
        finitePositiveWeightSingleSiteProbability weight A e g *
          f (Function.update A e g) ^ 2) -
        (finitePositiveWeightSingleSiteExpectation weight f A e) ^ 2 := by
  let prob := finitePositiveWeightSingleSiteProbability weight A e
  let mean := finitePositiveWeightSingleSiteExpectation weight f A e
  have hMass : ∑ g : G, prob g = 1 := by
    simpa [prob] using
      finitePositiveWeightSingleSiteProbability_sum_eq_one
        weight hweight A e
  have hMean :
      ∑ g : G, prob g * f (Function.update A e g) = mean := by
    rfl
  unfold finitePositiveWeightSingleSiteVariance
  change
    (∑ g : G, prob g * (f (Function.update A e g) - mean) ^ 2) = _
  calc
    (∑ g : G, prob g * (f (Function.update A e g) - mean) ^ 2) =
        (∑ g : G, prob g * f (Function.update A e g) ^ 2) -
          2 * mean *
            (∑ g : G, prob g * f (Function.update A e g)) +
          mean ^ 2 * (∑ g : G, prob g) := by
      simp_rw [sub_sq]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      congr 1
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro g _hg
        ring
      · rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro g _hg
        ring
    _ = (∑ g : G, prob g * f (Function.update A e g) ^ 2) -
        mean ^ 2 := by
      rw [hMean, hMass]
      ring
    _ = _ := by rfl

/-- The one-site conditional variance is exactly the symmetric pairwise local
Dirichlet form. -/
theorem finitePositiveWeightSingleSiteVariance_eq_pairDirichlet
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (f : (ι → G) → ℝ)
    (A : ι → G)
    (e : ι) :
    finitePositiveWeightSingleSiteVariance weight f A e =
      finitePositiveWeightSingleSitePairDirichlet weight f A e := by
  let prob := finitePositiveWeightSingleSiteProbability weight A e
  let mean := finitePositiveWeightSingleSiteExpectation weight f A e
  let second :=
    ∑ g : G, prob g * f (Function.update A e g) ^ 2
  have hMass : ∑ g : G, prob g = 1 := by
    simpa [prob] using
      finitePositiveWeightSingleSiteProbability_sum_eq_one
        weight hweight A e
  have hMean :
      ∑ g : G, prob g * f (Function.update A e g) = mean := by
    rfl
  have hVariance :
      finitePositiveWeightSingleSiteVariance weight f A e =
        second - mean ^ 2 := by
    simpa [prob, mean, second] using
      finitePositiveWeightSingleSiteVariance_eq_secondMoment_sub_mean_sq
        weight hweight f A e
  rw [hVariance]
  unfold finitePositiveWeightSingleSitePairDirichlet
  change
    second - mean ^ 2 =
      (2 : ℝ)⁻¹ *
        ∑ g : G, ∑ h : G,
          prob g * prob h *
            (f (Function.update A e g) -
              f (Function.update A e h)) ^ 2
  have hPairExpansion :
      (∑ g : G, ∑ h : G,
        prob g * prob h *
          (f (Function.update A e g) -
            f (Function.update A e h)) ^ 2) =
        2 * second - 2 * mean ^ 2 := by
    calc
      (∑ g : G, ∑ h : G,
        prob g * prob h *
          (f (Function.update A e g) -
            f (Function.update A e h)) ^ 2) =
          (∑ g : G, prob g * f (Function.update A e g) ^ 2) *
              (∑ h : G, prob h) -
            2 *
              ((∑ g : G, prob g * f (Function.update A e g)) *
                (∑ h : G, prob h * f (Function.update A e h))) +
            (∑ g : G, prob g) *
              (∑ h : G, prob h * f (Function.update A e h) ^ 2) := by
        rw [Finset.mul_sum, Finset.sum_mul]
        simp_rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro g _hg
        apply Finset.sum_congr rfl
        intro h _hh
        ring
      _ = 2 * second - 2 * mean ^ 2 := by
        rw [hMass, hMean]
        change second * 1 - 2 * (mean * mean) + 1 * second = _
        ring
  rw [hPairExpansion]
  ring

/-- Any ordered pair contribution is controlled by twice the one-site
conditional variance. -/
theorem finitePositiveWeightSingleSite_pairContribution_le_two_mul_variance
    {ι G : Type}
    [DecidableEq ι]
    [Fintype G]
    [Nonempty G]
    (weight : (ι → G) → ℝ)
    (hweight : ∀ A : ι → G, 0 < weight A)
    (f : (ι → G) → ℝ)
    (A : ι → G)
    (e : ι)
    (g h : G) :
    finitePositiveWeightSingleSiteProbability weight A e g *
        finitePositiveWeightSingleSiteProbability weight A e h *
        (f (Function.update A e g) -
          f (Function.update A e h)) ^ 2 ≤
      2 * finitePositiveWeightSingleSiteVariance weight f A e := by
  let term := fun g h : G =>
    finitePositiveWeightSingleSiteProbability weight A e g *
      finitePositiveWeightSingleSiteProbability weight A e h *
      (f (Function.update A e g) -
        f (Function.update A e h)) ^ 2
  have hterm_nonneg : ∀ g h : G, 0 ≤ term g h := by
    intro g' h'
    exact mul_nonneg
      (mul_nonneg
        (le_of_lt
          (finitePositiveWeightSingleSiteProbability_pos
            weight hweight A e g'))
        (le_of_lt
          (finitePositiveWeightSingleSiteProbability_pos
            weight hweight A e h')))
      (sq_nonneg _)
  have hTermLe : term g h ≤ ∑ g' : G, ∑ h' : G, term g' h' := by
    calc
      term g h ≤ ∑ h' : G, term g h' := by
        exact Finset.single_le_sum
          (fun h' _hh => hterm_nonneg g h') (Finset.mem_univ h)
      _ ≤ ∑ g' : G, ∑ h' : G, term g' h' := by
        exact Finset.single_le_sum
          (fun g' _hg => Finset.sum_nonneg fun h' _hh => hterm_nonneg g' h')
          (Finset.mem_univ g)
  have hVariance :=
    finitePositiveWeightSingleSiteVariance_eq_pairDirichlet
      weight hweight f A e
  unfold finitePositiveWeightSingleSitePairDirichlet at hVariance
  change term g h ≤ _
  change
    finitePositiveWeightSingleSiteVariance weight f A e =
      (2 : ℝ)⁻¹ * (∑ g' : G, ∑ h' : G, term g' h') at hVariance
  nlinarith

end

end MathlibAnalytic
end MGAP4D
