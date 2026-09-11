import MGAP4D.MathlibAnalytic.FiniteOrientedWilsonSingleLinkVarianceDomination
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators ENNReal

noncomputable section

/-- Two conditionally possible link values with probability at least `delta`
force a quantitative conditional-variance lower bound. -/
theorem finite_oriented_singleLinkConditionalVariance_twoPoint_lower
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (A : L.Configuration)
    (e : L.Edge)
    (g h : L.Gauge)
    (delta : ℝ)
    (hg : delta ≤ (L.singleLinkConditionalPMF A e g).toReal)
    (hh : delta ≤ (L.singleLinkConditionalPMF A e h).toReal) :
    delta *
        ((f (L.replaceLink A e g) - f (L.replaceLink A e h)) ^ 2 / 4) ≤
      L.singleLinkConditionalVariance f A e := by
  classical
  let mean := L.singleLinkConditionalExpectation f A e
  let value : L.Gauge → ℝ := fun k => f (L.replaceLink A e k)
  let probability : L.Gauge → ℝ := fun k =>
    (L.singleLinkConditionalPMF A e k).toReal
  change delta * ((value g - value h) ^ 2 / 4) ≤
    ∑ k : L.Gauge, probability k * (value k - mean) ^ 2
  have hGeometry :
      (value g - value h) ^ 2 ≤
        2 * (value g - mean) ^ 2 + 2 * (value h - mean) ^ 2 := by
    nlinarith [sq_nonneg ((value g - mean) + (value h - mean))]
  by_cases hLeft :
      (value g - value h) ^ 2 / 4 ≤ (value g - mean) ^ 2
  · have hTerm :
        delta * ((value g - value h) ^ 2 / 4) ≤
          probability g * (value g - mean) ^ 2 := by
      calc
        delta * ((value g - value h) ^ 2 / 4) ≤
            probability g * ((value g - value h) ^ 2 / 4) :=
          mul_le_mul_of_nonneg_right hg
            (div_nonneg (sq_nonneg _) (by norm_num))
        _ ≤ probability g * (value g - mean) ^ 2 :=
          mul_le_mul_of_nonneg_left hLeft ENNReal.toReal_nonneg
    have hSingle :
        probability g * (value g - mean) ^ 2 ≤
          ∑ k : L.Gauge, probability k * (value k - mean) ^ 2 := by
      exact Finset.single_le_sum
        (s := Finset.univ)
        (f := fun k : L.Gauge => probability k * (value k - mean) ^ 2)
        (fun k _hk => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))
        (Finset.mem_univ g)
    exact hTerm.trans hSingle
  · have hLeftLt :
        (value g - mean) ^ 2 < (value g - value h) ^ 2 / 4 :=
      lt_of_not_ge hLeft
    have hRight :
        (value g - value h) ^ 2 / 4 ≤ (value h - mean) ^ 2 := by
      nlinarith
    have hTerm :
        delta * ((value g - value h) ^ 2 / 4) ≤
          probability h * (value h - mean) ^ 2 := by
      calc
        delta * ((value g - value h) ^ 2 / 4) ≤
            probability h * ((value g - value h) ^ 2 / 4) :=
          mul_le_mul_of_nonneg_right hh
            (div_nonneg (sq_nonneg _) (by norm_num))
        _ ≤ probability h * (value h - mean) ^ 2 :=
          mul_le_mul_of_nonneg_left hRight ENNReal.toReal_nonneg
    have hSingle :
        probability h * (value h - mean) ^ 2 ≤
          ∑ k : L.Gauge, probability k * (value k - mean) ^ 2 := by
      exact Finset.single_le_sum
        (s := Finset.univ)
        (f := fun k : L.Gauge => probability k * (value k - mean) ^ 2)
        (fun k _hk => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _))
        (Finset.mem_univ h)
    exact hTerm.trans hSingle

/-- A pointwise lower bound on one-link conditional variance survives Gibbs
averaging. -/
theorem finite_oriented_lower_le_averagedSingleLinkVariance_of_pointwise
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (e : L.Edge)
    (c : ℝ)
    (hPointwise : ∀ A : L.Configuration,
      c ≤ L.singleLinkConditionalVariance f A e) :
    c ≤ L.averagedSingleLinkVariance f e := by
  classical
  have hMass :
      ∑ A : L.Configuration, L.gibbsProbabilityReal A = 1 := by
    simpa [FiniteOrientedLatticeWilsonSystem.gibbsProbabilityReal] using
      finite_oriented_pmf_sum_toReal_eq_one L.gibbsPMF
  unfold FiniteOrientedLatticeWilsonSystem.averagedSingleLinkVariance
  calc
    c = (∑ A : L.Configuration, L.gibbsProbabilityReal A) * c := by
      rw [hMass, one_mul]
    _ = ∑ A : L.Configuration, L.gibbsProbabilityReal A * c := by
      rw [Finset.sum_mul]
    _ ≤ ∑ A : L.Configuration,
        L.gibbsProbabilityReal A *
          L.singleLinkConditionalVariance f A e := by
      apply Finset.sum_le_sum
      intro A _hA
      exact mul_le_mul_of_nonneg_left (hPointwise A)
        (finite_oriented_gibbsProbabilityReal_nonneg L A)

/-- A pointwise one-link conditional-variance lower bound also bounds the full
finite-volume Gibbs variance from below. -/
theorem finite_oriented_lower_le_gibbsVarianceReal_of_conditional_pointwise
    (L : FiniteOrientedLatticeWilsonSystem)
    (f : L.Configuration → ℝ)
    (e : L.Edge)
    (c : ℝ)
    (hPointwise : ∀ A : L.Configuration,
      c ≤ L.singleLinkConditionalVariance f A e) :
    c ≤ L.gibbsVarianceReal f :=
  le_trans
    (finite_oriented_lower_le_averagedSingleLinkVariance_of_pointwise
      L f e c hPointwise)
    (finite_oriented_averagedSingleLinkVariance_le_gibbsVarianceReal L f e)

end

end MathlibAnalytic
end MGAP4D
