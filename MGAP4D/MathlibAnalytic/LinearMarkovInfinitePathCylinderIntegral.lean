import MGAP4D.MathlibAnalytic.LinearMarkovInfinitePathMeasure
import MGAP4D.MathlibAnalytic.LinearMarkovFinitePathCylinderMoment
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- The finite product cylinder on an infinite natural-time path. -/
def linearMarkovInfinitePathProduct
    {Ω : Type*}
    {n : ℕ}
    (fs : Fin (n + 1) → Ω → ℝ)
    (path : ℕ → Ω) : ℝ :=
  ∏ i : Fin (n + 1), fs i (path i.1)

/-- The infinite-path product cylinder factors exactly through the corresponding
finite tuple prefix. -/
theorem linearMarkovInfinitePathProduct_eq_comp_finPrefix
    {Ω : Type*}
    (n : ℕ)
    (fs : Fin (n + 1) → Ω → ℝ) :
    linearMarkovInfinitePathProduct fs =
      linearMarkovFinitePathProduct fs ∘
        linearMarkovInfinitePathFinPrefix n := by
  funext path
  rfl

/-- Every finite product cylinder on a finite tuple is strongly measurable on a
finite discrete state space. -/
theorem stronglyMeasurable_linearMarkovFinitePathProduct
    {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
    (n : ℕ)
    (fs : Fin (n + 1) → Ω → ℝ) :
    StronglyMeasurable (linearMarkovFinitePathProduct fs) :=
  (measurable_of_finite _).stronglyMeasurable

/-- Integration of a finite product cylinder against the infinite Markov path
measure is exactly the pre-existing backward cylinder moment. -/
theorem linearMarkovInfinitePathMeasure_cylinder_integral
    {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] [DiscreteMeasurableSpace Ω]
    (initial : PMF Ω)
    (transition : Ω → PMF Ω)
    (n : ℕ)
    (fs : Fin (n + 1) → Ω → ℝ) :
    (∫ path,
        linearMarkovInfinitePathProduct fs path
      ∂linearMarkovInfinitePathMeasure initial transition) =
      linearMarkovCylinderMoment
        (finitePMFExpectationReal initial)
        (finitePMFTransitionExpectationLinearMap transition)
        (List.ofFn fs) := by
  have hPrefixMeasurable :
      Measurable (linearMarkovInfinitePathFinPrefix (Ω := Ω) n) :=
    measurable_linearMarkovInfinitePathFinPrefix n
  have hProductStronglyMeasurable :
      StronglyMeasurable (linearMarkovFinitePathProduct fs) :=
    stronglyMeasurable_linearMarkovFinitePathProduct n fs
  calc
    (∫ path,
        linearMarkovInfinitePathProduct fs path
      ∂linearMarkovInfinitePathMeasure initial transition) =
      ∫ finitePath,
        linearMarkovFinitePathProduct fs finitePath
      ∂(linearMarkovInfinitePathMeasure initial transition).map
        (linearMarkovInfinitePathFinPrefix n) := by
          rw [linearMarkovInfinitePathProduct_eq_comp_finPrefix]
          symm
          exact MeasureTheory.integral_map_of_stronglyMeasurable
            hPrefixMeasurable hProductStronglyMeasurable
    _ = ∫ finitePath,
        linearMarkovFinitePathProduct fs finitePath
      ∂(linearMarkovFinitePathPMF initial transition n).toMeasure := by
          rw [linearMarkovInfinitePathMeasure_map_finPrefix]
    _ = finitePMFExpectationReal
        (linearMarkovFinitePathPMF initial transition n)
        (linearMarkovFinitePathProduct fs) := by
          rw [PMF.integral_eq_sum]
          rfl
    _ = linearMarkovCylinderMoment
        (finitePMFExpectationReal initial)
        (finitePMFTransitionExpectationLinearMap transition)
        (List.ofFn fs) :=
      linearMarkovFinitePathPMF_product_expectation_eq_cylinderMoment
        initial transition n fs

end

end MathlibAnalytic
end MGAP4D
