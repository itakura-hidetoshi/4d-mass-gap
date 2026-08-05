import MGAP4D.MathlibAnalytic.FinitePositiveWeightMultiplicativeFactorConditional
import Mathlib.Tactic

namespace MGAP4D
namespace MathlibAnalytic

open scoped BigOperators

noncomputable section

/-- A product weight assembled from independent one-coordinate factors. -/
def finiteProductCoordinatewiseFactor
    {ι G : Type}
    [Fintype ι]
    (factor : ι → G → ℝ)
    (A : ι → G) : ℝ :=
  ∏ coordinate : ι, factor coordinate (A coordinate)

/-- Every coordinatewise product factor has exact four-point cross ratio one.
The equality holds for arbitrary surrounding configurations: away from the
updated target, the two factors merely exchange order, while at the target
the inserted values pair identically. -/
theorem finiteProductCoordinatewiseFactor_singleSiteCrossRatio_one
    {ι G : Type}
    [DecidableEq ι]
    [Fintype ι]
    [Fintype G]
    (factor : ι → G → ℝ)
    (A B : ι → G)
    (target : ι) :
    FinitePositiveWeightSingleSiteCrossRatioBound
      (finiteProductCoordinatewiseFactor factor) A B target 1 := by
  classical
  intro g h
  unfold finiteProductCoordinatewiseFactor
  have hEq :
      (∏ coordinate : ι,
          factor coordinate ((Function.update A target g) coordinate)) *
        (∏ coordinate : ι,
          factor coordinate ((Function.update B target h) coordinate)) =
      (∏ coordinate : ι,
          factor coordinate ((Function.update B target g) coordinate)) *
        (∏ coordinate : ι,
          factor coordinate ((Function.update A target h) coordinate)) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro coordinate _hCoordinate
    by_cases hCoordinateTarget : coordinate = target
    · subst coordinate
      simp
    · simp [Function.update, hCoordinateTarget, mul_comm]
  simpa using hEq.le

end

end MathlibAnalytic
end MGAP4D
