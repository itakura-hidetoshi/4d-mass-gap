import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedInnerProduct
import MGAP4D.MathlibAnalytic.R2MPrefixDegenerateCoordinates

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

/-- If the finite-prefix quadratic functional of the left argument vanishes,
then the finite-prefix inner product with any right argument vanishes. -/
theorem r2m_prefix_inner_zero_left_of_quadratic_zero
    (N : ℕ)
    (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement)
    (hx : concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x = 0) :
    concreteL2GraphPairPrefixEnergyBoundedInnerProduct N x y = 0 := by
  unfold concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional at hx
  unfold concreteL2GraphPairPrefixEnergyBoundedInnerProduct
  exact Finset.sum_eq_zero fun n hn => by
    have hcoord := r2m_prefix_zero_coordinates N x.1 hx n hn
    rcases hcoord with ⟨hfst, hsnd⟩
    simp [hfst, hsnd]

/-- If the finite-prefix quadratic functional of the right argument vanishes,
then the finite-prefix inner product with any left argument vanishes. -/
theorem r2m_prefix_inner_zero_right_of_quadratic_zero
    (N : ℕ)
    (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement)
    (hy : concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N y = 0) :
    concreteL2GraphPairPrefixEnergyBoundedInnerProduct N x y = 0 := by
  rw [concrete_l2_graph_pair_prefix_energy_bounded_inner_symm N x y]
  exact r2m_prefix_inner_zero_left_of_quadratic_zero N y x hy

end

end MathlibAnalytic
end MGAP4D
