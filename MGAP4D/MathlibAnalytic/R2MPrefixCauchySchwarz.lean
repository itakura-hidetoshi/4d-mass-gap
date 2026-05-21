import MGAP4D.MathlibAnalytic.R2MPrefixCSPosBridge
import MGAP4D.MathlibAnalytic.R2MPrefixDegenerateInner

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Finite-prefix Cauchy--Schwarz inequality for the concrete bounded graph-pair
energy surface.  The proof splits the positive quadratic case from the
degenerate quadratic case; the former is delegated to the quadratic-vertex
argument and the latter to the finite nonnegative-sum degeneracy kernels. -/
theorem r2m_prefix_cauchy_schwarz
    (N : ℕ) (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    concreteL2GraphPairPrefixEnergyBoundedInnerProduct N x y ^ 2 ≤
      concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x *
        concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N y := by
  have hx_nonneg :
      0 ≤ concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x :=
    concrete_l2_graph_pair_prefix_energy_bounded_quadratic_nonneg N x
  by_cases hx_zero :
      concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x = 0
  · have hinner_zero :=
      r2m_prefix_inner_zero_left_of_quadratic_zero N x y hx_zero
    simp [hinner_zero, hx_zero]
  · have hx_pos :
      0 < concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x := by
      exact lt_of_le_of_ne hx_nonneg (fun h => hx_zero h.symm)
    exact r2m_prefix_cs_pos N x y hx_pos

end

end MathlibAnalytic
end MGAP4D
