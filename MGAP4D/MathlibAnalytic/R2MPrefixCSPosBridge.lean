import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2GraphPairEnergyPrefixRealAlgebra
import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedQuadraticVertexCore

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

theorem r2m_prefix_cs_pos
    (N : ℕ) (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement)
    (hx : 0 < concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x) :
    concreteL2GraphPairPrefixEnergyBoundedInnerProduct N x y ^ 2 ≤
      concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x *
        concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N y := by
  apply real_sq_le_mul_of_vertex_quadratic_nonneg
  · simpa using hx
  · have h0 := concrete_l2_graph_pair_prefix_energy_bounded_quadratic_vertex_nonneg N x y
    have h1 := concrete_l2_graph_pair_prefix_energy_bounded_quadratic_vertex_expansion N x y
    rw [h1] at h0
    simpa [concreteL2GraphPairPrefixEnergyBoundedQuadraticVertexCoeff] using h0

end

end MathlibAnalytic
end MGAP4D
