import MGAP4D.MathlibAnalytic.ConcreteAnalyticSpineL2R2GraphPairEnergyPrefixBoundedQuadraticVertexCore

namespace MGAP4D
namespace MathlibAnalytic

open scoped ENNReal lp

noncomputable section

theorem concrete_l2_graph_pair_prefix_energy_bounded_cauchy_schwarz_of_quadratic_pos
    (N : ℕ) (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement)
    (hQx : 0 < concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x) :
    concreteL2GraphPairPrefixEnergyBoundedInnerProduct N x y ^ 2 ≤
      concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x *
        concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N y := by
  let Qx : ℝ := concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N x
  let Qy : ℝ := concreteL2GraphPairPrefixEnergyBoundedQuadraticFunctional N y
  let Ixy : ℝ := concreteL2GraphPairPrefixEnergyBoundedInnerProduct N x y
  have hQx' : 0 < Qx := by simpa [Qx] using hQx
  have hvn := concrete_l2_graph_pair_prefix_energy_bounded_quadratic_vertex_nonneg N x y
  have hve := concrete_l2_graph_pair_prefix_energy_bounded_quadratic_vertex_expansion N x y
  have hpoly :
      0 ≤ ((-Ixy / Qx) ^ 2) * Qx +
        (2 : ℝ) * ((-Ixy / Qx) * Ixy) + Qy := by
    rw [hve] at hvn
    simpa [concreteL2GraphPairPrefixEnergyBoundedQuadraticVertexCoeff,
      Qx, Qy, Ixy] using hvn
  have hpoly_simplified :
      ((-Ixy / Qx) ^ 2) * Qx +
          (2 : ℝ) * ((-Ixy / Qx) * Ixy) + Qy =
        Qy - Ixy ^ 2 / Qx := by
    field_simp [ne_of_gt hQx']
  have hnonneg : 0 ≤ Qy - Ixy ^ 2 / Qx := by
    rwa [hpoly_simplified] at hpoly
  have hmul_nonneg : 0 ≤ Qx * (Qy - Ixy ^ 2 / Qx) := by
    exact mul_nonneg hQx'.le hnonneg
  have hmul_simplified :
      Qx * (Qy - Ixy ^ 2 / Qx) = Qx * Qy - Ixy ^ 2 := by
    field_simp [ne_of_gt hQx']
    ring
  have hdiff_nonneg : 0 ≤ Qx * Qy - Ixy ^ 2 := by
    rwa [hmul_simplified] at hmul_nonneg
  have hmain : Ixy ^ 2 ≤ Qx * Qy := by
    nlinarith
  simpa [Qx, Qy, Ixy] using hmain

end

end MathlibAnalytic
end MGAP4D
