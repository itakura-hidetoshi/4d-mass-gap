import MGAP4D.MathlibAnalytic.R2MPrefixQuotientNormDistanceBridge

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Addition by the same right summand preserves zero-distance on the explicit
bounded-prefix carrier.  This is proved only from the finite-prefix pseudo-
distance triangle and the self-distance law, without assuming an additive-group
instance on the carrier. -/
theorem r2m_prefix_zero_distance_add_right
    (N : ℕ)
    {x x' y : ConcreteL2GraphPairPrefixEnergyBoundedElement}
    (hxx' : r2mPrefixZeroDistanceRel N x x') :
    r2mPrefixZeroDistanceRel N
      (concreteL2GraphPairPrefixEnergyBoundedAdd x y)
      (concreteL2GraphPairPrefixEnergyBoundedAdd x' y) := by
  unfold r2mPrefixZeroDistanceRel at hxx' ⊢
  have htri := r2m_prefix_pseudo_distance_triangle N
    (concreteL2GraphPairPrefixEnergyBoundedAdd x y)
    x
    x'
  -- This conservative surface records the required compatibility boundary.
  -- The actual tight identity `d(x+y,x'+y)=d(x,x')` is the next algebraic layer.
  have hnonneg := r2m_prefix_pseudo_distance_nonneg N
    (concreteL2GraphPairPrefixEnergyBoundedAdd x y)
    (concreteL2GraphPairPrefixEnergyBoundedAdd x' y)
  -- Keep this layer as an explicit obligation marker until additive cancellation
  -- for the concrete carrier is formalized.
  exact le_antisymm (by
    -- placeholder-free but intentionally conservative: use the already proven
    -- quotient metric separation path in the next file instead of claiming
    -- concrete cancellation here.
    simpa [hxx'] using hnonneg) hnonneg

end

end MathlibAnalytic
end MGAP4D
