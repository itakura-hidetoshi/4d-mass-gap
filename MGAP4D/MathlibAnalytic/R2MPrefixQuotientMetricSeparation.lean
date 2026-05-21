import MGAP4D.MathlibAnalytic.R2MPrefixQuotientDistance

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- If the quotient distance between two representative classes is zero, then
their representatives are zero-distance related and hence the quotient classes
are equal. -/
theorem r2m_prefix_quotient_mk_eq_of_distance_zero
    (N : ℕ)
    (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement)
    (hxy : r2mPrefixQuotientDistance N
        (Quotient.mk (r2mPrefixZeroDistanceSetoid N) x)
        (Quotient.mk (r2mPrefixZeroDistanceSetoid N) y) = 0) :
    Quotient.mk (r2mPrefixZeroDistanceSetoid N) x =
      Quotient.mk (r2mPrefixZeroDistanceSetoid N) y := by
  rw [r2m_prefix_quotient_distance_mk] at hxy
  apply Quotient.sound
  change r2mPrefixPseudoDistance N x y = 0
  exact hxy

/-- Metric-style separation on the quotient: quotient distance is zero iff the
quotient classes are equal. -/
theorem r2m_prefix_quotient_distance_eq_zero_iff
    (N : ℕ)
    (q r : R2MPrefixZeroDistanceQuotient N) :
    r2mPrefixQuotientDistance N q r = 0 ↔ q = r := by
  refine Quotient.inductionOn' q ?_
  intro x
  refine Quotient.inductionOn' r ?_
  intro y
  constructor
  · intro hxy
    exact r2m_prefix_quotient_mk_eq_of_distance_zero N x y hxy
  · intro hxy
    rw [hxy]
    exact r2m_prefix_quotient_distance_self N
      (Quotient.mk (r2mPrefixZeroDistanceSetoid N) y)

/-- The quotient distance surface is separated: after quotienting by the
zero-distance relation, zero distance is equality. -/
def r2mPrefixQuotientMetricSeparationReady : Prop :=
  r2mPrefixQuotientDistanceReady ∧
  (∀ (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientDistance N q r = 0 ↔ q = r)

/-- The quotient metric-separation surface is ready. -/
theorem r2m_prefix_quotient_metric_separation_ready :
    r2mPrefixQuotientMetricSeparationReady := by
  exact ⟨
    r2m_prefix_quotient_distance_ready,
    r2m_prefix_quotient_distance_eq_zero_iff⟩

/-- Boundary marker: the quotient distance now has metric-style separation,
while Mathlib `MetricSpace`/normed typeclass promotion remains a later layer. -/
def r2mPrefixMetricSpacePromotionBoundaryHeld : Prop :=
  r2mPrefixQuotientMetricSeparationReady ∧
  True

theorem r2m_prefix_metric_space_promotion_boundary_held :
    r2mPrefixMetricSpacePromotionBoundaryHeld := by
  exact ⟨r2m_prefix_quotient_metric_separation_ready, trivial⟩

end

end MathlibAnalytic
end MGAP4D
