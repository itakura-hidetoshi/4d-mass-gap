import MGAP4D.MathlibAnalytic.R2MPrefixQuotientDistance
import MGAP4D.MathlibAnalytic.R2MPrefixQuotientSubLaws

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Concrete bridge: the finite-prefix pseudo-distance from `x` to `y` is the
finite-prefix pseudo-distance of the concrete difference `x-y` from zero. -/
theorem r2m_prefix_pseudo_distance_eq_sub_zero_distance
    (N : ℕ)
    (x y : ConcreteL2GraphPairPrefixEnergyBoundedElement) :
    r2mPrefixPseudoDistance N x y =
      r2mPrefixPseudoDistance N
        (concreteL2GraphPairPrefixEnergyBoundedSub x y)
        concreteL2GraphPairPrefixEnergyBoundedZero := by
  unfold r2mPrefixPseudoDistance
  rw [concrete_l2_graph_pair_prefix_energy_bounded_sub_zero_eq]

/-- Quotient bridge: the quotient distance is exactly the quotient seminorm of
the quotient subtraction.  This is the metric-style `dist q r = ‖q-r‖` surface
before installing Mathlib typeclass instances. -/
theorem r2m_prefix_quotient_distance_eq_seminorm_sub
    (N : ℕ)
    (q r : R2MPrefixZeroDistanceQuotient N) :
    r2mPrefixQuotientDistance N q r =
      r2mPrefixQuotientSeminorm N (r2mPrefixQuotientSub N q r) := by
  refine Quotient.inductionOn' q ?_
  intro x
  refine Quotient.inductionOn' r ?_
  intro y
  rw [r2m_prefix_quotient_distance_mk]
  rw [r2m_prefix_quotient_sub_mk]
  rw [r2m_prefix_quotient_seminorm_mk]
  exact r2m_prefix_pseudo_distance_eq_sub_zero_distance N x y

/-- Readiness package for the distance/subtraction/seminorm bridge. -/
def r2mPrefixQuotientDistanceSubBridgeReady : Prop :=
  r2mPrefixQuotientDistanceReady ∧
  r2mPrefixQuotientSubLawsReady ∧
  (∀ (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientDistance N q r =
      r2mPrefixQuotientSeminorm N (r2mPrefixQuotientSub N q r))

/-- The quotient distance/subtraction/seminorm bridge is ready. -/
theorem r2m_prefix_quotient_distance_sub_bridge_ready :
    r2mPrefixQuotientDistanceSubBridgeReady := by
  exact ⟨
    r2m_prefix_quotient_distance_ready,
    r2m_prefix_quotient_sub_laws_ready,
    r2m_prefix_quotient_distance_eq_seminorm_sub⟩

/-- Boundary marker: the finite-prefix quotient now has the canonical
`distance = seminorm of subtraction` bridge, while Mathlib typeclass promotion
remains deliberately deferred. -/
def r2mPrefixQuotientNormedGroupBoundaryHeld : Prop :=
  r2mPrefixQuotientDistanceSubBridgeReady ∧
  True

theorem r2m_prefix_quotient_normed_group_boundary_held :
    r2mPrefixQuotientNormedGroupBoundaryHeld := by
  exact ⟨r2m_prefix_quotient_distance_sub_bridge_ready, trivial⟩

end

end MathlibAnalytic
end MGAP4D
