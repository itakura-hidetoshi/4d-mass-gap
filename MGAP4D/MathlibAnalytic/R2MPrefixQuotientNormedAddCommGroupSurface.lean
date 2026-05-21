import MGAP4D.MathlibAnalytic.R2MPrefixQuotientSubSeminormMetricAPI

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Mathlib-style naming alias: the quotient distance is the seminorm of the
quotient subtraction.  This is the pre-typeclass `dist_eq_norm_sub` surface. -/
theorem r2m_prefix_quotient_dist_eq_norm_sub
    (N : ℕ)
    (q r : R2MPrefixZeroDistanceQuotient N) :
    r2mPrefixQuotientDistance N q r =
      r2mPrefixQuotientSeminorm N (r2mPrefixQuotientSub N q r) := by
  exact r2m_prefix_quotient_distance_eq_seminorm_sub N q r

/-- Mathlib-style naming alias: the norm-like seminorm of a quotient difference
is symmetric. -/
theorem r2m_prefix_quotient_norm_sub_comm
    (N : ℕ)
    (q r : R2MPrefixZeroDistanceQuotient N) :
    r2mPrefixQuotientSeminorm N (r2mPrefixQuotientSub N q r) =
      r2mPrefixQuotientSeminorm N (r2mPrefixQuotientSub N r q) := by
  exact r2m_prefix_quotient_seminorm_sub_symm N q r

/-- Mathlib-style naming alias: triangle inequality in norm-of-subtraction
form. -/
theorem r2m_prefix_quotient_norm_sub_triangle
    (N : ℕ)
    (q r s : R2MPrefixZeroDistanceQuotient N) :
    r2mPrefixQuotientSeminorm N (r2mPrefixQuotientSub N q s) ≤
      r2mPrefixQuotientSeminorm N (r2mPrefixQuotientSub N q r) +
        r2mPrefixQuotientSeminorm N (r2mPrefixQuotientSub N r s) := by
  exact r2m_prefix_quotient_seminorm_sub_triangle N q r s

/-- Pre-typeclass surface for the finite-prefix quotient: additive commutative
group laws, separated metric laws, and the canonical `dist = norm(sub)` bridge
are all available as explicit theorems before installing Mathlib instances. -/
def r2mPrefixQuotientNormedAddCommGroupSurfaceReady : Prop :=
  r2mPrefixQuotientSubSeminormMetricAPIReady ∧
  (∀ (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientAdd N (r2mPrefixQuotientZeroClass N) q = q) ∧
  (∀ (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientAdd N q (r2mPrefixQuotientZeroClass N) = q) ∧
  (∀ (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientAdd N q r = r2mPrefixQuotientAdd N r q) ∧
  (∀ (N : ℕ) (q r s : R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientAdd N (r2mPrefixQuotientAdd N q r) s =
      r2mPrefixQuotientAdd N q (r2mPrefixQuotientAdd N r s)) ∧
  (∀ (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientAdd N q (r2mPrefixQuotientNeg N q) =
      r2mPrefixQuotientZeroClass N) ∧
  (∀ (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientDistance N q r =
      r2mPrefixQuotientSeminorm N (r2mPrefixQuotientSub N q r)) ∧
  (∀ (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientSeminorm N (r2mPrefixQuotientSub N q r) =
      r2mPrefixQuotientSeminorm N (r2mPrefixQuotientSub N r q)) ∧
  (∀ (N : ℕ) (q r s : R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientSeminorm N (r2mPrefixQuotientSub N q s) ≤
      r2mPrefixQuotientSeminorm N (r2mPrefixQuotientSub N q r) +
        r2mPrefixQuotientSeminorm N (r2mPrefixQuotientSub N r s))

/-- The finite-prefix quotient normed-additive-commutative-group surface is
ready, without yet claiming a Mathlib typeclass instance. -/
theorem r2m_prefix_quotient_normed_add_comm_group_surface_ready :
    r2mPrefixQuotientNormedAddCommGroupSurfaceReady := by
  exact ⟨
    r2m_prefix_quotient_sub_seminorm_metric_api_ready,
    r2m_prefix_quotient_zero_add,
    r2m_prefix_quotient_add_zero,
    r2m_prefix_quotient_add_comm,
    r2m_prefix_quotient_add_assoc,
    r2m_prefix_quotient_add_neg,
    r2m_prefix_quotient_dist_eq_norm_sub,
    r2m_prefix_quotient_norm_sub_comm,
    r2m_prefix_quotient_norm_sub_triangle⟩

/-- Boundary marker: the quotient has the explicit theorem surface expected of
a separated normed additive commutative group, while actual instance promotion
is deliberately left to a later layer. -/
def r2mPrefixQuotientNormedAddCommGroupInstanceBoundaryHeld : Prop :=
  r2mPrefixQuotientNormedAddCommGroupSurfaceReady ∧
  True

theorem r2m_prefix_quotient_normed_add_comm_group_instance_boundary_held :
    r2mPrefixQuotientNormedAddCommGroupInstanceBoundaryHeld := by
  exact ⟨r2m_prefix_quotient_normed_add_comm_group_surface_ready, trivial⟩

end

end MathlibAnalytic
end MGAP4D
