import MGAP4D.MathlibAnalytic.R2MPrefixQuotientNormDistTypeclass

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Nonnegativity of the installed quotient distance. -/
theorem r2m_prefix_quotient_dist_nonneg_typeclass
    (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N) :
    0 ≤ dist q r := by
  rw [r2m_prefix_quotient_dist_typeclass_def]
  exact r2m_prefix_quotient_distance_nonneg N q r

/-- The installed quotient distance vanishes exactly on equality, in the
`dist_eq_zero` direction used by Mathlib metric-space constructors. -/
theorem r2m_prefix_quotient_eq_of_dist_eq_zero_typeclass
    (N : ℕ) {q r : R2MPrefixZeroDistanceQuotient N}
    (h : dist q r = 0) :
    q = r := by
  exact (r2m_prefix_quotient_dist_eq_zero_iff_typeclass N q r).mp h

/-- Equality implies zero installed quotient distance. -/
theorem r2m_prefix_quotient_dist_eq_zero_of_eq_typeclass
    (N : ℕ) {q r : R2MPrefixZeroDistanceQuotient N}
    (h : q = r) :
    dist q r = 0 := by
  exact (r2m_prefix_quotient_dist_eq_zero_iff_typeclass N q r).mpr h

/-- Strict positivity of the installed quotient distance away from equality. -/
theorem r2m_prefix_quotient_dist_pos_iff_ne_typeclass
    (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N) :
    0 < dist q r ↔ q ≠ r := by
  rw [r2m_prefix_quotient_dist_typeclass_def]
  exact r2m_prefix_quotient_distance_pos_iff_ne N q r

/-- If two quotient points are distinct, their installed quotient distance is
strictly positive. -/
theorem r2m_prefix_quotient_dist_pos_of_ne_typeclass
    (N : ℕ) {q r : R2MPrefixZeroDistanceQuotient N}
    (h : q ≠ r) :
    0 < dist q r := by
  exact (r2m_prefix_quotient_dist_pos_iff_ne_typeclass N q r).mpr h

/-- If the installed quotient distance is positive, the two quotient points are
distinct. -/
theorem r2m_prefix_quotient_ne_of_dist_pos_typeclass
    (N : ℕ) {q r : R2MPrefixZeroDistanceQuotient N}
    (h : 0 < dist q r) :
    q ≠ r := by
  exact (r2m_prefix_quotient_dist_pos_iff_ne_typeclass N q r).mp h

/-- Mathlib metric-space candidate surface: all metric laws are now available
in installed `dist` notation, while the actual `MetricSpace` promotion is kept
as an explicit later boundary. -/
def r2mPrefixQuotientMetricSpaceCandidateReady : Prop :=
  r2mPrefixQuotientNormDistTypeclassReady ∧
  (∀ (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N),
    0 ≤ dist q r) ∧
  (∀ (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N),
    dist q q = 0) ∧
  (∀ (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N),
    dist q r = dist r q) ∧
  (∀ (N : ℕ) (q r s : R2MPrefixZeroDistanceQuotient N),
    dist q s ≤ dist q r + dist r s) ∧
  (∀ (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N),
    dist q r = 0 ↔ q = r) ∧
  (∀ (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N),
    0 < dist q r ↔ q ≠ r) ∧
  (∀ (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N),
    dist q r = ‖q - r‖)

/-- The quotient metric-space candidate surface is ready. -/
theorem r2m_prefix_quotient_metric_space_candidate_ready :
    r2mPrefixQuotientMetricSpaceCandidateReady := by
  exact ⟨
    r2m_prefix_quotient_norm_dist_typeclass_ready,
    r2m_prefix_quotient_dist_nonneg_typeclass,
    r2m_prefix_quotient_dist_self_typeclass,
    r2m_prefix_quotient_dist_comm_typeclass,
    r2m_prefix_quotient_dist_triangle_typeclass,
    r2m_prefix_quotient_dist_eq_zero_iff_typeclass,
    r2m_prefix_quotient_dist_pos_iff_ne_typeclass,
    r2m_prefix_quotient_dist_eq_norm_sub_typeclass⟩

/-- Boundary marker: the finite-prefix quotient has the full metric theorem
surface in mathlib notation; actual instance installation remains separate. -/
def r2mPrefixQuotientMetricSpaceCandidateBoundaryHeld : Prop :=
  r2mPrefixQuotientMetricSpaceCandidateReady ∧
  True

theorem r2m_prefix_quotient_metric_space_candidate_boundary_held :
    r2mPrefixQuotientMetricSpaceCandidateBoundaryHeld := by
  exact ⟨r2m_prefix_quotient_metric_space_candidate_ready, trivial⟩

end

end MathlibAnalytic
end MGAP4D
