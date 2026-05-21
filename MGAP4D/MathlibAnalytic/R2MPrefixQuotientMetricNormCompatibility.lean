import MGAP4D.MathlibAnalytic.R2MPrefixQuotientMetricSpaceCandidate

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The installed quotient norm is the installed quotient distance to zero. -/
theorem r2m_prefix_quotient_norm_eq_dist_zero_typeclass
    (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N) :
    ‖q‖ = dist q 0 := by
  rw [r2m_prefix_quotient_norm_typeclass_def]
  rw [r2m_prefix_quotient_dist_typeclass_def]
  rw [r2m_prefix_quotient_add_comm_group_zero_def]
  exact r2m_prefix_quotient_seminorm_eq_distance_zero_class N q

/-- The installed quotient distance to zero is the installed quotient norm. -/
theorem r2m_prefix_quotient_dist_zero_eq_norm_typeclass
    (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N) :
    dist q 0 = ‖q‖ := by
  exact (r2m_prefix_quotient_norm_eq_dist_zero_typeclass N q).symm

/-- The installed quotient distance from zero is also the installed quotient
norm, by symmetry of the quotient distance. -/
theorem r2m_prefix_quotient_dist_zero_left_eq_norm_typeclass
    (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N) :
    dist 0 q = ‖q‖ := by
  calc
    dist 0 q = dist q 0 := r2m_prefix_quotient_dist_comm_typeclass N 0 q
    _ = ‖q‖ := r2m_prefix_quotient_dist_zero_eq_norm_typeclass N q

/-- The installed quotient norm is zero at zero. -/
theorem r2m_prefix_quotient_norm_zero_typeclass
    (N : ℕ) :
    ‖(0 : R2MPrefixZeroDistanceQuotient N)‖ = 0 := by
  exact (r2m_prefix_quotient_norm_eq_zero_iff N
    (0 : R2MPrefixZeroDistanceQuotient N)).mpr rfl

/-- The installed quotient norm is positive exactly away from zero. -/
theorem r2m_prefix_quotient_norm_pos_iff_ne_zero_typeclass
    (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N) :
    0 < ‖q‖ ↔ q ≠ 0 := by
  rw [r2m_prefix_quotient_norm_typeclass_def]
  rw [r2m_prefix_quotient_add_comm_group_zero_def]
  exact r2m_prefix_quotient_seminorm_pos_iff_ne_zero_class N q

/-- If a quotient point is nonzero, its installed quotient norm is positive. -/
theorem r2m_prefix_quotient_norm_pos_of_ne_zero_typeclass
    (N : ℕ) {q : R2MPrefixZeroDistanceQuotient N}
    (hq : q ≠ 0) :
    0 < ‖q‖ := by
  exact (r2m_prefix_quotient_norm_pos_iff_ne_zero_typeclass N q).mpr hq

/-- If the installed quotient norm is positive, the quotient point is nonzero. -/
theorem r2m_prefix_quotient_ne_zero_of_norm_pos_typeclass
    (N : ℕ) {q : R2MPrefixZeroDistanceQuotient N}
    (hq : 0 < ‖q‖) :
    q ≠ 0 := by
  exact (r2m_prefix_quotient_norm_pos_iff_ne_zero_typeclass N q).mp hq

/-- Metric/norm compatibility surface in mathlib notation.  This collects the
standard identities expected before promoting the quotient to a full normed
metric hierarchy. -/
def r2mPrefixQuotientMetricNormCompatibilityReady : Prop :=
  r2mPrefixQuotientMetricSpaceCandidateReady ∧
  (∀ (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N),
    ‖q‖ = dist q 0) ∧
  (∀ (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N),
    dist q 0 = ‖q‖) ∧
  (∀ (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N),
    dist 0 q = ‖q‖) ∧
  (∀ (N : ℕ),
    ‖(0 : R2MPrefixZeroDistanceQuotient N)‖ = 0) ∧
  (∀ (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N),
    0 < ‖q‖ ↔ q ≠ 0)

/-- The quotient metric/norm compatibility surface is ready. -/
theorem r2m_prefix_quotient_metric_norm_compatibility_ready :
    r2mPrefixQuotientMetricNormCompatibilityReady := by
  exact ⟨
    r2m_prefix_quotient_metric_space_candidate_ready,
    r2m_prefix_quotient_norm_eq_dist_zero_typeclass,
    r2m_prefix_quotient_dist_zero_eq_norm_typeclass,
    r2m_prefix_quotient_dist_zero_left_eq_norm_typeclass,
    r2m_prefix_quotient_norm_zero_typeclass,
    r2m_prefix_quotient_norm_pos_iff_ne_zero_typeclass⟩

/-- Boundary marker: quotient norm and quotient metric are compatible in
standard mathlib notation. -/
def r2mPrefixQuotientMetricNormCompatibilityBoundaryHeld : Prop :=
  r2mPrefixQuotientMetricNormCompatibilityReady ∧
  True

theorem r2m_prefix_quotient_metric_norm_compatibility_boundary_held :
    r2mPrefixQuotientMetricNormCompatibilityBoundaryHeld := by
  exact ⟨r2m_prefix_quotient_metric_norm_compatibility_ready, trivial⟩

end

end MathlibAnalytic
end MGAP4D
