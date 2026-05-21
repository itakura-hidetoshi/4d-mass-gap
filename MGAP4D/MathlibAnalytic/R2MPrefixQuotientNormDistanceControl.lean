import MGAP4D.MathlibAnalytic.R2MPrefixQuotientReverseTriangle

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- One-sided reverse triangle inequality: the norm difference is controlled by
quotient subtraction. -/
theorem r2m_prefix_quotient_norm_sub_norm_le_norm_sub_typeclass
    (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N) :
    ‖q‖ - ‖r‖ ≤ ‖q - r‖ := by
  exact le_trans (le_abs_self (‖q‖ - ‖r‖))
    (r2m_prefix_quotient_abs_norm_sub_le_norm_sub_typeclass N q r)

/-- One-sided reverse triangle inequality in installed distance notation. -/
theorem r2m_prefix_quotient_norm_sub_norm_le_dist_typeclass
    (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N) :
    ‖q‖ - ‖r‖ ≤ dist q r := by
  exact le_trans (le_abs_self (‖q‖ - ‖r‖))
    (r2m_prefix_quotient_abs_norm_sub_le_dist_typeclass N q r)

/-- A norm is bounded above by the reference norm plus quotient subtraction. -/
theorem r2m_prefix_quotient_norm_le_norm_add_norm_sub_typeclass
    (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N) :
    ‖q‖ ≤ ‖r‖ + ‖q - r‖ := by
  have h := r2m_prefix_quotient_norm_sub_norm_le_norm_sub_typeclass N q r
  linarith

/-- A norm is bounded above by the reference norm plus quotient distance. -/
theorem r2m_prefix_quotient_norm_le_norm_add_dist_typeclass
    (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N) :
    ‖q‖ ≤ ‖r‖ + dist q r := by
  have h := r2m_prefix_quotient_norm_sub_norm_le_dist_typeclass N q r
  linarith

/-- A lower bound version of norm control by distance. -/
theorem r2m_prefix_quotient_norm_sub_dist_le_norm_typeclass
    (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N) :
    ‖r‖ - dist q r ≤ ‖q‖ := by
  have h := r2m_prefix_quotient_norm_sub_norm_le_dist_typeclass N r q
  rw [r2m_prefix_quotient_dist_comm_typeclass N r q] at h
  linarith

/-- Symmetric upper control by distance. -/
theorem r2m_prefix_quotient_norm_symm_le_norm_add_dist_typeclass
    (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N) :
    ‖r‖ ≤ ‖q‖ + dist q r := by
  have h := r2m_prefix_quotient_norm_sub_norm_le_dist_typeclass N r q
  rw [r2m_prefix_quotient_dist_comm_typeclass N r q] at h
  linarith

/-- Distance-control surface for the quotient norm.  This packages the
1-Lipschitz behavior of the norm map in theorem-surface form, without yet
installing a full `MetricSpace` instance. -/
def r2mPrefixQuotientNormDistanceControlReady : Prop :=
  r2mPrefixQuotientReverseTriangleReady ∧
  (∀ (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N),
    ‖q‖ - ‖r‖ ≤ ‖q - r‖) ∧
  (∀ (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N),
    ‖q‖ - ‖r‖ ≤ dist q r) ∧
  (∀ (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N),
    ‖q‖ ≤ ‖r‖ + ‖q - r‖) ∧
  (∀ (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N),
    ‖q‖ ≤ ‖r‖ + dist q r) ∧
  (∀ (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N),
    ‖r‖ - dist q r ≤ ‖q‖) ∧
  (∀ (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N),
    ‖r‖ ≤ ‖q‖ + dist q r)

/-- The quotient norm-distance control surface is ready. -/
theorem r2m_prefix_quotient_norm_distance_control_ready :
    r2mPrefixQuotientNormDistanceControlReady := by
  exact ⟨
    r2m_prefix_quotient_reverse_triangle_ready,
    r2m_prefix_quotient_norm_sub_norm_le_norm_sub_typeclass,
    r2m_prefix_quotient_norm_sub_norm_le_dist_typeclass,
    r2m_prefix_quotient_norm_le_norm_add_norm_sub_typeclass,
    r2m_prefix_quotient_norm_le_norm_add_dist_typeclass,
    r2m_prefix_quotient_norm_sub_dist_le_norm_typeclass,
    r2m_prefix_quotient_norm_symm_le_norm_add_dist_typeclass⟩

/-- Boundary marker: quotient norm variation is controlled by quotient distance. -/
def r2mPrefixQuotientNormDistanceControlBoundaryHeld : Prop :=
  r2mPrefixQuotientNormDistanceControlReady ∧
  True

theorem r2m_prefix_quotient_norm_distance_control_boundary_held :
    r2mPrefixQuotientNormDistanceControlBoundaryHeld := by
  exact ⟨r2m_prefix_quotient_norm_distance_control_ready, trivial⟩

end

end MathlibAnalytic
end MGAP4D
