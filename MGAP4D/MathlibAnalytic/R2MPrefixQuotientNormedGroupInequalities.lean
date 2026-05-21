import MGAP4D.MathlibAnalytic.R2MPrefixQuotientMetricNormCompatibility

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Triangle inequality for the installed quotient norm.  This is the
mathlib-notation form of the concrete finite-prefix Minkowski inequality after
transport to the zero-distance quotient. -/
theorem r2m_prefix_quotient_norm_add_le_typeclass
    (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N) :
    ‖q + r‖ ≤ ‖q‖ + ‖r‖ := by
  refine Quotient.inductionOn' q ?_
  intro x
  refine Quotient.inductionOn' r ?_
  intro y
  rw [r2m_prefix_quotient_add_comm_group_add_def]
  rw [r2m_prefix_quotient_add_mk]
  repeat rw [r2m_prefix_quotient_norm_typeclass_def]
  repeat rw [r2m_prefix_quotient_seminorm_mk]
  exact r2m_prefix_triangle_inequality N x y

/-- The installed quotient norm is invariant under negation. -/
theorem r2m_prefix_quotient_norm_neg_typeclass
    (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N) :
    ‖-q‖ = ‖q‖ := by
  rw [r2m_prefix_quotient_add_comm_group_neg_def]
  unfold r2mPrefixQuotientNeg
  rw [← r2m_prefix_quotient_module_smul_def N (-1 : ℝ) q]
  rw [r2m_prefix_quotient_norm_smul_typeclass]
  simp

/-- The installed quotient norm is invariant under reversing subtraction. -/
theorem r2m_prefix_quotient_norm_sub_rev_typeclass
    (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N) :
    ‖q - r‖ = ‖r - q‖ := by
  calc
    ‖q - r‖ = dist q r := by
      exact (r2m_prefix_quotient_dist_eq_norm_sub_typeclass N q r).symm
    _ = dist r q := r2m_prefix_quotient_dist_comm_typeclass N q r
    _ = ‖r - q‖ := r2m_prefix_quotient_dist_eq_norm_sub_typeclass N r q

/-- A standard subtraction estimate for the installed quotient norm. -/
theorem r2m_prefix_quotient_norm_sub_le_typeclass
    (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N) :
    ‖q - r‖ ≤ ‖q‖ + ‖r‖ := by
  calc
    ‖q - r‖ = ‖q + (-r)‖ := by
      rw [sub_eq_add_neg]
    _ ≤ ‖q‖ + ‖-r‖ :=
      r2m_prefix_quotient_norm_add_le_typeclass N q (-r)
    _ = ‖q‖ + ‖r‖ := by
      rw [r2m_prefix_quotient_norm_neg_typeclass]

/-- A symmetric subtraction estimate for the installed quotient norm. -/
theorem r2m_prefix_quotient_norm_sub_le_rev_typeclass
    (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N) :
    ‖q - r‖ ≤ ‖r‖ + ‖q‖ := by
  calc
    ‖q - r‖ = ‖r - q‖ :=
      r2m_prefix_quotient_norm_sub_rev_typeclass N q r
    _ ≤ ‖r‖ + ‖q‖ :=
      r2m_prefix_quotient_norm_sub_le_typeclass N r q

/-- Normed-additive-group inequality surface in standard mathlib notation. -/
def r2mPrefixQuotientNormedGroupInequalitiesReady : Prop :=
  r2mPrefixQuotientMetricNormCompatibilityReady ∧
  (∀ (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N),
    ‖q + r‖ ≤ ‖q‖ + ‖r‖) ∧
  (∀ (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N),
    ‖-q‖ = ‖q‖) ∧
  (∀ (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N),
    ‖q - r‖ = ‖r - q‖) ∧
  (∀ (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N),
    ‖q - r‖ ≤ ‖q‖ + ‖r‖)

/-- The quotient normed-additive-group inequality surface is ready. -/
theorem r2m_prefix_quotient_normed_group_inequalities_ready :
    r2mPrefixQuotientNormedGroupInequalitiesReady := by
  exact ⟨
    r2m_prefix_quotient_metric_norm_compatibility_ready,
    r2m_prefix_quotient_norm_add_le_typeclass,
    r2m_prefix_quotient_norm_neg_typeclass,
    r2m_prefix_quotient_norm_sub_rev_typeclass,
    r2m_prefix_quotient_norm_sub_le_typeclass⟩

/-- Boundary marker: the quotient now has the standard norm inequalities used
by mathlib's normed additive hierarchy, while full instance promotion remains a
separate explicit step. -/
def r2mPrefixQuotientNormedGroupInequalitiesBoundaryHeld : Prop :=
  r2mPrefixQuotientNormedGroupInequalitiesReady ∧
  True

theorem r2m_prefix_quotient_normed_group_inequalities_boundary_held :
    r2mPrefixQuotientNormedGroupInequalitiesBoundaryHeld := by
  exact ⟨r2m_prefix_quotient_normed_group_inequalities_ready, trivial⟩

end

end MathlibAnalytic
end MGAP4D
