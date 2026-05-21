import MGAP4D.MathlibAnalytic.R2MPrefixQuotientNormedGroupInequalities

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A translated triangle inequality: the norm of `q` is controlled by the
norm of the displacement from `r` plus the norm of `r`.  The identity
`q = (q - r) + r` is discharged by mathlib's additive-group normalizer. -/
theorem r2m_prefix_quotient_norm_le_norm_sub_add_norm_typeclass
    (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N) :
    ‖q‖ ≤ ‖q - r‖ + ‖r‖ := by
  calc
    ‖q‖ = ‖(q - r) + r‖ := by
      congr 1
      abel
    _ ≤ ‖q - r‖ + ‖r‖ :=
      r2m_prefix_quotient_norm_add_le_typeclass N (q - r) r

/-- The symmetric translated triangle inequality. -/
theorem r2m_prefix_quotient_norm_le_norm_sub_add_norm_symm_typeclass
    (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N) :
    ‖r‖ ≤ ‖q - r‖ + ‖q‖ := by
  calc
    ‖r‖ = ‖(r - q) + q‖ := by
      congr 1
      abel
    _ ≤ ‖r - q‖ + ‖q‖ :=
      r2m_prefix_quotient_norm_add_le_typeclass N (r - q) q
    _ = ‖q - r‖ + ‖q‖ := by
      rw [r2m_prefix_quotient_norm_sub_rev_typeclass N r q]

/-- Reverse triangle inequality for the installed quotient norm. -/
theorem r2m_prefix_quotient_abs_norm_sub_le_norm_sub_typeclass
    (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N) :
    |‖q‖ - ‖r‖| ≤ ‖q - r‖ := by
  apply abs_le.mpr
  constructor
  · have h := r2m_prefix_quotient_norm_le_norm_sub_add_norm_symm_typeclass N q r
    linarith
  · have h := r2m_prefix_quotient_norm_le_norm_sub_add_norm_typeclass N q r
    linarith

/-- Reverse triangle inequality in installed distance notation. -/
theorem r2m_prefix_quotient_abs_norm_sub_le_dist_typeclass
    (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N) :
    |‖q‖ - ‖r‖| ≤ dist q r := by
  rw [r2m_prefix_quotient_dist_eq_norm_sub_typeclass]
  exact r2m_prefix_quotient_abs_norm_sub_le_norm_sub_typeclass N q r

/-- Reverse-triangle surface for the finite-prefix quotient in mathlib notation. -/
def r2mPrefixQuotientReverseTriangleReady : Prop :=
  r2mPrefixQuotientNormedGroupInequalitiesReady ∧
  (∀ (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N),
    ‖q‖ ≤ ‖q - r‖ + ‖r‖) ∧
  (∀ (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N),
    ‖r‖ ≤ ‖q - r‖ + ‖q‖) ∧
  (∀ (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N),
    |‖q‖ - ‖r‖| ≤ ‖q - r‖) ∧
  (∀ (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N),
    |‖q‖ - ‖r‖| ≤ dist q r)

/-- The quotient reverse-triangle surface is ready. -/
theorem r2m_prefix_quotient_reverse_triangle_ready :
    r2mPrefixQuotientReverseTriangleReady := by
  exact ⟨
    r2m_prefix_quotient_normed_group_inequalities_ready,
    r2m_prefix_quotient_norm_le_norm_sub_add_norm_typeclass,
    r2m_prefix_quotient_norm_le_norm_sub_add_norm_symm_typeclass,
    r2m_prefix_quotient_abs_norm_sub_le_norm_sub_typeclass,
    r2m_prefix_quotient_abs_norm_sub_le_dist_typeclass⟩

/-- Boundary marker: the quotient now supports the reverse triangle inequality
in both norm-subtraction and distance form. -/
def r2mPrefixQuotientReverseTriangleBoundaryHeld : Prop :=
  r2mPrefixQuotientReverseTriangleReady ∧
  True

theorem r2m_prefix_quotient_reverse_triangle_boundary_held :
    r2mPrefixQuotientReverseTriangleBoundaryHeld := by
  exact ⟨r2m_prefix_quotient_reverse_triangle_ready, trivial⟩

end

end MathlibAnalytic
end MGAP4D
