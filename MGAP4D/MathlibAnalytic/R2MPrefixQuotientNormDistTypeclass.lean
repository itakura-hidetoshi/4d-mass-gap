import MGAP4D.MathlibAnalytic.R2MPrefixQuotientModuleInstance
import MGAP4D.MathlibAnalytic.R2MPrefixQuotientScalarAlgebraSurface

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Mathlib `Norm` operation on the finite-prefix quotient, induced by the
quotient seminorm candidate. -/
instance r2mPrefixQuotientNormInst
    (N : ℕ) : Norm (R2MPrefixZeroDistanceQuotient N) where
  norm := r2mPrefixQuotientSeminorm N

/-- Mathlib `Dist` operation on the finite-prefix quotient, induced by the
quotient distance. -/
instance r2mPrefixQuotientDistInst
    (N : ℕ) : Dist (R2MPrefixZeroDistanceQuotient N) where
  dist := r2mPrefixQuotientDistance N

/-- The installed norm is definitionally the quotient seminorm. -/
theorem r2m_prefix_quotient_norm_typeclass_def
    (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N) :
    ‖q‖ = r2mPrefixQuotientSeminorm N q := by
  rfl

/-- The installed distance is definitionally the quotient distance. -/
theorem r2m_prefix_quotient_dist_typeclass_def
    (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N) :
    dist q r = r2mPrefixQuotientDistance N q r := by
  rfl

/-- Nonnegativity of the installed quotient norm. -/
theorem r2m_prefix_quotient_norm_nonneg
    (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N) :
    0 ≤ ‖q‖ := by
  rw [r2m_prefix_quotient_norm_typeclass_def]
  exact r2m_prefix_quotient_seminorm_nonneg N q

/-- The installed quotient norm vanishes exactly at zero. -/
theorem r2m_prefix_quotient_norm_eq_zero_iff
    (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N) :
    ‖q‖ = 0 ↔ q = 0 := by
  rw [r2m_prefix_quotient_norm_typeclass_def]
  rw [r2m_prefix_quotient_add_comm_group_zero_def]
  exact r2m_prefix_quotient_seminorm_eq_zero_iff N q

/-- The installed quotient norm is absolutely homogeneous. -/
theorem r2m_prefix_quotient_norm_smul_typeclass
    (N : ℕ) (c : ℝ) (q : R2MPrefixZeroDistanceQuotient N) :
    ‖c • q‖ = |c| * ‖q‖ := by
  rw [r2m_prefix_quotient_norm_typeclass_def]
  rw [r2m_prefix_quotient_module_smul_def]
  rw [r2m_prefix_quotient_norm_typeclass_def]
  exact r2m_prefix_quotient_norm_smul N c q

/-- Self-distance is zero for the installed distance. -/
theorem r2m_prefix_quotient_dist_self_typeclass
    (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N) :
    dist q q = 0 := by
  rw [r2m_prefix_quotient_dist_typeclass_def]
  exact r2m_prefix_quotient_distance_self N q

/-- Symmetry of the installed quotient distance. -/
theorem r2m_prefix_quotient_dist_comm_typeclass
    (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N) :
    dist q r = dist r q := by
  repeat rw [r2m_prefix_quotient_dist_typeclass_def]
  exact r2m_prefix_quotient_distance_symm N q r

/-- Triangle inequality for the installed quotient distance. -/
theorem r2m_prefix_quotient_dist_triangle_typeclass
    (N : ℕ) (q r s : R2MPrefixZeroDistanceQuotient N) :
    dist q s ≤ dist q r + dist r s := by
  repeat rw [r2m_prefix_quotient_dist_typeclass_def]
  exact r2m_prefix_quotient_distance_triangle N q r s

/-- The installed distance vanishes exactly on equality. -/
theorem r2m_prefix_quotient_dist_eq_zero_iff_typeclass
    (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N) :
    dist q r = 0 ↔ q = r := by
  rw [r2m_prefix_quotient_dist_typeclass_def]
  exact r2m_prefix_quotient_distance_eq_zero_iff N q r

/-- Mathlib-style bridge: the installed distance is the installed norm of the
installed subtraction. -/
theorem r2m_prefix_quotient_dist_eq_norm_sub_typeclass
    (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N) :
    dist q r = ‖q - r‖ := by
  rw [r2m_prefix_quotient_dist_typeclass_def]
  rw [r2m_prefix_quotient_norm_typeclass_def]
  rw [r2m_prefix_quotient_add_comm_group_sub_def]
  exact r2m_prefix_quotient_dist_eq_norm_sub N q r

/-- Typeclass-operation surface for quotient norm and distance.  This is the
last thin layer before attempting full `MetricSpace`/`NormedAddCommGroup`
promotion. -/
def r2mPrefixQuotientNormDistTypeclassReady : Prop :=
  r2mPrefixQuotientModuleInstanceReady ∧
  r2mPrefixQuotientScalarAlgebraSurfaceReady ∧
  (∀ (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N),
    ‖q‖ = r2mPrefixQuotientSeminorm N q) ∧
  (∀ (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N),
    dist q r = r2mPrefixQuotientDistance N q r) ∧
  (∀ (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N),
    0 ≤ ‖q‖) ∧
  (∀ (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N),
    ‖q‖ = 0 ↔ q = 0) ∧
  (∀ (N : ℕ) (c : ℝ) (q : R2MPrefixZeroDistanceQuotient N),
    ‖c • q‖ = |c| * ‖q‖) ∧
  (∀ (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N),
    dist q r = ‖q - r‖) ∧
  (∀ (N : ℕ) (q r s : R2MPrefixZeroDistanceQuotient N),
    dist q s ≤ dist q r + dist r s)

/-- The quotient norm/distance typeclass-operation surface is ready. -/
theorem r2m_prefix_quotient_norm_dist_typeclass_ready :
    r2mPrefixQuotientNormDistTypeclassReady := by
  exact ⟨
    r2m_prefix_quotient_module_instance_ready,
    r2m_prefix_quotient_scalar_algebra_surface_ready,
    r2m_prefix_quotient_norm_typeclass_def,
    r2m_prefix_quotient_dist_typeclass_def,
    r2m_prefix_quotient_norm_nonneg,
    r2m_prefix_quotient_norm_eq_zero_iff,
    r2m_prefix_quotient_norm_smul_typeclass,
    r2m_prefix_quotient_dist_eq_norm_sub_typeclass,
    r2m_prefix_quotient_dist_triangle_typeclass⟩

/-- Boundary marker: quotient norm and distance now have mathlib notation and
explicit compatibility theorems. -/
def r2mPrefixQuotientNormDistTypeclassBoundaryHeld : Prop :=
  r2mPrefixQuotientNormDistTypeclassReady ∧
  True

theorem r2m_prefix_quotient_norm_dist_typeclass_boundary_held :
    r2mPrefixQuotientNormDistTypeclassBoundaryHeld := by
  exact ⟨r2m_prefix_quotient_norm_dist_typeclass_ready, trivial⟩

end

end MathlibAnalytic
end MGAP4D
