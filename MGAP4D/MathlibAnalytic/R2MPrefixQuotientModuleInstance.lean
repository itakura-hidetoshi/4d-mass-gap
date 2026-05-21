import MGAP4D.MathlibAnalytic.R2MPrefixQuotientAddCommGroupInstance

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The finite-prefix zero-distance quotient carries the real module structure
induced by the representative scalar multiplication.

The proof is intentionally thin: all analytic work was already performed in the
well-definedness and module-law surface files.  This file only promotes those
checked laws into mathlib's standard `Module ℝ` interface. -/
instance r2mPrefixQuotientModuleInst
    (N : ℕ) : Module ℝ (R2MPrefixZeroDistanceQuotient N) where
  one_smul := r2m_prefix_quotient_one_smul_typeclass N
  mul_smul := r2m_prefix_quotient_mul_smul_typeclass N
  smul_zero := r2m_prefix_quotient_smul_zero_typeclass N
  smul_add := r2m_prefix_quotient_smul_add_typeclass N
  zero_smul := r2m_prefix_quotient_zero_smul_typeclass N
  add_smul := r2m_prefix_quotient_add_smul_typeclass N

/-- The installed real module uses the previously constructed quotient scalar
multiplication definitionally. -/
theorem r2m_prefix_quotient_module_smul_def
    (N : ℕ) (c : ℝ) (q : R2MPrefixZeroDistanceQuotient N) :
    c • q = r2mPrefixQuotientSmul N c q := by
  rfl

/-- Mathlib now recognizes the quotient as a real module. -/
def r2mPrefixQuotientModuleInstanceReady : Prop :=
  r2mPrefixQuotientModuleInstanceCandidateReady ∧
  r2mPrefixQuotientAddCommGroupInstanceReady ∧
  (∀ (N : ℕ), Nonempty (Module ℝ (R2MPrefixZeroDistanceQuotient N))) ∧
  (∀ (N : ℕ) (c : ℝ) (q : R2MPrefixZeroDistanceQuotient N),
    c • q = r2mPrefixQuotientSmul N c q)

/-- The quotient real module instance is ready. -/
theorem r2m_prefix_quotient_module_instance_ready :
    r2mPrefixQuotientModuleInstanceReady := by
  exact ⟨
    r2m_prefix_quotient_module_instance_candidate_ready,
    r2m_prefix_quotient_add_comm_group_instance_ready,
    fun N => ⟨inferInstance⟩,
    r2m_prefix_quotient_module_smul_def⟩

/-- Boundary marker: the finite-prefix zero-distance quotient has crossed from
theorem-level module candidate to an installed mathlib `Module ℝ` instance. -/
def r2mPrefixQuotientModuleInstanceBoundaryHeld : Prop :=
  r2mPrefixQuotientModuleInstanceReady ∧
  True

theorem r2m_prefix_quotient_module_instance_boundary_held :
    r2mPrefixQuotientModuleInstanceBoundaryHeld := by
  exact ⟨r2m_prefix_quotient_module_instance_ready, trivial⟩

end

end MathlibAnalytic
end MGAP4D
