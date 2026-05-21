import MGAP4D.MathlibAnalytic.R2MPrefixQuotientModuleZeroLaws

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Mathlib-field orientation for `one_smul` on the quotient. -/
theorem r2m_prefix_quotient_module_one_smul_field
    (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N) :
    r2mPrefixQuotientSmul N (1 : ℝ) q = q := by
  exact r2m_prefix_quotient_one_smul N q

/-- Mathlib-field orientation for `mul_smul` on the quotient.  The earlier
surface theorem was stated in the analytic composition direction, so the
instance-facing field uses its symmetric form. -/
theorem r2m_prefix_quotient_module_mul_smul_field
    (N : ℕ) (a b : ℝ) (q : R2MPrefixZeroDistanceQuotient N) :
    r2mPrefixQuotientSmul N (a * b) q =
      r2mPrefixQuotientSmul N a (r2mPrefixQuotientSmul N b q) := by
  exact (r2m_prefix_quotient_smul_smul N a b q).symm

/-- Mathlib-field orientation for `zero_smul` on the quotient. -/
theorem r2m_prefix_quotient_module_zero_smul_field
    (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N) :
    r2mPrefixQuotientSmul N (0 : ℝ) q =
      r2mPrefixQuotientZeroClass N := by
  exact r2m_prefix_quotient_zero_smul N q

/-- Mathlib-field orientation for `smul_zero` on the quotient. -/
theorem r2m_prefix_quotient_module_smul_zero_field
    (N : ℕ) (c : ℝ) :
    r2mPrefixQuotientSmul N c (r2mPrefixQuotientZeroClass N) =
      r2mPrefixQuotientZeroClass N := by
  exact r2m_prefix_quotient_smul_zero N c

/-- Mathlib-field orientation for `smul_add` on the quotient. -/
theorem r2m_prefix_quotient_module_smul_add_field
    (N : ℕ) (c : ℝ)
    (q r : R2MPrefixZeroDistanceQuotient N) :
    r2mPrefixQuotientSmul N c (r2mPrefixQuotientAdd N q r) =
      r2mPrefixQuotientAdd N
        (r2mPrefixQuotientSmul N c q)
        (r2mPrefixQuotientSmul N c r) := by
  exact r2m_prefix_quotient_smul_add N c q r

/-- Mathlib-field orientation for `add_smul` on the quotient. -/
theorem r2m_prefix_quotient_module_add_smul_field
    (N : ℕ) (a b : ℝ)
    (q : R2MPrefixZeroDistanceQuotient N) :
    r2mPrefixQuotientSmul N (a + b) q =
      r2mPrefixQuotientAdd N
        (r2mPrefixQuotientSmul N a q)
        (r2mPrefixQuotientSmul N b q) := by
  exact r2m_prefix_quotient_add_smul N a b q

/-- Instance-candidate theorem surface for a real `Module` on the finite-prefix
zero-distance quotient.  This is intentionally still a theorem-level candidate:
installing global typeclass instances is kept as the next explicit audit step. -/
def r2mPrefixQuotientModuleInstanceCandidateReady : Prop :=
  r2mPrefixQuotientFullModuleSurfaceReady ∧
  (∀ (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientSmul N (1 : ℝ) q = q) ∧
  (∀ (N : ℕ) (a b : ℝ) (q : R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientSmul N (a * b) q =
      r2mPrefixQuotientSmul N a (r2mPrefixQuotientSmul N b q)) ∧
  (∀ (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientSmul N (0 : ℝ) q =
      r2mPrefixQuotientZeroClass N) ∧
  (∀ (N : ℕ) (c : ℝ),
    r2mPrefixQuotientSmul N c (r2mPrefixQuotientZeroClass N) =
      r2mPrefixQuotientZeroClass N) ∧
  (∀ (N : ℕ) (c : ℝ) (q r : R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientSmul N c (r2mPrefixQuotientAdd N q r) =
      r2mPrefixQuotientAdd N
        (r2mPrefixQuotientSmul N c q)
        (r2mPrefixQuotientSmul N c r)) ∧
  (∀ (N : ℕ) (a b : ℝ) (q : R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientSmul N (a + b) q =
      r2mPrefixQuotientAdd N
        (r2mPrefixQuotientSmul N a q)
        (r2mPrefixQuotientSmul N b q))

/-- The quotient module instance candidate surface is ready. -/
theorem r2m_prefix_quotient_module_instance_candidate_ready :
    r2mPrefixQuotientModuleInstanceCandidateReady := by
  exact ⟨
    r2m_prefix_quotient_full_module_surface_ready,
    r2m_prefix_quotient_module_one_smul_field,
    r2m_prefix_quotient_module_mul_smul_field,
    r2m_prefix_quotient_module_zero_smul_field,
    r2m_prefix_quotient_module_smul_zero_field,
    r2m_prefix_quotient_module_smul_add_field,
    r2m_prefix_quotient_module_add_smul_field⟩

/-- Boundary marker: all module-instance-facing field orientations have now been
made explicit and checked, but no global instance is installed here. -/
def r2mPrefixQuotientModuleInstanceCandidateBoundaryHeld : Prop :=
  r2mPrefixQuotientModuleInstanceCandidateReady ∧
  True

theorem r2m_prefix_quotient_module_instance_candidate_boundary_held :
    r2mPrefixQuotientModuleInstanceCandidateBoundaryHeld := by
  exact ⟨r2m_prefix_quotient_module_instance_candidate_ready, trivial⟩

end

end MathlibAnalytic
end MGAP4D
