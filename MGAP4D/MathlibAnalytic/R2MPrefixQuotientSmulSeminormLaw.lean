import MGAP4D.MathlibAnalytic.R2MPrefixQuotientSmulOperation

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Absolute homogeneity of the transported quotient seminorm under the
well-defined quotient scalar operation.  The proof reduces by quotient induction
to the already-proved finite-prefix bounded seminorm absolute homogeneity. -/
theorem r2m_prefix_quotient_seminorm_smul_abs
    (N : ℕ) (c : ℝ) (q : R2MPrefixZeroDistanceQuotient N) :
    r2mPrefixQuotientSeminorm N (r2mPrefixQuotientSmul N c q) =
      |c| * r2mPrefixQuotientSeminorm N q := by
  refine Quotient.inductionOn' q ?_
  intro x
  rw [r2m_prefix_quotient_smul_mk]
  rw [r2m_prefix_quotient_seminorm_mk]
  rw [r2m_prefix_quotient_seminorm_mk]
  exact concrete_l2_graph_pair_prefix_energy_bounded_seminorm_candidate_smul_abs N c x

/-- The quotient scalar operation preserves the zero class. -/
theorem r2m_prefix_quotient_smul_zero_class
    (N : ℕ) (c : ℝ) :
    r2mPrefixQuotientSmul N c (r2mPrefixQuotientZeroClass N) =
      r2mPrefixQuotientZeroClass N := by
  apply (r2m_prefix_quotient_seminorm_eq_zero_iff N
    (r2mPrefixQuotientSmul N c (r2mPrefixQuotientZeroClass N))).mp
  rw [r2m_prefix_quotient_seminorm_smul_abs]
  rw [r2m_prefix_quotient_seminorm_zero_class']
  ring

/-- Scalar multiplication by zero sends every quotient point to the zero class,
proved through the separated quotient seminorm. -/
theorem r2m_prefix_quotient_zero_smul_eq_zero_class
    (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N) :
    r2mPrefixQuotientSmul N 0 q = r2mPrefixQuotientZeroClass N := by
  apply (r2m_prefix_quotient_seminorm_eq_zero_iff N
    (r2mPrefixQuotientSmul N 0 q)).mp
  rw [r2m_prefix_quotient_seminorm_smul_abs]
  simp

/-- Readiness package for quotient scalar seminorm laws. -/
def r2mPrefixQuotientSmulSeminormLawReady : Prop :=
  r2mPrefixQuotientSmulOperationReady ∧
  (∀ (N : ℕ) (c : ℝ) (q : R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientSeminorm N (r2mPrefixQuotientSmul N c q) =
      |c| * r2mPrefixQuotientSeminorm N q) ∧
  (∀ (N : ℕ) (c : ℝ),
    r2mPrefixQuotientSmul N c (r2mPrefixQuotientZeroClass N) =
      r2mPrefixQuotientZeroClass N) ∧
  (∀ (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientSmul N 0 q = r2mPrefixQuotientZeroClass N)

/-- The quotient scalar seminorm law surface is ready. -/
theorem r2m_prefix_quotient_smul_seminorm_law_ready :
    r2mPrefixQuotientSmulSeminormLawReady := by
  exact ⟨
    r2m_prefix_quotient_smul_operation_ready,
    r2m_prefix_quotient_seminorm_smul_abs,
    r2m_prefix_quotient_smul_zero_class,
    r2m_prefix_quotient_zero_smul_eq_zero_class⟩

/-- Boundary marker: scalar seminorm laws are closed; addition and full
vector-space promotion remain intentionally separate. -/
def r2mPrefixQuotientAdditiveLawBoundaryHeld : Prop :=
  r2mPrefixQuotientSmulSeminormLawReady ∧
  True

theorem r2m_prefix_quotient_additive_law_boundary_held :
    r2mPrefixQuotientAdditiveLawBoundaryHeld := by
  exact ⟨r2m_prefix_quotient_smul_seminorm_law_ready, trivial⟩

end

end MathlibAnalytic
end MGAP4D
