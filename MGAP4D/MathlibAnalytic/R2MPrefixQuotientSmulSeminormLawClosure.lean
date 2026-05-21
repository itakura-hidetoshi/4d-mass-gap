import MGAP4D.MathlibAnalytic.R2MPrefixQuotientSmulSeminormLaw
import MGAP4D.MathlibAnalytic.R2MPrefixConcreteZeroCompatibility

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Absolute homogeneity of the transported quotient seminorm under the
well-defined quotient scalar operation.  The missing bridge is the concrete
zero-compatibility law `d_N(x,0)=seminormCandidate x`. -/
theorem r2m_prefix_quotient_seminorm_smul_abs_closed
    (N : ℕ) (c : ℝ) (q : R2MPrefixZeroDistanceQuotient N) :
    r2mPrefixQuotientSeminorm N (r2mPrefixQuotientSmul N c q) =
      |c| * r2mPrefixQuotientSeminorm N q := by
  refine Quotient.inductionOn' q ?_
  intro x
  rw [r2m_prefix_quotient_smul_mk]
  rw [r2m_prefix_quotient_seminorm_mk]
  rw [r2m_prefix_quotient_seminorm_mk]
  rw [r2m_prefix_pseudo_distance_zero_right_eq_seminorm]
  rw [r2m_prefix_pseudo_distance_zero_right_eq_seminorm]
  exact concrete_l2_graph_pair_prefix_energy_bounded_seminorm_candidate_smul_abs N c x

/-- The quotient scalar operation preserves the zero class. -/
theorem r2m_prefix_quotient_smul_zero_class_closed
    (N : ℕ) (c : ℝ) :
    r2mPrefixQuotientSmul N c (r2mPrefixQuotientZeroClass N) =
      r2mPrefixQuotientZeroClass N := by
  unfold r2mPrefixQuotientZeroClass
  rw [r2m_prefix_quotient_smul_mk]
  rw [concrete_l2_graph_pair_prefix_energy_bounded_smul_zero_eq]

/-- Scalar multiplication by zero sends every quotient point to the zero class,
using quotient separation and absolute homogeneity. -/
theorem r2m_prefix_quotient_zero_smul_eq_zero_class_closed
    (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N) :
    r2mPrefixQuotientSmul N 0 q = r2mPrefixQuotientZeroClass N := by
  apply (r2m_prefix_quotient_seminorm_eq_zero_iff N
    (r2mPrefixQuotientSmul N 0 q)).mp
  rw [r2m_prefix_quotient_seminorm_smul_abs_closed]
  simp

/-- The scalar seminorm law obligation is now discharged. -/
def r2mPrefixQuotientSmulSeminormLawClosed : Prop :=
  r2mPrefixQuotientSmulSeminormLawBoundaryHeld ∧
  r2mPrefixQuotientSmulSeminormLawObligation ∧
  r2mPrefixSmulZeroPseudoDistanceCompatibilityObligation ∧
  (∀ (N : ℕ) (c : ℝ),
    r2mPrefixQuotientSmul N c (r2mPrefixQuotientZeroClass N) =
      r2mPrefixQuotientZeroClass N) ∧
  (∀ (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientSmul N 0 q = r2mPrefixQuotientZeroClass N)

/-- The quotient scalar seminorm law surface is closed. -/
theorem r2m_prefix_quotient_smul_seminorm_law_closed :
    r2mPrefixQuotientSmulSeminormLawClosed := by
  exact ⟨
    r2m_prefix_quotient_smul_seminorm_law_boundary_held,
    r2m_prefix_quotient_seminorm_smul_abs_closed,
    r2m_prefix_smul_zero_pseudo_distance_compatibility,
    r2m_prefix_quotient_smul_zero_class_closed,
    r2m_prefix_quotient_zero_smul_eq_zero_class_closed⟩

/-- Boundary marker: scalar seminorm laws are now closed; quotient addition and
full vector-space/typeclass promotion remain intentionally separate. -/
def r2mPrefixQuotientAdditiveLawAfterSmulBoundaryHeld : Prop :=
  r2mPrefixQuotientSmulSeminormLawClosed ∧
  True

theorem r2m_prefix_quotient_additive_law_after_smul_boundary_held :
    r2mPrefixQuotientAdditiveLawAfterSmulBoundaryHeld := by
  exact ⟨r2m_prefix_quotient_smul_seminorm_law_closed, trivial⟩

end

end MathlibAnalytic
end MGAP4D
