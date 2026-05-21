import MGAP4D.MathlibAnalytic.R2MPrefixQuotientTypeclassOperations

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Mathlib-notation candidate: the additive identity is left-neutral. -/
theorem r2m_prefix_quotient_add_comm_group_zero_add_field
    (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N) :
    (0 : R2MPrefixZeroDistanceQuotient N) + q = q := by
  exact r2m_prefix_quotient_zero_add_typeclass N q

/-- Mathlib-notation candidate: the additive identity is right-neutral. -/
theorem r2m_prefix_quotient_add_comm_group_add_zero_field
    (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N) :
    q + (0 : R2MPrefixZeroDistanceQuotient N) = q := by
  exact r2m_prefix_quotient_add_zero_typeclass N q

/-- Mathlib-notation candidate: addition is associative. -/
theorem r2m_prefix_quotient_add_comm_group_add_assoc_field
    (N : ℕ) (q r s : R2MPrefixZeroDistanceQuotient N) :
    (q + r) + s = q + (r + s) := by
  exact r2m_prefix_quotient_add_assoc_typeclass N q r s

/-- Mathlib-notation candidate: addition is commutative. -/
theorem r2m_prefix_quotient_add_comm_group_add_comm_field
    (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N) :
    q + r = r + q := by
  exact r2m_prefix_quotient_add_comm_typeclass N q r

/-- Mathlib-notation candidate: negation cancels on the left. -/
theorem r2m_prefix_quotient_add_comm_group_neg_add_cancel_field
    (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N) :
    -q + q = (0 : R2MPrefixZeroDistanceQuotient N) := by
  exact r2m_prefix_quotient_neg_add_cancel_typeclass N q

/-- Mathlib-notation candidate: negation cancels on the right. -/
theorem r2m_prefix_quotient_add_comm_group_add_neg_cancel_field
    (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N) :
    q + -q = (0 : R2MPrefixZeroDistanceQuotient N) := by
  exact r2m_prefix_quotient_add_neg_cancel_typeclass N q

/-- Mathlib-notation candidate: subtraction is addition of the negative. -/
theorem r2m_prefix_quotient_add_comm_group_sub_eq_add_neg_field
    (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N) :
    q - r = q + -r := by
  rfl

/-- Mathlib-notation candidate: zero is fixed by negation. -/
theorem r2m_prefix_quotient_add_comm_group_neg_zero_field
    (N : ℕ) :
    -(0 : R2MPrefixZeroDistanceQuotient N) =
      (0 : R2MPrefixZeroDistanceQuotient N) := by
  exact r2m_prefix_quotient_smul_zero_typeclass N (-1 : ℝ)

/-- Additive-commutative-group instance candidate surface for the finite-prefix
zero-distance quotient.  This deliberately remains theorem-level: global
hierarchy installation is a later explicit promotion step. -/
def r2mPrefixQuotientAddCommGroupCandidateReady : Prop :=
  r2mPrefixQuotientTypeclassOperationsReady ∧
  (∀ (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N),
    (0 : R2MPrefixZeroDistanceQuotient N) + q = q) ∧
  (∀ (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N),
    q + (0 : R2MPrefixZeroDistanceQuotient N) = q) ∧
  (∀ (N : ℕ) (q r s : R2MPrefixZeroDistanceQuotient N),
    (q + r) + s = q + (r + s)) ∧
  (∀ (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N),
    q + r = r + q) ∧
  (∀ (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N),
    -q + q = (0 : R2MPrefixZeroDistanceQuotient N)) ∧
  (∀ (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N),
    q + -q = (0 : R2MPrefixZeroDistanceQuotient N)) ∧
  (∀ (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N),
    q - r = q + -r) ∧
  (∀ (N : ℕ),
    -(0 : R2MPrefixZeroDistanceQuotient N) =
      (0 : R2MPrefixZeroDistanceQuotient N))

/-- The additive-commutative-group candidate surface is ready. -/
theorem r2m_prefix_quotient_add_comm_group_candidate_ready :
    r2mPrefixQuotientAddCommGroupCandidateReady := by
  exact ⟨
    r2m_prefix_quotient_typeclass_operations_ready,
    r2m_prefix_quotient_add_comm_group_zero_add_field,
    r2m_prefix_quotient_add_comm_group_add_zero_field,
    r2m_prefix_quotient_add_comm_group_add_assoc_field,
    r2m_prefix_quotient_add_comm_group_add_comm_field,
    r2m_prefix_quotient_add_comm_group_neg_add_cancel_field,
    r2m_prefix_quotient_add_comm_group_add_neg_cancel_field,
    r2m_prefix_quotient_add_comm_group_sub_eq_add_neg_field,
    r2m_prefix_quotient_add_comm_group_neg_zero_field⟩

/-- Boundary marker for the add-comm-group candidate: all fields expected before
instance installation have mathlib-facing theorem statements. -/
def r2mPrefixQuotientAddCommGroupCandidateBoundaryHeld : Prop :=
  r2mPrefixQuotientAddCommGroupCandidateReady ∧
  True

theorem r2m_prefix_quotient_add_comm_group_candidate_boundary_held :
    r2mPrefixQuotientAddCommGroupCandidateBoundaryHeld := by
  exact ⟨r2m_prefix_quotient_add_comm_group_candidate_ready, trivial⟩

end

end MathlibAnalytic
end MGAP4D
