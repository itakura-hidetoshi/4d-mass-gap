import MGAP4D.MathlibAnalytic.R2MPrefixQuotientAddCommGroupCandidate

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The finite-prefix zero-distance quotient carries the additive-commutative
 group structure induced by the representative addition, negation, and zero.

This is the first genuine mathlib hierarchy promotion for the quotient layer:
the previous files proved the laws theorem-by-theorem, and this instance simply
packages those laws in the standard `AddCommGroup` interface. -/
instance r2mPrefixQuotientAddCommGroupInst
    (N : ℕ) : AddCommGroup (R2MPrefixZeroDistanceQuotient N) where
  add := r2mPrefixQuotientAdd N
  add_assoc := r2m_prefix_quotient_add_comm_group_add_assoc_field N
  zero := r2mPrefixQuotientZeroClass N
  zero_add := r2m_prefix_quotient_add_comm_group_zero_add_field N
  add_zero := r2m_prefix_quotient_add_comm_group_add_zero_field N
  neg := r2mPrefixQuotientNeg N
  sub := r2mPrefixQuotientSub N
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel := r2m_prefix_quotient_add_comm_group_neg_add_cancel_field N
  add_comm := r2m_prefix_quotient_add_comm_group_add_comm_field N

/-- The installed additive commutative group uses the previously constructed
quotient addition definitionally. -/
theorem r2m_prefix_quotient_add_comm_group_add_def
    (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N) :
    q + r = r2mPrefixQuotientAdd N q r := by
  rfl

/-- The installed additive commutative group uses the previously constructed
quotient zero definitionally. -/
theorem r2m_prefix_quotient_add_comm_group_zero_def
    (N : ℕ) :
    (0 : R2MPrefixZeroDistanceQuotient N) =
      r2mPrefixQuotientZeroClass N := by
  rfl

/-- The installed additive commutative group uses the previously constructed
quotient negation definitionally. -/
theorem r2m_prefix_quotient_add_comm_group_neg_def
    (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N) :
    -q = r2mPrefixQuotientNeg N q := by
  rfl

/-- The installed additive commutative group uses the previously constructed
quotient subtraction definitionally. -/
theorem r2m_prefix_quotient_add_comm_group_sub_def
    (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N) :
    q - r = r2mPrefixQuotientSub N q r := by
  rfl

/-- After the hierarchy promotion, the quotient add-comm-group surface is fully
available through mathlib typeclass inference. -/
def r2mPrefixQuotientAddCommGroupInstanceReady : Prop :=
  r2mPrefixQuotientAddCommGroupCandidateReady ∧
  (∀ (N : ℕ), Nonempty (AddCommGroup (R2MPrefixZeroDistanceQuotient N))) ∧
  (∀ (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N),
    q + r = r2mPrefixQuotientAdd N q r) ∧
  (∀ (N : ℕ),
    (0 : R2MPrefixZeroDistanceQuotient N) =
      r2mPrefixQuotientZeroClass N) ∧
  (∀ (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N),
    -q = r2mPrefixQuotientNeg N q) ∧
  (∀ (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N),
    q - r = r2mPrefixQuotientSub N q r)

/-- The quotient additive commutative group instance is ready. -/
theorem r2m_prefix_quotient_add_comm_group_instance_ready :
    r2mPrefixQuotientAddCommGroupInstanceReady := by
  exact ⟨
    r2m_prefix_quotient_add_comm_group_candidate_ready,
    fun N => ⟨inferInstance⟩,
    r2m_prefix_quotient_add_comm_group_add_def,
    r2m_prefix_quotient_add_comm_group_zero_def,
    r2m_prefix_quotient_add_comm_group_neg_def,
    r2m_prefix_quotient_add_comm_group_sub_def⟩

/-- Boundary marker: the finite-prefix zero-distance quotient has now crossed
from theorem-level add-comm-group candidate to an installed mathlib
`AddCommGroup` instance. -/
def r2mPrefixQuotientAddCommGroupInstanceBoundaryHeld : Prop :=
  r2mPrefixQuotientAddCommGroupInstanceReady ∧
  True

theorem r2m_prefix_quotient_add_comm_group_instance_boundary_held :
    r2mPrefixQuotientAddCommGroupInstanceBoundaryHeld := by
  exact ⟨r2m_prefix_quotient_add_comm_group_instance_ready, trivial⟩

end

end MathlibAnalytic
end MGAP4D
