import MGAP4D.MathlibAnalytic.R2MPrefixQuotientModuleInstanceCandidate
import MGAP4D.MathlibAnalytic.R2MPrefixQuotientSubLaws

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Typeclass zero on the finite-prefix zero-distance quotient. -/
instance r2mPrefixQuotientZeroInst
    (N : ℕ) : Zero (R2MPrefixZeroDistanceQuotient N) where
  zero := r2mPrefixQuotientZeroClass N

/-- Typeclass addition on the finite-prefix zero-distance quotient. -/
instance r2mPrefixQuotientAddInst
    (N : ℕ) : Add (R2MPrefixZeroDistanceQuotient N) where
  add := r2mPrefixQuotientAdd N

/-- Typeclass negation on the finite-prefix zero-distance quotient. -/
instance r2mPrefixQuotientNegInst
    (N : ℕ) : Neg (R2MPrefixZeroDistanceQuotient N) where
  neg := r2mPrefixQuotientNeg N

/-- Typeclass subtraction on the finite-prefix zero-distance quotient. -/
instance r2mPrefixQuotientSubInst
    (N : ℕ) : Sub (R2MPrefixZeroDistanceQuotient N) where
  sub := r2mPrefixQuotientSub N

/-- Typeclass real scalar multiplication on the finite-prefix zero-distance
quotient. -/
instance r2mPrefixQuotientSMulInst
    (N : ℕ) : SMul ℝ (R2MPrefixZeroDistanceQuotient N) where
  smul := r2mPrefixQuotientSmul N

/-- The typeclass zero notation is definitionally the quotient zero class. -/
theorem r2m_prefix_quotient_zero_typeclass_def
    (N : ℕ) :
    (0 : R2MPrefixZeroDistanceQuotient N) =
      r2mPrefixQuotientZeroClass N := by
  rfl

/-- The typeclass addition notation is definitionally the quotient addition. -/
theorem r2m_prefix_quotient_add_typeclass_def
    (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N) :
    q + r = r2mPrefixQuotientAdd N q r := by
  rfl

/-- The typeclass negation notation is definitionally quotient negation. -/
theorem r2m_prefix_quotient_neg_typeclass_def
    (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N) :
    -q = r2mPrefixQuotientNeg N q := by
  rfl

/-- The typeclass subtraction notation is definitionally quotient subtraction. -/
theorem r2m_prefix_quotient_sub_typeclass_def
    (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N) :
    q - r = r2mPrefixQuotientSub N q r := by
  rfl

/-- The typeclass scalar-multiplication notation is definitionally quotient
scalar multiplication. -/
theorem r2m_prefix_quotient_smul_typeclass_def
    (N : ℕ) (c : ℝ) (q : R2MPrefixZeroDistanceQuotient N) :
    c • q = r2mPrefixQuotientSmul N c q := by
  rfl

/-- Mathlib notation version of the left zero law. -/
theorem r2m_prefix_quotient_zero_add_typeclass
    (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N) :
    (0 : R2MPrefixZeroDistanceQuotient N) + q = q := by
  exact r2m_prefix_quotient_zero_add N q

/-- Mathlib notation version of the right zero law. -/
theorem r2m_prefix_quotient_add_zero_typeclass
    (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N) :
    q + (0 : R2MPrefixZeroDistanceQuotient N) = q := by
  exact r2m_prefix_quotient_add_zero N q

/-- Mathlib notation version of commutativity of quotient addition. -/
theorem r2m_prefix_quotient_add_comm_typeclass
    (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N) :
    q + r = r + q := by
  exact r2m_prefix_quotient_add_comm N q r

/-- Mathlib notation version of associativity of quotient addition. -/
theorem r2m_prefix_quotient_add_assoc_typeclass
    (N : ℕ) (q r s : R2MPrefixZeroDistanceQuotient N) :
    (q + r) + s = q + (r + s) := by
  exact r2m_prefix_quotient_add_assoc N q r s

/-- Mathlib notation version of the left inverse law. -/
theorem r2m_prefix_quotient_neg_add_cancel_typeclass
    (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N) :
    -q + q = (0 : R2MPrefixZeroDistanceQuotient N) := by
  exact r2m_prefix_quotient_neg_add N q

/-- Mathlib notation version of the right inverse law. -/
theorem r2m_prefix_quotient_add_neg_cancel_typeclass
    (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N) :
    q + -q = (0 : R2MPrefixZeroDistanceQuotient N) := by
  exact r2m_prefix_quotient_add_neg N q

/-- Mathlib notation version of the one-scalar law. -/
theorem r2m_prefix_quotient_one_smul_typeclass
    (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N) :
    (1 : ℝ) • q = q := by
  exact r2m_prefix_quotient_module_one_smul_field N q

/-- Mathlib notation version of scalar associativity. -/
theorem r2m_prefix_quotient_mul_smul_typeclass
    (N : ℕ) (a b : ℝ) (q : R2MPrefixZeroDistanceQuotient N) :
    (a * b) • q = a • (b • q) := by
  exact r2m_prefix_quotient_module_mul_smul_field N a b q

/-- Mathlib notation version of zero scalar multiplication. -/
theorem r2m_prefix_quotient_zero_smul_typeclass
    (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N) :
    (0 : ℝ) • q = (0 : R2MPrefixZeroDistanceQuotient N) := by
  exact r2m_prefix_quotient_module_zero_smul_field N q

/-- Mathlib notation version of scalar multiplication of zero. -/
theorem r2m_prefix_quotient_smul_zero_typeclass
    (N : ℕ) (c : ℝ) :
    c • (0 : R2MPrefixZeroDistanceQuotient N) =
      (0 : R2MPrefixZeroDistanceQuotient N) := by
  exact r2m_prefix_quotient_module_smul_zero_field N c

/-- Mathlib notation version of scalar distributivity over addition. -/
theorem r2m_prefix_quotient_smul_add_typeclass
    (N : ℕ) (c : ℝ) (q r : R2MPrefixZeroDistanceQuotient N) :
    c • (q + r) = c • q + c • r := by
  exact r2m_prefix_quotient_module_smul_add_field N c q r

/-- Mathlib notation version of additive scalar distributivity. -/
theorem r2m_prefix_quotient_add_smul_typeclass
    (N : ℕ) (a b : ℝ) (q : R2MPrefixZeroDistanceQuotient N) :
    (a + b) • q = a • q + b • q := by
  exact r2m_prefix_quotient_module_add_smul_field N a b q

/-- The quotient operation layer has been exposed through Lean/mathlib notation,
without yet installing the full algebraic hierarchy as global instances. -/
def r2mPrefixQuotientTypeclassOperationsReady : Prop :=
  r2mPrefixQuotientModuleInstanceCandidateReady ∧
  r2mPrefixQuotientSubLawsReady ∧
  (∀ (N : ℕ),
    (0 : R2MPrefixZeroDistanceQuotient N) =
      r2mPrefixQuotientZeroClass N) ∧
  (∀ (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N),
    q + r = r2mPrefixQuotientAdd N q r) ∧
  (∀ (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N),
    -q = r2mPrefixQuotientNeg N q) ∧
  (∀ (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N),
    q - r = r2mPrefixQuotientSub N q r) ∧
  (∀ (N : ℕ) (c : ℝ) (q : R2MPrefixZeroDistanceQuotient N),
    c • q = r2mPrefixQuotientSmul N c q)

/-- Typeclass operation bridge readiness. -/
theorem r2m_prefix_quotient_typeclass_operations_ready :
    r2mPrefixQuotientTypeclassOperationsReady := by
  exact ⟨
    r2m_prefix_quotient_module_instance_candidate_ready,
    r2m_prefix_quotient_sub_laws_ready,
    r2m_prefix_quotient_zero_typeclass_def,
    r2m_prefix_quotient_add_typeclass_def,
    r2m_prefix_quotient_neg_typeclass_def,
    r2m_prefix_quotient_sub_typeclass_def,
    r2m_prefix_quotient_smul_typeclass_def⟩

end

end MathlibAnalytic
end MGAP4D
