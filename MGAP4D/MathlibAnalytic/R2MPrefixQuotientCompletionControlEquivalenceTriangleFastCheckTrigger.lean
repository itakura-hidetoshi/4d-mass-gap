import MGAP4D.MathlibAnalytic.R2MPrefixQuotientCompletionControlEquivalenceTriangleIndex

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Fast-check trigger leaf for the completion-control equivalence triangle.

This file is intentionally thin and proof-carrying: it imports the compact
triangle index and re-exposes the boundary theorem as the maximal changed Lean
target for `PR Lean Fast Check`. -/
def r2mPrefixQuotientCompletionControlEquivalenceTriangleFastCheckReady : Prop :=
  r2mPrefixQuotientCompletionControlEquivalenceTriangleIndexBoundaryHeld

/-- The fast-check trigger leaf is ready. -/
theorem r2m_prefix_quotient_completion_control_equivalence_triangle_fast_check_ready :
    r2mPrefixQuotientCompletionControlEquivalenceTriangleFastCheckReady := by
  exact r2m_prefix_quotient_completion_control_equivalence_triangle_index_boundary_held

/-- Boundary marker for the fast-check trigger leaf. -/
def r2mPrefixQuotientCompletionControlEquivalenceTriangleFastCheckBoundaryHeld : Prop :=
  r2mPrefixQuotientCompletionControlEquivalenceTriangleFastCheckReady ∧
  r2mPrefixQuotientCompletionControlEquivalenceTriangleIndexReady

/-- Boundary theorem for the fast-check trigger leaf. -/
theorem r2m_prefix_quotient_completion_control_equivalence_triangle_fast_check_boundary_held :
    r2mPrefixQuotientCompletionControlEquivalenceTriangleFastCheckBoundaryHeld := by
  exact ⟨
    r2m_prefix_quotient_completion_control_equivalence_triangle_fast_check_ready,
    r2m_prefix_quotient_completion_control_equivalence_triangle_index_ready⟩

end

end MathlibAnalytic
end MGAP4D
