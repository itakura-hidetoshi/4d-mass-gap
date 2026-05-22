import MGAP4D.MathlibAnalytic.R2MPrefixQuotientCompletionControlEquivalenceTriangle

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A compact index surface for the three equivalent completion-control views in
the prefix quotient lane.  This leaf is intentionally thin: it records the
triangle theorem and its six directional transport maps as a single audit target
for the PR fast-check lane. -/
def r2mPrefixQuotientCompletionControlEquivalenceTriangleIndexReady : Prop :=
  r2mPrefixQuotientCompletionControlEquivalenceTriangleReady ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientCompletionControlEquivalenceTriangle N u) ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientMetricTailControlled N u ↔
      r2mPrefixQuotientLocalConvergenceControlled N u) ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientMetricTailControlled N u ↔
      ∀ ε : ℝ, 0 < ε →
        ∃ M : ℕ, r2mPrefixQuotientStableHalfRadiusPacket N u ε M) ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientLocalConvergenceControlled N u ↔
      ∀ ε : ℝ, 0 < ε →
        ∃ M : ℕ, r2mPrefixQuotientStableHalfRadiusPacket N u ε M)

/-- The compact completion-control equivalence triangle index is ready. -/
theorem r2m_prefix_quotient_completion_control_equivalence_triangle_index_ready :
    r2mPrefixQuotientCompletionControlEquivalenceTriangleIndexReady := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact r2m_prefix_quotient_completion_control_equivalence_triangle_ready
  · intro N u
    exact r2m_prefix_quotient_completion_control_equivalence_triangle N u
  · intro N u
    exact r2m_prefix_quotient_metric_tail_controlled_iff_local_convergence_controlled N u
  · intro N u
    exact r2m_prefix_quotient_metric_tail_controlled_iff_stable_half_radius_packets N u
  · intro N u
    exact r2m_prefix_quotient_local_convergence_controlled_iff_stable_half_radius_packets N u

/-- Boundary marker for the compact equivalence triangle index. -/
def r2mPrefixQuotientCompletionControlEquivalenceTriangleIndexBoundaryHeld : Prop :=
  r2mPrefixQuotientCompletionControlEquivalenceTriangleIndexReady ∧
  r2mPrefixQuotientCompletionControlEquivalenceTriangleBoundaryHeld

/-- Boundary theorem for the compact equivalence triangle index. -/
theorem r2m_prefix_quotient_completion_control_equivalence_triangle_index_boundary_held :
    r2mPrefixQuotientCompletionControlEquivalenceTriangleIndexBoundaryHeld := by
  exact ⟨
    r2m_prefix_quotient_completion_control_equivalence_triangle_index_ready,
    r2m_prefix_quotient_completion_control_equivalence_triangle_boundary_held⟩

end

end MathlibAnalytic
end MGAP4D
