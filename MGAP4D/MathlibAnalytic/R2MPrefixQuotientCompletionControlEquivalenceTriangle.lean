import MGAP4D.MathlibAnalytic.R2MPrefixQuotientCompletionStableHalfRadiusLocalBridge

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The three completion-control views used in the prefix quotient lane are
mutually equivalent:

* metric-tail control,
* ordinary local convergence control,
* stable half-radius packet control.

This is a small triangular index theorem.  It is deliberately only an
interface-level equivalence between already-proved control predicates, not a
promotion to a Mathlib `MetricSpace`, normed group, Hilbert completion, or
closed-operator theorem. -/
def r2mPrefixQuotientCompletionControlEquivalenceTriangle
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) : Prop :=
  (r2mPrefixQuotientMetricTailControlled N u ↔
    r2mPrefixQuotientLocalConvergenceControlled N u) ∧
  (r2mPrefixQuotientMetricTailControlled N u ↔
    ∀ ε : ℝ, 0 < ε →
      ∃ M : ℕ, r2mPrefixQuotientStableHalfRadiusPacket N u ε M) ∧
  (r2mPrefixQuotientLocalConvergenceControlled N u ↔
    ∀ ε : ℝ, 0 < ε →
      ∃ M : ℕ, r2mPrefixQuotientStableHalfRadiusPacket N u ε M)

/-- The completion-control equivalence triangle holds for every prefix quotient
sequence. -/
theorem r2m_prefix_quotient_completion_control_equivalence_triangle
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) :
    r2mPrefixQuotientCompletionControlEquivalenceTriangle N u := by
  exact ⟨
    r2m_prefix_quotient_metric_tail_controlled_iff_local_convergence_controlled N u,
    r2m_prefix_quotient_metric_tail_controlled_iff_stable_half_radius_packets N u,
    r2m_prefix_quotient_local_convergence_controlled_iff_stable_half_radius_packets N u⟩

/-- Metric-tail control can be transported to ordinary local convergence through
the equivalence triangle. -/
theorem r2m_prefix_quotient_completion_triangle_metric_to_local
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (h : r2mPrefixQuotientMetricTailControlled N u) :
    r2mPrefixQuotientLocalConvergenceControlled N u := by
  exact (r2m_prefix_quotient_completion_control_equivalence_triangle N u).1.mp h

/-- Ordinary local convergence can be transported back to metric-tail control
through the equivalence triangle. -/
theorem r2m_prefix_quotient_completion_triangle_local_to_metric
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (h : r2mPrefixQuotientLocalConvergenceControlled N u) :
    r2mPrefixQuotientMetricTailControlled N u := by
  exact (r2m_prefix_quotient_completion_control_equivalence_triangle N u).1.mpr h

/-- Metric-tail control can be transported to stable half-radius packets through
the equivalence triangle. -/
theorem r2m_prefix_quotient_completion_triangle_metric_to_stable_half_radius
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (h : r2mPrefixQuotientMetricTailControlled N u) :
    ∀ ε : ℝ, 0 < ε →
      ∃ M : ℕ, r2mPrefixQuotientStableHalfRadiusPacket N u ε M := by
  exact (r2m_prefix_quotient_completion_control_equivalence_triangle N u).2.1.mp h

/-- Stable half-radius packets can be transported back to metric-tail control
through the equivalence triangle. -/
theorem r2m_prefix_quotient_completion_triangle_stable_half_radius_to_metric
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (h : ∀ ε : ℝ, 0 < ε →
      ∃ M : ℕ, r2mPrefixQuotientStableHalfRadiusPacket N u ε M) :
    r2mPrefixQuotientMetricTailControlled N u := by
  exact (r2m_prefix_quotient_completion_control_equivalence_triangle N u).2.1.mpr h

/-- Local convergence can be transported to stable half-radius packets through
the equivalence triangle. -/
theorem r2m_prefix_quotient_completion_triangle_local_to_stable_half_radius
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (h : r2mPrefixQuotientLocalConvergenceControlled N u) :
    ∀ ε : ℝ, 0 < ε →
      ∃ M : ℕ, r2mPrefixQuotientStableHalfRadiusPacket N u ε M := by
  exact (r2m_prefix_quotient_completion_control_equivalence_triangle N u).2.2.mp h

/-- Stable half-radius packets can be transported back to ordinary local
convergence through the equivalence triangle. -/
theorem r2m_prefix_quotient_completion_triangle_stable_half_radius_to_local
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (h : ∀ ε : ℝ, 0 < ε →
      ∃ M : ℕ, r2mPrefixQuotientStableHalfRadiusPacket N u ε M) :
    r2mPrefixQuotientLocalConvergenceControlled N u := by
  exact (r2m_prefix_quotient_completion_control_equivalence_triangle N u).2.2.mpr h

/-- Readiness surface for the completion-control equivalence triangle. -/
def r2mPrefixQuotientCompletionControlEquivalenceTriangleReady : Prop :=
  r2mPrefixQuotientCompletionStableHalfRadiusLocalBridgeReady ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientCompletionControlEquivalenceTriangle N u) ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientMetricTailControlled N u →
      r2mPrefixQuotientLocalConvergenceControlled N u) ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientLocalConvergenceControlled N u →
      r2mPrefixQuotientMetricTailControlled N u) ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientMetricTailControlled N u →
      ∀ ε : ℝ, 0 < ε →
        ∃ M : ℕ, r2mPrefixQuotientStableHalfRadiusPacket N u ε M) ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N),
    (∀ ε : ℝ, 0 < ε →
      ∃ M : ℕ, r2mPrefixQuotientStableHalfRadiusPacket N u ε M) →
        r2mPrefixQuotientMetricTailControlled N u) ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientLocalConvergenceControlled N u →
      ∀ ε : ℝ, 0 < ε →
        ∃ M : ℕ, r2mPrefixQuotientStableHalfRadiusPacket N u ε M) ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N),
    (∀ ε : ℝ, 0 < ε →
      ∃ M : ℕ, r2mPrefixQuotientStableHalfRadiusPacket N u ε M) →
        r2mPrefixQuotientLocalConvergenceControlled N u)

/-- The completion-control equivalence triangle is ready. -/
theorem r2m_prefix_quotient_completion_control_equivalence_triangle_ready :
    r2mPrefixQuotientCompletionControlEquivalenceTriangleReady := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact r2m_prefix_quotient_completion_stable_half_radius_local_bridge_ready
  · intro N u
    exact r2m_prefix_quotient_completion_control_equivalence_triangle N u
  · intro N u h
    exact r2m_prefix_quotient_completion_triangle_metric_to_local N u h
  · intro N u h
    exact r2m_prefix_quotient_completion_triangle_local_to_metric N u h
  · intro N u h
    exact r2m_prefix_quotient_completion_triangle_metric_to_stable_half_radius N u h
  · intro N u h
    exact r2m_prefix_quotient_completion_triangle_stable_half_radius_to_metric N u h
  · intro N u h
    exact r2m_prefix_quotient_completion_triangle_local_to_stable_half_radius N u h
  · intro N u h
    exact r2m_prefix_quotient_completion_triangle_stable_half_radius_to_local N u h

/-- Boundary marker for the completion-control equivalence triangle leaf. -/
def r2mPrefixQuotientCompletionControlEquivalenceTriangleBoundaryHeld : Prop :=
  r2mPrefixQuotientCompletionControlEquivalenceTriangleReady ∧
  r2mPrefixQuotientCompletionStableHalfRadiusLocalBridgeBoundaryHeld

/-- Boundary theorem for the completion-control equivalence triangle leaf. -/
theorem r2m_prefix_quotient_completion_control_equivalence_triangle_boundary_held :
    r2mPrefixQuotientCompletionControlEquivalenceTriangleBoundaryHeld := by
  exact ⟨
    r2m_prefix_quotient_completion_control_equivalence_triangle_ready,
    r2m_prefix_quotient_completion_stable_half_radius_local_bridge_boundary_held⟩

end

end MathlibAnalytic
end MGAP4D
