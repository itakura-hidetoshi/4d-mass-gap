import MGAP4D.MathlibAnalytic.R2MPrefixQuotientCompletionLocalConvergenceHalfRadiusStability

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A stable half-radius packet packages the completion-facing witness used in
the prefix quotient lane: local convergence at `ε / 2`, pointwise metric/norm
accessors at that half radius, and the reconstructed full-radius metric Cauchy
tail. -/
def r2mPrefixQuotientStableHalfRadiusPacket
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) (ε : ℝ) (M : ℕ) : Prop :=
  r2mPrefixQuotientLocalConvergencePacket N u (ε / 2) M ∧
  (∀ n : ℕ, M ≤ n → dist (u n) (u M) ≤ ε / 2) ∧
  (∀ n : ℕ, M ≤ n → ‖u n - u M‖ ≤ ε / 2) ∧
  (∀ n m : ℕ, M ≤ n → M ≤ m → dist (u n) (u m) ≤ ε)

/-- Metric-tail control produces a stable half-radius packet at every positive
radius. -/
theorem r2m_prefix_quotient_metric_tail_controlled_to_stable_half_radius_packets
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (h : r2mPrefixQuotientMetricTailControlled N u) :
    ∀ ε : ℝ, 0 < ε →
      ∃ M : ℕ, r2mPrefixQuotientStableHalfRadiusPacket N u ε M := by
  intro ε hε
  rcases r2m_prefix_quotient_metric_tail_controlled_exists_stable_half_radius_packet
    N u h ε hε with ⟨M, hM, hdist, hnorm, htail⟩
  exact ⟨M, hM, hdist, hnorm, htail⟩

/-- Stable half-radius packets recover metric-tail control by projecting the
full-radius tail component. -/
theorem r2m_prefix_quotient_stable_half_radius_packets_to_metric_tail_controlled
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (h : ∀ ε : ℝ, 0 < ε →
      ∃ M : ℕ, r2mPrefixQuotientStableHalfRadiusPacket N u ε M) :
    r2mPrefixQuotientMetricTailControlled N u := by
  intro ε hε
  rcases h ε hε with ⟨M, _hM, _hdist, _hnorm, htail⟩
  exact ⟨M, htail⟩

/-- Metric-tail control is equivalent to the existence of stable half-radius
packets at every positive radius. -/
theorem r2m_prefix_quotient_metric_tail_controlled_iff_stable_half_radius_packets
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) :
    r2mPrefixQuotientMetricTailControlled N u ↔
      ∀ ε : ℝ, 0 < ε →
        ∃ M : ℕ, r2mPrefixQuotientStableHalfRadiusPacket N u ε M := by
  constructor
  · intro h
    exact r2m_prefix_quotient_metric_tail_controlled_to_stable_half_radius_packets N u h
  · intro h
    exact r2m_prefix_quotient_stable_half_radius_packets_to_metric_tail_controlled N u h

/-- Stable half-radius packet equivalence surface for the quotient completion
lane.  This is a pure logical repackaging of the half-radius stability leaf: it
exposes the completion-facing packet form without promoting to a Mathlib
`MetricSpace`, normed group, Hilbert completion, or closed-operator theorem. -/
def r2mPrefixQuotientCompletionStableHalfRadiusPacketEquivalenceReady : Prop :=
  r2mPrefixQuotientCompletionLocalConvergenceHalfRadiusStabilityReady ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientMetricTailControlled N u →
      ∀ ε : ℝ, 0 < ε →
        ∃ M : ℕ, r2mPrefixQuotientStableHalfRadiusPacket N u ε M) ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N),
    (∀ ε : ℝ, 0 < ε →
      ∃ M : ℕ, r2mPrefixQuotientStableHalfRadiusPacket N u ε M) →
        r2mPrefixQuotientMetricTailControlled N u) ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientMetricTailControlled N u ↔
      ∀ ε : ℝ, 0 < ε →
        ∃ M : ℕ, r2mPrefixQuotientStableHalfRadiusPacket N u ε M)

/-- The stable half-radius packet equivalence surface is ready. -/
theorem r2m_prefix_quotient_completion_stable_half_radius_packet_equivalence_ready :
    r2mPrefixQuotientCompletionStableHalfRadiusPacketEquivalenceReady := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact r2m_prefix_quotient_completion_local_convergence_half_radius_stability_ready
  · intro N u h ε hε
    exact r2m_prefix_quotient_metric_tail_controlled_to_stable_half_radius_packets N u h ε hε
  · intro N u h
    exact r2m_prefix_quotient_stable_half_radius_packets_to_metric_tail_controlled N u h
  · intro N u
    exact r2m_prefix_quotient_metric_tail_controlled_iff_stable_half_radius_packets N u

/-- Boundary marker for the stable half-radius packet equivalence leaf. -/
def r2mPrefixQuotientCompletionStableHalfRadiusPacketEquivalenceBoundaryHeld : Prop :=
  r2mPrefixQuotientCompletionStableHalfRadiusPacketEquivalenceReady ∧
  r2mPrefixQuotientCompletionLocalConvergenceHalfRadiusStabilityBoundaryHeld

/-- Boundary theorem for the stable half-radius packet equivalence leaf. -/
theorem r2m_prefix_quotient_completion_stable_half_radius_packet_equivalence_boundary_held :
    r2mPrefixQuotientCompletionStableHalfRadiusPacketEquivalenceBoundaryHeld := by
  exact ⟨
    r2m_prefix_quotient_completion_stable_half_radius_packet_equivalence_ready,
    r2m_prefix_quotient_completion_local_convergence_half_radius_stability_boundary_held⟩

end

end MathlibAnalytic
end MGAP4D
