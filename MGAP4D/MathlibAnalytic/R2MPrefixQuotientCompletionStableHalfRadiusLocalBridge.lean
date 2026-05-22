import MGAP4D.MathlibAnalytic.R2MPrefixQuotientCompletionStableHalfRadiusPacketEquivalence

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A stable half-radius packet upgrades to the ordinary full-radius local
convergence packet at the same reference point.  Positivity of the full radius is
recovered from the half-radius local packet, and the radius monotonicity is the
existing local-convergence packet monotonicity theorem. -/
theorem r2m_prefix_quotient_stable_half_radius_packet_to_local_convergence_packet
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) (ε : ℝ) (M : ℕ)
    (h : r2mPrefixQuotientStableHalfRadiusPacket N u ε M) :
    r2mPrefixQuotientLocalConvergencePacket N u ε M := by
  rcases h with ⟨hlocal, _hdist, _hnorm, _htail⟩
  have hhalf_le : ε / 2 ≤ ε := by
    linarith [hlocal.1]
  exact r2m_prefix_quotient_local_convergence_packet_mono
    N u (ε / 2) ε M hhalf_le hlocal

/-- Stable half-radius packets for every positive radius imply ordinary local
convergence control. -/
theorem r2m_prefix_quotient_stable_half_radius_packets_to_local_convergence_controlled
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (h : ∀ ε : ℝ, 0 < ε →
      ∃ M : ℕ, r2mPrefixQuotientStableHalfRadiusPacket N u ε M) :
    r2mPrefixQuotientLocalConvergenceControlled N u := by
  intro ε hε
  rcases h ε hε with ⟨M, hM⟩
  exact ⟨M,
    r2m_prefix_quotient_stable_half_radius_packet_to_local_convergence_packet
      N u ε M hM⟩

/-- Ordinary local convergence control implies stable half-radius packets for
every positive radius, by first passing through the metric-tail/Cauchy bridge. -/
theorem r2m_prefix_quotient_local_convergence_controlled_to_stable_half_radius_packets
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (h : r2mPrefixQuotientLocalConvergenceControlled N u) :
    ∀ ε : ℝ, 0 < ε →
      ∃ M : ℕ, r2mPrefixQuotientStableHalfRadiusPacket N u ε M := by
  have htail : r2mPrefixQuotientMetricTailControlled N u :=
    r2m_prefix_quotient_local_convergence_controlled_to_metric_tail_controlled N u h
  exact r2m_prefix_quotient_metric_tail_controlled_to_stable_half_radius_packets N u htail

/-- Ordinary local convergence control is equivalent to the stable half-radius
packet formulation. -/
theorem r2m_prefix_quotient_local_convergence_controlled_iff_stable_half_radius_packets
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) :
    r2mPrefixQuotientLocalConvergenceControlled N u ↔
      ∀ ε : ℝ, 0 < ε →
        ∃ M : ℕ, r2mPrefixQuotientStableHalfRadiusPacket N u ε M := by
  constructor
  · intro h
    exact r2m_prefix_quotient_local_convergence_controlled_to_stable_half_radius_packets N u h
  · intro h
    exact r2m_prefix_quotient_stable_half_radius_packets_to_local_convergence_controlled N u h

/-- Stable half-radius/local bridge surface.  This closes the equivalence between
ordinary local convergence control and the completion-facing stable half-radius
packet formulation, without promoting the quotient surface to a Mathlib metric
or normed typeclass instance. -/
def r2mPrefixQuotientCompletionStableHalfRadiusLocalBridgeReady : Prop :=
  r2mPrefixQuotientCompletionStableHalfRadiusPacketEquivalenceReady ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
      (ε : ℝ) (M : ℕ),
    r2mPrefixQuotientStableHalfRadiusPacket N u ε M →
      r2mPrefixQuotientLocalConvergencePacket N u ε M) ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N),
    (∀ ε : ℝ, 0 < ε →
      ∃ M : ℕ, r2mPrefixQuotientStableHalfRadiusPacket N u ε M) →
        r2mPrefixQuotientLocalConvergenceControlled N u) ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientLocalConvergenceControlled N u →
      ∀ ε : ℝ, 0 < ε →
        ∃ M : ℕ, r2mPrefixQuotientStableHalfRadiusPacket N u ε M) ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientLocalConvergenceControlled N u ↔
      ∀ ε : ℝ, 0 < ε →
        ∃ M : ℕ, r2mPrefixQuotientStableHalfRadiusPacket N u ε M)

/-- The stable half-radius/local bridge surface is ready. -/
theorem r2m_prefix_quotient_completion_stable_half_radius_local_bridge_ready :
    r2mPrefixQuotientCompletionStableHalfRadiusLocalBridgeReady := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact r2m_prefix_quotient_completion_stable_half_radius_packet_equivalence_ready
  · intro N u ε M h
    exact r2m_prefix_quotient_stable_half_radius_packet_to_local_convergence_packet
      N u ε M h
  · intro N u h
    exact r2m_prefix_quotient_stable_half_radius_packets_to_local_convergence_controlled
      N u h
  · intro N u h ε hε
    exact r2m_prefix_quotient_local_convergence_controlled_to_stable_half_radius_packets
      N u h ε hε
  · intro N u
    exact r2m_prefix_quotient_local_convergence_controlled_iff_stable_half_radius_packets
      N u

/-- Boundary marker for the stable half-radius/local bridge leaf. -/
def r2mPrefixQuotientCompletionStableHalfRadiusLocalBridgeBoundaryHeld : Prop :=
  r2mPrefixQuotientCompletionStableHalfRadiusLocalBridgeReady ∧
  r2mPrefixQuotientCompletionStableHalfRadiusPacketEquivalenceBoundaryHeld

/-- Boundary theorem for the stable half-radius/local bridge leaf. -/
theorem r2m_prefix_quotient_completion_stable_half_radius_local_bridge_boundary_held :
    r2mPrefixQuotientCompletionStableHalfRadiusLocalBridgeBoundaryHeld := by
  exact ⟨
    r2m_prefix_quotient_completion_stable_half_radius_local_bridge_ready,
    r2m_prefix_quotient_completion_stable_half_radius_packet_equivalence_boundary_held⟩

end

end MathlibAnalytic
end MGAP4D
