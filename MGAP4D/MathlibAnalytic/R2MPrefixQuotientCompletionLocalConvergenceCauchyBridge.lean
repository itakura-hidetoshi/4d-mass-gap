import MGAP4D.MathlibAnalytic.R2MPrefixQuotientCompletionLocalConvergencePacket

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A local convergence packet at half tolerance reconstructs the metric Cauchy
estimate on the tail by the quotient triangle theorem through the same
reference point `u M`. -/
theorem r2m_prefix_quotient_local_convergence_packet_half_to_metric_tail_at
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) (ε : ℝ) (M : ℕ)
    (h : r2mPrefixQuotientLocalConvergencePacket N u (ε / 2) M) :
    ∀ n m : ℕ, M ≤ n → M ≤ m → dist (u n) (u m) ≤ ε := by
  intro n m hn hm
  rcases h with ⟨_hhalf, hM⟩
  have hnM : dist (u n) (u M) ≤ ε / 2 := (hM n hn).1
  have hmM : dist (u m) (u M) ≤ ε / 2 := (hM m hm).1
  have hMm : dist (u M) (u m) ≤ ε / 2 := by
    have hcomm : dist (u M) (u m) = dist (u m) (u M) :=
      r2m_prefix_quotient_dist_comm_typeclass N (u M) (u m)
    rw [hcomm]
    exact hmM
  calc
    dist (u n) (u m) ≤ dist (u n) (u M) + dist (u M) (u m) :=
      r2m_prefix_quotient_dist_triangle_typeclass N (u n) (u M) (u m)
    _ ≤ ε / 2 + ε / 2 := add_le_add hnM hMm
    _ = ε := by ring

/-- Local convergence control reconstructs the usual metric Cauchy-tail control:
choose a half-tolerance local packet and then use the triangle theorem. -/
theorem r2m_prefix_quotient_local_convergence_controlled_to_metric_tail_controlled
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (h : r2mPrefixQuotientLocalConvergenceControlled N u) :
    r2mPrefixQuotientMetricTailControlled N u := by
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  rcases h (ε / 2) hhalf with ⟨M, hM⟩
  exact ⟨M, r2m_prefix_quotient_local_convergence_packet_half_to_metric_tail_at N u ε M hM⟩

/-- Metric-tail control and local convergence control are equivalent.  The
forward direction is the fixed-reference witness construction; the reverse
direction is the quotient triangle theorem through the chosen local reference
point. -/
theorem r2m_prefix_quotient_metric_tail_controlled_iff_local_convergence_controlled
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) :
    r2mPrefixQuotientMetricTailControlled N u ↔
    r2mPrefixQuotientLocalConvergenceControlled N u := by
  constructor
  · intro h
    exact r2m_prefix_quotient_metric_tail_controlled_to_local_convergence_controlled N u h
  · intro h
    exact r2m_prefix_quotient_local_convergence_controlled_to_metric_tail_controlled N u h

/-- A metric-tail sequence admits a local packet at half tolerance whose same
reference point reconstructs the full Cauchy-tail estimate. -/
theorem r2m_prefix_quotient_metric_tail_controlled_exists_local_packet_reconstructing_tail
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (h : r2mPrefixQuotientMetricTailControlled N u)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ,
      r2mPrefixQuotientLocalConvergencePacket N u (ε / 2) M ∧
      (∀ n m : ℕ, M ≤ n → M ≤ m → dist (u n) (u m) ≤ ε) := by
  rcases r2m_prefix_quotient_metric_tail_controlled_exists_local_convergence_packet_half N u h ε hε with
    ⟨M, hM⟩
  exact ⟨M, hM,
    r2m_prefix_quotient_local_convergence_packet_half_to_metric_tail_at N u ε M hM⟩

/-- Completion local-convergence/Cauchy bridge surface: the same-center local
packet is now known to be equivalent to the usual Cauchy-tail view. -/
def r2mPrefixQuotientCompletionLocalConvergenceCauchyBridgeReady : Prop :=
  r2mPrefixQuotientCompletionLocalConvergencePacketReady ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientLocalConvergenceControlled N u →
    r2mPrefixQuotientMetricTailControlled N u) ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientMetricTailControlled N u ↔
    r2mPrefixQuotientLocalConvergenceControlled N u) ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
      (_h : r2mPrefixQuotientMetricTailControlled N u) (ε : ℝ),
    0 < ε → ∃ M : ℕ,
      r2mPrefixQuotientLocalConvergencePacket N u (ε / 2) M ∧
      (∀ n m : ℕ, M ≤ n → M ≤ m → dist (u n) (u m) ≤ ε))

/-- The quotient completion local-convergence/Cauchy bridge surface is ready. -/
theorem r2m_prefix_quotient_completion_local_convergence_cauchy_bridge_ready :
    r2mPrefixQuotientCompletionLocalConvergenceCauchyBridgeReady := by
  exact ⟨
    r2m_prefix_quotient_completion_local_convergence_packet_ready,
    r2m_prefix_quotient_local_convergence_controlled_to_metric_tail_controlled,
    r2m_prefix_quotient_metric_tail_controlled_iff_local_convergence_controlled,
    r2m_prefix_quotient_metric_tail_controlled_exists_local_packet_reconstructing_tail⟩

/-- Boundary marker: local convergence packets and Cauchy-tail estimates are now
interchangeable in the quotient completion lane. -/
def r2mPrefixQuotientCompletionLocalConvergenceCauchyBridgeBoundaryHeld : Prop :=
  r2mPrefixQuotientCompletionLocalConvergenceCauchyBridgeReady ∧
  True

theorem r2m_prefix_quotient_completion_local_convergence_cauchy_bridge_boundary_held :
    r2mPrefixQuotientCompletionLocalConvergenceCauchyBridgeBoundaryHeld := by
  exact ⟨r2m_prefix_quotient_completion_local_convergence_cauchy_bridge_ready, trivial⟩

end

end MathlibAnalytic
end MGAP4D
