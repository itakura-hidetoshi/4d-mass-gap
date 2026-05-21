import MGAP4D.MathlibAnalytic.R2MPrefixQuotientCompletionLocalConvergenceCauchyBridge

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Pointwise metric projection from a local-convergence packet. -/
theorem r2m_prefix_quotient_local_convergence_packet_dist_at
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) (ε : ℝ) (M n : ℕ)
    (h : r2mPrefixQuotientLocalConvergencePacket N u ε M) (hn : M ≤ n) :
    dist (u n) (u M) ≤ ε := by
  exact (h.2 n hn).1

/-- Pointwise norm projection from a local-convergence packet. -/
theorem r2m_prefix_quotient_local_convergence_packet_norm_at
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) (ε : ℝ) (M n : ℕ)
    (h : r2mPrefixQuotientLocalConvergencePacket N u ε M) (hn : M ≤ n) :
    ‖u n - u M‖ ≤ ε := by
  exact (h.2 n hn).2

/-- A local-convergence packet gives a two-radius Cauchy estimate on its tail. -/
theorem r2m_prefix_quotient_local_convergence_packet_to_metric_two_radius_tail_at
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) (ε : ℝ) (M : ℕ)
    (h : r2mPrefixQuotientLocalConvergencePacket N u ε M) :
    ∀ n m : ℕ, M ≤ n → M ≤ m → dist (u n) (u m) ≤ ε + ε := by
  intro n m hn hm
  have hnM : dist (u n) (u M) ≤ ε :=
    r2m_prefix_quotient_local_convergence_packet_dist_at N u ε M n h hn
  have hmM : dist (u m) (u M) ≤ ε :=
    r2m_prefix_quotient_local_convergence_packet_dist_at N u ε M m h hm
  have hMm : dist (u M) (u m) ≤ ε := by
    have hcomm : dist (u M) (u m) = dist (u m) (u M) :=
      r2m_prefix_quotient_dist_comm_typeclass N (u M) (u m)
    rw [hcomm]
    exact hmM
  exact le_trans
    (r2m_prefix_quotient_dist_triangle_typeclass N (u n) (u M) (u m))
    (add_le_add hnM hMm)

/-- Stability packet: local convergence contains pointwise metric/norm accessors
and its tail is controlled at twice the local radius. -/
def r2mPrefixQuotientCompletionLocalConvergenceStabilityReady : Prop :=
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
      (ε : ℝ) (M n : ℕ),
    r2mPrefixQuotientLocalConvergencePacket N u ε M →
    M ≤ n → dist (u n) (u M) ≤ ε) ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
      (ε : ℝ) (M n : ℕ),
    r2mPrefixQuotientLocalConvergencePacket N u ε M →
    M ≤ n → ‖u n - u M‖ ≤ ε) ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
      (ε : ℝ) (M : ℕ),
    r2mPrefixQuotientLocalConvergencePacket N u ε M →
    ∀ n m : ℕ, M ≤ n → M ≤ m → dist (u n) (u m) ≤ ε + ε)

theorem r2m_prefix_quotient_completion_local_convergence_stability_ready :
    r2mPrefixQuotientCompletionLocalConvergenceStabilityReady := by
  refine ⟨?_, ?_, ?_⟩
  · intro N u ε M n h hn
    exact r2m_prefix_quotient_local_convergence_packet_dist_at N u ε M n h hn
  · intro N u ε M n h hn
    exact r2m_prefix_quotient_local_convergence_packet_norm_at N u ε M n h hn
  · intro N u ε M h n m hn hm
    exact r2m_prefix_quotient_local_convergence_packet_to_metric_two_radius_tail_at N u ε M h n m hn hm

/-- Boundary marker for replaying the stability packet as a leaf completion
surface. -/
def r2mPrefixQuotientCompletionLocalConvergenceStabilityBoundaryHeld : Prop :=
  r2mPrefixQuotientCompletionLocalConvergenceStabilityReady ∧
  r2mPrefixQuotientCompletionLocalConvergenceCauchyBridgeBoundaryHeld

theorem r2m_prefix_quotient_completion_local_convergence_stability_boundary_held :
    r2mPrefixQuotientCompletionLocalConvergenceStabilityBoundaryHeld := by
  exact ⟨
    r2m_prefix_quotient_completion_local_convergence_stability_ready,
    r2m_prefix_quotient_completion_local_convergence_cauchy_bridge_boundary_held⟩

end

end MathlibAnalytic
end MGAP4D
