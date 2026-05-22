import MGAP4D.MathlibAnalytic.R2MPrefixQuotientCompletionLocalConvergenceStability

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Half-radius local convergence gives the full-radius metric tail estimate.

This is the stability-side replay of the Cauchy bridge: first use the generic
`ε + ε` tail estimate from the local-convergence stability surface at radius
`ε / 2`, then close the arithmetic identity by `ring`. -/
theorem r2m_prefix_quotient_local_convergence_packet_half_radius_to_metric_tail_at
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) (ε : ℝ) (M : ℕ)
    (h : r2mPrefixQuotientLocalConvergencePacket N u (ε / 2) M) :
    ∀ n m : ℕ, M ≤ n → M ≤ m → dist (u n) (u m) ≤ ε := by
  intro n m hn hm
  have htwo : dist (u n) (u m) ≤ ε / 2 + ε / 2 :=
    r2m_prefix_quotient_local_convergence_packet_to_metric_two_radius_tail_at
      N u (ε / 2) M h n m hn hm
  calc
    dist (u n) (u m) ≤ ε / 2 + ε / 2 := htwo
    _ = ε := by ring

/-- Half-radius metric accessor from a local-convergence packet. -/
theorem r2m_prefix_quotient_local_convergence_packet_half_radius_dist_at
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) (ε : ℝ) (M n : ℕ)
    (h : r2mPrefixQuotientLocalConvergencePacket N u (ε / 2) M) (hn : M ≤ n) :
    dist (u n) (u M) ≤ ε / 2 := by
  exact r2m_prefix_quotient_local_convergence_packet_dist_at N u (ε / 2) M n h hn

/-- Half-radius norm accessor from a local-convergence packet. -/
theorem r2m_prefix_quotient_local_convergence_packet_half_radius_norm_at
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) (ε : ℝ) (M n : ℕ)
    (h : r2mPrefixQuotientLocalConvergencePacket N u (ε / 2) M) (hn : M ≤ n) :
    ‖u n - u M‖ ≤ ε / 2 := by
  exact r2m_prefix_quotient_local_convergence_packet_norm_at N u (ε / 2) M n h hn

/-- A metric-tail controlled sequence admits a stable half-radius local packet:
pointwise metric and norm accessors are available at radius `ε / 2`, and the
same reference point reconstructs the full-radius metric Cauchy tail. -/
theorem r2m_prefix_quotient_metric_tail_controlled_exists_stable_half_radius_packet
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (h : r2mPrefixQuotientMetricTailControlled N u)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ,
      r2mPrefixQuotientLocalConvergencePacket N u (ε / 2) M ∧
      (∀ n : ℕ, M ≤ n → dist (u n) (u M) ≤ ε / 2) ∧
      (∀ n : ℕ, M ≤ n → ‖u n - u M‖ ≤ ε / 2) ∧
      (∀ n m : ℕ, M ≤ n → M ≤ m → dist (u n) (u m) ≤ ε) := by
  rcases r2m_prefix_quotient_metric_tail_controlled_exists_local_packet_reconstructing_tail
    N u h ε hε with ⟨M, hM, htail⟩
  exact ⟨M, hM,
    (fun n hn =>
      r2m_prefix_quotient_local_convergence_packet_half_radius_dist_at N u ε M n hM hn),
    (fun n hn =>
      r2m_prefix_quotient_local_convergence_packet_half_radius_norm_at N u ε M n hM hn),
    htail⟩

/-- Half-radius stability surface: local convergence at `ε / 2` is now exposed
as a reusable full-radius Cauchy-tail estimate, with pointwise metric and norm
accessors retained at the half radius. -/
def r2mPrefixQuotientCompletionLocalConvergenceHalfRadiusStabilityReady : Prop :=
  r2mPrefixQuotientCompletionLocalConvergenceStabilityReady ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
      (ε : ℝ) (M : ℕ),
    r2mPrefixQuotientLocalConvergencePacket N u (ε / 2) M →
    ∀ n m : ℕ, M ≤ n → M ≤ m → dist (u n) (u m) ≤ ε) ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
      (_h : r2mPrefixQuotientMetricTailControlled N u) (ε : ℝ),
    0 < ε → ∃ M : ℕ,
      r2mPrefixQuotientLocalConvergencePacket N u (ε / 2) M ∧
      (∀ n : ℕ, M ≤ n → dist (u n) (u M) ≤ ε / 2) ∧
      (∀ n : ℕ, M ≤ n → ‖u n - u M‖ ≤ ε / 2) ∧
      (∀ n m : ℕ, M ≤ n → M ≤ m → dist (u n) (u m) ≤ ε))

theorem r2m_prefix_quotient_completion_local_convergence_half_radius_stability_ready :
    r2mPrefixQuotientCompletionLocalConvergenceHalfRadiusStabilityReady := by
  refine ⟨?_, ?_, ?_⟩
  · exact r2m_prefix_quotient_completion_local_convergence_stability_ready
  · intro N u ε M h n m hn hm
    exact r2m_prefix_quotient_local_convergence_packet_half_radius_to_metric_tail_at
      N u ε M h n m hn hm
  · intro N u h ε hε
    exact r2m_prefix_quotient_metric_tail_controlled_exists_stable_half_radius_packet
      N u h ε hε

/-- Boundary marker for the half-radius stability replay. -/
def r2mPrefixQuotientCompletionLocalConvergenceHalfRadiusStabilityBoundaryHeld : Prop :=
  r2mPrefixQuotientCompletionLocalConvergenceHalfRadiusStabilityReady ∧
  r2mPrefixQuotientCompletionLocalConvergenceStabilityBoundaryHeld

theorem r2m_prefix_quotient_completion_local_convergence_half_radius_stability_boundary_held :
    r2mPrefixQuotientCompletionLocalConvergenceHalfRadiusStabilityBoundaryHeld := by
  exact ⟨
    r2m_prefix_quotient_completion_local_convergence_half_radius_stability_ready,
    r2m_prefix_quotient_completion_local_convergence_stability_boundary_held⟩

end

end MathlibAnalytic
end MGAP4D
