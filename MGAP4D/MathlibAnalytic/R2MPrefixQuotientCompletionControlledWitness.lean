import MGAP4D.MathlibAnalytic.R2MPrefixQuotientCompletionLocalConvergenceStability

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Controlled local convergence yields a single half-radius local packet whose
center simultaneously exposes pointwise metric control, pointwise norm control,
and the reconstructed full-radius Cauchy tail. -/
theorem r2m_prefix_quotient_local_convergence_controlled_exists_stable_half_witness
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (h : r2mPrefixQuotientLocalConvergenceControlled N u)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ,
      r2mPrefixQuotientLocalConvergencePacket N u (ε / 2) M ∧
      (∀ n : ℕ, M ≤ n → dist (u n) (u M) ≤ ε / 2) ∧
      (∀ n : ℕ, M ≤ n → ‖u n - u M‖ ≤ ε / 2) ∧
      (∀ n m : ℕ, M ≤ n → M ≤ m → dist (u n) (u m) ≤ ε) := by
  have hhalf : 0 < ε / 2 := half_pos hε
  rcases h (ε / 2) hhalf with ⟨M, hM⟩
  refine ⟨M, hM, ?_, ?_, ?_⟩
  · intro n hn
    exact r2m_prefix_quotient_local_convergence_packet_dist_at N u (ε / 2) M n hM hn
  · intro n hn
    exact r2m_prefix_quotient_local_convergence_packet_norm_at N u (ε / 2) M n hM hn
  · exact r2m_prefix_quotient_local_convergence_packet_half_to_metric_tail_at N u ε M hM

/-- The same witness extraction is available from metric-tail control by first
using the established equivalence with local convergence. -/
theorem r2m_prefix_quotient_metric_tail_controlled_exists_stable_half_witness
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (h : r2mPrefixQuotientMetricTailControlled N u)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ,
      r2mPrefixQuotientLocalConvergencePacket N u (ε / 2) M ∧
      (∀ n : ℕ, M ≤ n → dist (u n) (u M) ≤ ε / 2) ∧
      (∀ n : ℕ, M ≤ n → ‖u n - u M‖ ≤ ε / 2) ∧
      (∀ n m : ℕ, M ≤ n → M ≤ m → dist (u n) (u m) ≤ ε) := by
  have hlocal : r2mPrefixQuotientLocalConvergenceControlled N u :=
    (r2m_prefix_quotient_metric_tail_controlled_iff_local_convergence_controlled N u).1 h
  exact r2m_prefix_quotient_local_convergence_controlled_exists_stable_half_witness N u hlocal ε hε

/-- Controlled-witness completion surface: both local-convergence control and
metric-tail control now produce the same stable half-radius witness packet. -/
def r2mPrefixQuotientCompletionControlledWitnessReady : Prop :=
  r2mPrefixQuotientCompletionLocalConvergenceStabilityReady ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
      (h : r2mPrefixQuotientLocalConvergenceControlled N u)
      (ε : ℝ),
    0 < ε → ∃ M : ℕ,
      r2mPrefixQuotientLocalConvergencePacket N u (ε / 2) M ∧
      (∀ n : ℕ, M ≤ n → dist (u n) (u M) ≤ ε / 2) ∧
      (∀ n : ℕ, M ≤ n → ‖u n - u M‖ ≤ ε / 2) ∧
      (∀ n m : ℕ, M ≤ n → M ≤ m → dist (u n) (u m) ≤ ε)) ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
      (h : r2mPrefixQuotientMetricTailControlled N u)
      (ε : ℝ),
    0 < ε → ∃ M : ℕ,
      r2mPrefixQuotientLocalConvergencePacket N u (ε / 2) M ∧
      (∀ n : ℕ, M ≤ n → dist (u n) (u M) ≤ ε / 2) ∧
      (∀ n : ℕ, M ≤ n → ‖u n - u M‖ ≤ ε / 2) ∧
      (∀ n m : ℕ, M ≤ n → M ≤ m → dist (u n) (u m) ≤ ε))

theorem r2m_prefix_quotient_completion_controlled_witness_ready :
    r2mPrefixQuotientCompletionControlledWitnessReady := by
  exact ⟨
    r2m_prefix_quotient_completion_local_convergence_stability_ready,
    r2m_prefix_quotient_local_convergence_controlled_exists_stable_half_witness,
    r2m_prefix_quotient_metric_tail_controlled_exists_stable_half_witness⟩

/-- Boundary marker: controlled sequences now admit stable half-radius witness
packets without promoting the quotient to a completion or typeclass metric. -/
def r2mPrefixQuotientCompletionControlledWitnessBoundaryHeld : Prop :=
  r2mPrefixQuotientCompletionControlledWitnessReady ∧
  r2mPrefixQuotientCompletionLocalConvergenceStabilityBoundaryHeld

theorem r2m_prefix_quotient_completion_controlled_witness_boundary_held :
    r2mPrefixQuotientCompletionControlledWitnessBoundaryHeld := by
  exact ⟨
    r2m_prefix_quotient_completion_controlled_witness_ready,
    r2m_prefix_quotient_completion_local_convergence_stability_boundary_held⟩

end

end MathlibAnalytic
end MGAP4D
