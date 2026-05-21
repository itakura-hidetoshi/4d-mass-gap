import MGAP4D.MathlibAnalytic.R2MPrefixQuotientCompletionFixedReferenceWitness

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A local convergence packet around a reference tail point `u M`: every later
point is within `ε` of `u M` both metrically and in the quotient norm of the
difference.  This is the small consumable shape for completion and closed-graph
limit arguments. -/
def r2mPrefixQuotientLocalConvergencePacket
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) (ε : ℝ) (M : ℕ) : Prop :=
  0 < ε ∧ ∀ n : ℕ, M ≤ n →
    dist (u n) (u M) ≤ ε ∧ ‖u n - u M‖ ≤ ε

/-- A fixed-reference packet canonically induces the corresponding local
convergence packet at the same reference index. -/
theorem r2m_prefix_quotient_fixed_reference_packet_to_local_convergence_packet
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) (ε : ℝ) (M : ℕ)
    (h : r2mPrefixQuotientFixedReferencePacket N u ε M) :
    r2mPrefixQuotientLocalConvergencePacket N u ε M := by
  rcases h with ⟨_hmetric, hnorm⟩
  rcases hnorm with ⟨hε, hM⟩
  refine ⟨hε, ?_⟩
  intro n hn
  have hnorm_le : ‖u n - u M‖ ≤ ε := hM n hn
  have hdist_le : dist (u n) (u M) ≤ ε := by
    rw [r2m_prefix_quotient_dist_eq_norm_sub_typeclass N (u n) (u M)]
    exact hnorm_le
  exact ⟨hdist_le, hnorm_le⟩

/-- A fixed-reference witness induces an existential local convergence packet. -/
theorem r2m_prefix_quotient_fixed_reference_witness_to_local_convergence_packet
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) (ε : ℝ)
    (h : r2mPrefixQuotientFixedReferenceWitness N u ε) :
    ∃ M : ℕ, r2mPrefixQuotientLocalConvergencePacket N u ε M := by
  rcases h with ⟨M, hM⟩
  exact ⟨M, r2m_prefix_quotient_fixed_reference_packet_to_local_convergence_packet N u ε M hM⟩

/-- Local convergence packets are monotone in the tolerance while preserving the
same reference index. -/
theorem r2m_prefix_quotient_local_convergence_packet_mono
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) (ε δ : ℝ) (M : ℕ)
    (hεδ : ε ≤ δ)
    (h : r2mPrefixQuotientLocalConvergencePacket N u ε M) :
    r2mPrefixQuotientLocalConvergencePacket N u δ M := by
  rcases h with ⟨hε, hM⟩
  refine ⟨lt_of_lt_of_le hε hεδ, ?_⟩
  intro n hn
  exact ⟨le_trans (hM n hn).1 hεδ, le_trans (hM n hn).2 hεδ⟩

/-- Local convergence controlled sequence: every positive tolerance admits a
reference tail point whose whole tail is locally contained around that point. -/
def r2mPrefixQuotientLocalConvergenceControlled
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ M : ℕ,
    r2mPrefixQuotientLocalConvergencePacket N u ε M

/-- Metric-tail control supplies local convergence packets for every positive
tolerance. -/
theorem r2m_prefix_quotient_metric_tail_controlled_to_local_convergence_controlled
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (h : r2mPrefixQuotientMetricTailControlled N u) :
    r2mPrefixQuotientLocalConvergenceControlled N u := by
  intro ε hε
  exact r2m_prefix_quotient_fixed_reference_witness_to_local_convergence_packet N u ε
    (r2m_prefix_quotient_metric_tail_controlled_exists_fixed_reference_witness N u h ε hε)

/-- Metric-tail control supplies a half-tolerance local convergence packet. -/
theorem r2m_prefix_quotient_metric_tail_controlled_exists_local_convergence_packet_half
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (h : r2mPrefixQuotientMetricTailControlled N u)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, r2mPrefixQuotientLocalConvergencePacket N u (ε / 2) M := by
  exact r2m_prefix_quotient_fixed_reference_witness_to_local_convergence_packet N u (ε / 2)
    (r2m_prefix_quotient_metric_tail_controlled_exists_fixed_reference_witness_half N u h ε hε)

/-- A half-tolerance local convergence packet enlarges to the full tolerance at
the same reference point. -/
theorem r2m_prefix_quotient_local_convergence_packet_half_to_full
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) (ε : ℝ) (M : ℕ)
    (hε : 0 < ε)
    (h : r2mPrefixQuotientLocalConvergencePacket N u (ε / 2) M) :
    r2mPrefixQuotientLocalConvergencePacket N u ε M := by
  have hhalf_le : ε / 2 ≤ ε := by linarith
  exact r2m_prefix_quotient_local_convergence_packet_mono N u (ε / 2) ε M hhalf_le h

/-- Completion local convergence surface: fixed-reference witnesses now feed a
same-center local convergence packet containing both the metric and norm views. -/
def r2mPrefixQuotientCompletionLocalConvergencePacketReady : Prop :=
  r2mPrefixQuotientCompletionFixedReferenceWitnessReady ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) (ε : ℝ) (M : ℕ),
    r2mPrefixQuotientFixedReferencePacket N u ε M →
    r2mPrefixQuotientLocalConvergencePacket N u ε M) ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) (ε : ℝ),
    r2mPrefixQuotientFixedReferenceWitness N u ε →
    ∃ M : ℕ, r2mPrefixQuotientLocalConvergencePacket N u ε M) ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientMetricTailControlled N u →
    r2mPrefixQuotientLocalConvergenceControlled N u) ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
      (h : r2mPrefixQuotientMetricTailControlled N u) (ε : ℝ),
    0 < ε → ∃ M : ℕ, r2mPrefixQuotientLocalConvergencePacket N u (ε / 2) M)

/-- The quotient completion local convergence packet surface is ready. -/
theorem r2m_prefix_quotient_completion_local_convergence_packet_ready :
    r2mPrefixQuotientCompletionLocalConvergencePacketReady := by
  exact ⟨
    r2m_prefix_quotient_completion_fixed_reference_witness_ready,
    r2m_prefix_quotient_fixed_reference_packet_to_local_convergence_packet,
    r2m_prefix_quotient_fixed_reference_witness_to_local_convergence_packet,
    r2m_prefix_quotient_metric_tail_controlled_to_local_convergence_controlled,
    r2m_prefix_quotient_metric_tail_controlled_exists_local_convergence_packet_half⟩

/-- Boundary marker: quotient completion now has local convergence packets that
carry the metric and norm views at the same tail reference point. -/
def r2mPrefixQuotientCompletionLocalConvergencePacketBoundaryHeld : Prop :=
  r2mPrefixQuotientCompletionLocalConvergencePacketReady ∧
  True

theorem r2m_prefix_quotient_completion_local_convergence_packet_boundary_held :
    r2mPrefixQuotientCompletionLocalConvergencePacketBoundaryHeld := by
  exact ⟨r2m_prefix_quotient_completion_local_convergence_packet_ready, trivial⟩

end

end MathlibAnalytic
end MGAP4D
