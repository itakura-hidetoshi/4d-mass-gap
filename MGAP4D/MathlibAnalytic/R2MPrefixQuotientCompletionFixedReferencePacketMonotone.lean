import MGAP4D.MathlibAnalytic.R2MPrefixQuotientCompletionFixedReferencePacket

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Fixed-reference norm packets are monotone in the tolerance.  The reference
index `M` is not changed. -/
theorem r2m_prefix_quotient_fixed_reference_norm_packet_mono
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) (ε δ : ℝ) (M : ℕ)
    (hεδ : ε ≤ δ)
    (h : r2mPrefixQuotientFixedReferenceNormPacket N u ε M) :
    r2mPrefixQuotientFixedReferenceNormPacket N u δ M := by
  rcases h with ⟨hε, hM⟩
  refine ⟨lt_of_lt_of_le hε hεδ, ?_⟩
  intro n hn
  exact le_trans (hM n hn) hεδ

/-- Fixed-reference metric packets are monotone in the tolerance. -/
theorem r2m_prefix_quotient_fixed_reference_metric_packet_mono
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) (ε δ : ℝ) (M : ℕ)
    (hεδ : ε ≤ δ)
    (h : r2mPrefixQuotientFixedReferenceMetricPacket N u ε M) :
    r2mPrefixQuotientFixedReferenceMetricPacket N u δ M := by
  rcases h with ⟨hε, hM⟩
  refine ⟨lt_of_lt_of_le hε hεδ, ?_⟩
  intro n hn
  exact le_trans (hM n hn) hεδ

/-- Fixed-reference paired packets are monotone in the tolerance, preserving the
same center and reference index. -/
theorem r2m_prefix_quotient_fixed_reference_packet_mono
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) (ε δ : ℝ) (M : ℕ)
    (hεδ : ε ≤ δ)
    (h : r2mPrefixQuotientFixedReferencePacket N u ε M) :
    r2mPrefixQuotientFixedReferencePacket N u δ M := by
  exact ⟨
    r2m_prefix_quotient_fixed_reference_metric_packet_mono N u ε δ M hεδ h.1,
    r2m_prefix_quotient_fixed_reference_norm_packet_mono N u ε δ M hεδ h.2⟩

/-- Metric-tail control supplies a fixed-reference paired packet at half of any
positive tolerance. -/
theorem r2m_prefix_quotient_metric_tail_controlled_exists_fixed_reference_packet_half
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (h : r2mPrefixQuotientMetricTailControlled N u)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, r2mPrefixQuotientFixedReferencePacket N u (ε / 2) M := by
  have hhalf : 0 < ε / 2 := half_pos hε
  exact r2m_prefix_quotient_metric_tail_controlled_exists_fixed_reference_packet N u h (ε / 2) hhalf

/-- A half-tolerance fixed-reference packet upgrades to the original tolerance
without moving its reference index. -/
theorem r2m_prefix_quotient_fixed_reference_packet_half_to_full
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) (ε : ℝ) (M : ℕ)
    (hε : 0 < ε)
    (h : r2mPrefixQuotientFixedReferencePacket N u (ε / 2) M) :
    r2mPrefixQuotientFixedReferencePacket N u ε M := by
  have hhalf_le : ε / 2 ≤ ε := by linarith
  exact r2m_prefix_quotient_fixed_reference_packet_mono N u (ε / 2) ε M hhalf_le h

/-- Metric-tail control supplies a full-tolerance packet through the half-step
route.  This is a useful witness shape when downstream estimates consume half
of the budget and then enlarge back to `ε`. -/
theorem r2m_prefix_quotient_metric_tail_controlled_exists_fixed_reference_packet_via_half
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (h : r2mPrefixQuotientMetricTailControlled N u)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, r2mPrefixQuotientFixedReferencePacket N u ε M := by
  rcases r2m_prefix_quotient_metric_tail_controlled_exists_fixed_reference_packet_half N u h ε hε with ⟨M, hM⟩
  exact ⟨M, r2m_prefix_quotient_fixed_reference_packet_half_to_full N u ε M hε hM⟩

/-- Completion fixed-reference packet monotonicity surface: the fixed-reference
packet API is stable under tolerance enlargement and supports the standard
half-ε budget split used in completion arguments. -/
def r2mPrefixQuotientCompletionFixedReferencePacketMonotoneReady : Prop :=
  r2mPrefixQuotientCompletionFixedReferencePacketReady ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) (ε δ : ℝ) (M : ℕ),
    ε ≤ δ →
    r2mPrefixQuotientFixedReferencePacket N u ε M →
    r2mPrefixQuotientFixedReferencePacket N u δ M) ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
      (h : r2mPrefixQuotientMetricTailControlled N u) (ε : ℝ),
    0 < ε → ∃ M : ℕ, r2mPrefixQuotientFixedReferencePacket N u (ε / 2) M) ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
      (h : r2mPrefixQuotientMetricTailControlled N u) (ε : ℝ),
    0 < ε → ∃ M : ℕ, r2mPrefixQuotientFixedReferencePacket N u ε M)

/-- The quotient completion fixed-reference packet monotonicity surface is ready. -/
theorem r2m_prefix_quotient_completion_fixed_reference_packet_monotone_ready :
    r2mPrefixQuotientCompletionFixedReferencePacketMonotoneReady := by
  exact ⟨
    r2m_prefix_quotient_completion_fixed_reference_packet_ready,
    r2m_prefix_quotient_fixed_reference_packet_mono,
    r2m_prefix_quotient_metric_tail_controlled_exists_fixed_reference_packet_half,
    r2m_prefix_quotient_metric_tail_controlled_exists_fixed_reference_packet_via_half⟩

/-- Boundary marker: fixed-reference completion packets now support monotone
budget enlargement and half-ε splitting. -/
def r2mPrefixQuotientCompletionFixedReferencePacketMonotoneBoundaryHeld : Prop :=
  r2mPrefixQuotientCompletionFixedReferencePacketMonotoneReady ∧
  True

theorem r2m_prefix_quotient_completion_fixed_reference_packet_monotone_boundary_held :
    r2mPrefixQuotientCompletionFixedReferencePacketMonotoneBoundaryHeld := by
  exact ⟨r2m_prefix_quotient_completion_fixed_reference_packet_monotone_ready, trivial⟩

end

end MathlibAnalytic
end MGAP4D
