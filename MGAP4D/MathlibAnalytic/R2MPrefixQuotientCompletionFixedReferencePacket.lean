import MGAP4D.MathlibAnalytic.R2MPrefixQuotientCompletionZeroCenteredEquivalence

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A fixed-reference norm packet: for a chosen tolerance `ε` and reference
index `M`, every tail difference from `u M` lies in the ε-ball around zero in
quotient norm.  This is the small, consumable shape for later completion
witnesses. -/
def r2mPrefixQuotientFixedReferenceNormPacket
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) (ε : ℝ) (M : ℕ) : Prop :=
  0 < ε ∧ ∀ n : ℕ, M ≤ n → ‖u n - u M‖ ≤ ε

/-- A fixed-reference metric packet: the same tail reference point, but stated
in the installed metric against zero. -/
def r2mPrefixQuotientFixedReferenceMetricPacket
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) (ε : ℝ) (M : ℕ) : Prop :=
  0 < ε ∧ ∀ n : ℕ, M ≤ n → dist (u n - u M) 0 ≤ ε

/-- A paired fixed-reference packet carrying both metric and norm estimates at
the same reference index. -/
def r2mPrefixQuotientFixedReferencePacket
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) (ε : ℝ) (M : ℕ) : Prop :=
  r2mPrefixQuotientFixedReferenceMetricPacket N u ε M ∧
  r2mPrefixQuotientFixedReferenceNormPacket N u ε M

/-- A norm packet induces its metric packet at the same reference index. -/
theorem r2m_prefix_quotient_fixed_reference_norm_packet_to_metric_packet
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) (ε : ℝ) (M : ℕ)
    (h : r2mPrefixQuotientFixedReferenceNormPacket N u ε M) :
    r2mPrefixQuotientFixedReferenceMetricPacket N u ε M := by
  rcases h with ⟨hε, hM⟩
  refine ⟨hε, ?_⟩
  intro n hn
  have hnorm : ‖u n - u M‖ ≤ ε := hM n hn
  rw [r2m_prefix_quotient_dist_eq_norm_sub_typeclass N (u n - u M) 0]
  simpa using hnorm

/-- A metric packet induces its norm packet at the same reference index. -/
theorem r2m_prefix_quotient_fixed_reference_metric_packet_to_norm_packet
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) (ε : ℝ) (M : ℕ)
    (h : r2mPrefixQuotientFixedReferenceMetricPacket N u ε M) :
    r2mPrefixQuotientFixedReferenceNormPacket N u ε M := by
  rcases h with ⟨hε, hM⟩
  refine ⟨hε, ?_⟩
  intro n hn
  have hdist : dist (u n - u M) 0 ≤ ε := hM n hn
  rw [r2m_prefix_quotient_dist_eq_norm_sub_typeclass N (u n - u M) 0] at hdist
  simpa using hdist

/-- A norm packet canonically packages both metric and norm estimates without
changing the reference index. -/
theorem r2m_prefix_quotient_fixed_reference_norm_packet_to_packet
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) (ε : ℝ) (M : ℕ)
    (h : r2mPrefixQuotientFixedReferenceNormPacket N u ε M) :
    r2mPrefixQuotientFixedReferencePacket N u ε M := by
  exact ⟨
    r2m_prefix_quotient_fixed_reference_norm_packet_to_metric_packet N u ε M h,
    h⟩

/-- Zero-centered norm tube control supplies a fixed-reference norm packet for
every positive tolerance. -/
theorem r2m_prefix_quotient_zero_centered_norm_tube_controlled_exists_fixed_reference_norm_packet
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (h : r2mPrefixQuotientZeroCenteredNormTubeControlled N u)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, r2mPrefixQuotientFixedReferenceNormPacket N u ε M := by
  rcases h ε hε with ⟨M, hM⟩
  exact ⟨M, hε, hM⟩

/-- Zero-centered paired tube control supplies a fixed-reference paired packet
for every positive tolerance. -/
theorem r2m_prefix_quotient_zero_centered_tube_controlled_exists_fixed_reference_packet
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (h : r2mPrefixQuotientZeroCenteredTubeControlled N u)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, r2mPrefixQuotientFixedReferencePacket N u ε M := by
  rcases h ε hε with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  constructor
  · exact ⟨hε, fun n hn => (hM n hn).1⟩
  · exact ⟨hε, fun n hn => (hM n hn).2⟩

/-- Metric-tail control directly supplies a fixed-reference paired packet for
every positive tolerance. -/
theorem r2m_prefix_quotient_metric_tail_controlled_exists_fixed_reference_packet
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (h : r2mPrefixQuotientMetricTailControlled N u)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, r2mPrefixQuotientFixedReferencePacket N u ε M := by
  exact r2m_prefix_quotient_zero_centered_tube_controlled_exists_fixed_reference_packet N u
    (r2m_prefix_quotient_metric_tail_controlled_to_zero_centered_tube_controlled N u h)
    ε hε

/-- Completion fixed-reference packet surface: metric Cauchy tail data has been
converted into same-center ε-packets suitable for later completion witnesses. -/
def r2mPrefixQuotientCompletionFixedReferencePacketReady : Prop :=
  r2mPrefixQuotientCompletionZeroCenteredEquivalenceReady ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) (ε : ℝ) (M : ℕ),
    r2mPrefixQuotientFixedReferenceNormPacket N u ε M →
    r2mPrefixQuotientFixedReferenceMetricPacket N u ε M) ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) (ε : ℝ) (M : ℕ),
    r2mPrefixQuotientFixedReferenceMetricPacket N u ε M →
    r2mPrefixQuotientFixedReferenceNormPacket N u ε M) ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
      (h : r2mPrefixQuotientMetricTailControlled N u) (ε : ℝ),
    0 < ε → ∃ M : ℕ, r2mPrefixQuotientFixedReferencePacket N u ε M)

/-- The quotient completion fixed-reference packet surface is ready. -/
theorem r2m_prefix_quotient_completion_fixed_reference_packet_ready :
    r2mPrefixQuotientCompletionFixedReferencePacketReady := by
  refine ⟨
    r2m_prefix_quotient_completion_zero_centered_equivalence_ready,
    r2m_prefix_quotient_fixed_reference_norm_packet_to_metric_packet,
    r2m_prefix_quotient_fixed_reference_metric_packet_to_norm_packet,
    ?_⟩
  intro N u h ε hε
  exact r2m_prefix_quotient_metric_tail_controlled_exists_fixed_reference_packet N u h ε hε

/-- Boundary marker: completion now has fixed-reference ε-packets with metric
and norm estimates sharing the same center. -/
def r2mPrefixQuotientCompletionFixedReferencePacketBoundaryHeld : Prop :=
  r2mPrefixQuotientCompletionFixedReferencePacketReady ∧
  True

theorem r2m_prefix_quotient_completion_fixed_reference_packet_boundary_held :
    r2mPrefixQuotientCompletionFixedReferencePacketBoundaryHeld := by
  exact ⟨r2m_prefix_quotient_completion_fixed_reference_packet_ready, trivial⟩

end

end MathlibAnalytic
end MGAP4D
