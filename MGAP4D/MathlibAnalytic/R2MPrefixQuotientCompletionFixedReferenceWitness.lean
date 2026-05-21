import MGAP4D.MathlibAnalytic.R2MPrefixQuotientCompletionFixedReferencePacketMonotone

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- A fixed-reference witness is the existential packaging of a same-center
metric/norm packet at tolerance `ε`.  It is intentionally a `Prop`-level witness
surface so later completion layers can consume it without choosing data. -/
def r2mPrefixQuotientFixedReferenceWitness
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) (ε : ℝ) : Prop :=
  ∃ M : ℕ, r2mPrefixQuotientFixedReferencePacket N u ε M

/-- Project the metric part from a fixed-reference witness. -/
theorem r2m_prefix_quotient_fixed_reference_witness_to_metric_witness
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) (ε : ℝ)
    (h : r2mPrefixQuotientFixedReferenceWitness N u ε) :
    ∃ M : ℕ, r2mPrefixQuotientFixedReferenceMetricPacket N u ε M := by
  rcases h with ⟨M, hM⟩
  exact ⟨M, hM.1⟩

/-- Project the norm part from a fixed-reference witness. -/
theorem r2m_prefix_quotient_fixed_reference_witness_to_norm_witness
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) (ε : ℝ)
    (h : r2mPrefixQuotientFixedReferenceWitness N u ε) :
    ∃ M : ℕ, r2mPrefixQuotientFixedReferenceNormPacket N u ε M := by
  rcases h with ⟨M, hM⟩
  exact ⟨M, hM.2⟩

/-- Fixed-reference witnesses are monotone in the tolerance. -/
theorem r2m_prefix_quotient_fixed_reference_witness_mono
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) (ε δ : ℝ)
    (hεδ : ε ≤ δ)
    (h : r2mPrefixQuotientFixedReferenceWitness N u ε) :
    r2mPrefixQuotientFixedReferenceWitness N u δ := by
  rcases h with ⟨M, hM⟩
  exact ⟨M, r2m_prefix_quotient_fixed_reference_packet_mono N u ε δ M hεδ hM⟩

/-- Metric-tail control supplies a fixed-reference witness for every positive
tolerance. -/
theorem r2m_prefix_quotient_metric_tail_controlled_exists_fixed_reference_witness
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (h : r2mPrefixQuotientMetricTailControlled N u)
    (ε : ℝ) (hε : 0 < ε) :
    r2mPrefixQuotientFixedReferenceWitness N u ε := by
  exact r2m_prefix_quotient_metric_tail_controlled_exists_fixed_reference_packet_via_half N u h ε hε

/-- Metric-tail control supplies a half-tolerance fixed-reference witness. -/
theorem r2m_prefix_quotient_metric_tail_controlled_exists_fixed_reference_witness_half
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (h : r2mPrefixQuotientMetricTailControlled N u)
    (ε : ℝ) (hε : 0 < ε) :
    r2mPrefixQuotientFixedReferenceWitness N u (ε / 2) := by
  exact r2m_prefix_quotient_metric_tail_controlled_exists_fixed_reference_packet_half N u h ε hε

/-- A half-tolerance witness upgrades to a full-tolerance witness without
changing the witness reference index internally. -/
theorem r2m_prefix_quotient_fixed_reference_witness_half_to_full
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) (ε : ℝ)
    (hε : 0 < ε)
    (h : r2mPrefixQuotientFixedReferenceWitness N u (ε / 2)) :
    r2mPrefixQuotientFixedReferenceWitness N u ε := by
  have hhalf_le : ε / 2 ≤ ε := by linarith
  exact r2m_prefix_quotient_fixed_reference_witness_mono N u (ε / 2) ε hhalf_le h

/-- Completion fixed-reference witness surface: the fixed-reference packet API
is now packaged as existential witnesses and remains compatible with half-ε
budgeting. -/
def r2mPrefixQuotientCompletionFixedReferenceWitnessReady : Prop :=
  r2mPrefixQuotientCompletionFixedReferencePacketMonotoneReady ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) (ε : ℝ),
    r2mPrefixQuotientFixedReferenceWitness N u ε →
    ∃ M : ℕ, r2mPrefixQuotientFixedReferenceMetricPacket N u ε M) ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) (ε : ℝ),
    r2mPrefixQuotientFixedReferenceWitness N u ε →
    ∃ M : ℕ, r2mPrefixQuotientFixedReferenceNormPacket N u ε M) ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
      (h : r2mPrefixQuotientMetricTailControlled N u) (ε : ℝ),
    0 < ε → r2mPrefixQuotientFixedReferenceWitness N u ε) ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
      (h : r2mPrefixQuotientMetricTailControlled N u) (ε : ℝ),
    0 < ε → r2mPrefixQuotientFixedReferenceWitness N u (ε / 2))

/-- The quotient completion fixed-reference witness surface is ready. -/
theorem r2m_prefix_quotient_completion_fixed_reference_witness_ready :
    r2mPrefixQuotientCompletionFixedReferenceWitnessReady := by
  exact ⟨
    r2m_prefix_quotient_completion_fixed_reference_packet_monotone_ready,
    r2m_prefix_quotient_fixed_reference_witness_to_metric_witness,
    r2m_prefix_quotient_fixed_reference_witness_to_norm_witness,
    r2m_prefix_quotient_metric_tail_controlled_exists_fixed_reference_witness,
    r2m_prefix_quotient_metric_tail_controlled_exists_fixed_reference_witness_half⟩

/-- Boundary marker: completion now has existential fixed-reference witnesses
with paired metric/norm packet projections. -/
def r2mPrefixQuotientCompletionFixedReferenceWitnessBoundaryHeld : Prop :=
  r2mPrefixQuotientCompletionFixedReferenceWitnessReady ∧
  True

theorem r2m_prefix_quotient_completion_fixed_reference_witness_boundary_held :
    r2mPrefixQuotientCompletionFixedReferenceWitnessBoundaryHeld := by
  exact ⟨r2m_prefix_quotient_completion_fixed_reference_witness_ready, trivial⟩

end

end MathlibAnalytic
end MGAP4D
