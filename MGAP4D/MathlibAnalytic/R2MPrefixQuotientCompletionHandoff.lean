import MGAP4D.MathlibAnalytic.R2MPrefixQuotientNormTailTubeControl

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Metric tail-control predicate for quotient sequences, stated in elementary
ε-tail form to keep the completion handoff independent of later typeclass
completion choices. -/
def r2mPrefixQuotientMetricTailControlled
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ M : ℕ,
    ∀ n m : ℕ, M ≤ n → M ≤ m → dist (u n) (u m) ≤ ε

/-- Scalar norm tail-control predicate induced by the quotient norm. -/
def r2mPrefixQuotientNormTailControlled
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ M : ℕ,
    ∀ n m : ℕ, M ≤ n → M ≤ m → |‖u n‖ - ‖u m‖| ≤ ε

/-- Reference tube predicate for a quotient sequence: after some index `M`, all
norms lie in the ε-tube around the reference norm `‖u M‖`. -/
def r2mPrefixQuotientNormReferenceTubeControlled
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ M : ℕ,
    ∀ n : ℕ, M ≤ n → ‖u M‖ - ε ≤ ‖u n‖ ∧ ‖u n‖ ≤ ‖u M‖ + ε

/-- Metric ε-tail control transports to scalar norm ε-tail control. -/
theorem r2m_prefix_quotient_metric_tail_controlled_to_norm_tail_controlled
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (h : r2mPrefixQuotientMetricTailControlled N u) :
    r2mPrefixQuotientNormTailControlled N u := by
  intro ε hε
  rcases h ε hε with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro n m hn hm
  exact r2m_prefix_quotient_norm_tail_abs_sub_le_of_dist_tail_typeclass N u M ε hM
    n m hn hm

/-- Metric ε-tail control also gives a reference norm tube around the first tail
point. -/
theorem r2m_prefix_quotient_metric_tail_controlled_to_norm_reference_tube_controlled
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (h : r2mPrefixQuotientMetricTailControlled N u) :
    r2mPrefixQuotientNormReferenceTubeControlled N u := by
  intro ε hε
  rcases h ε hε with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro n hn
  exact r2m_prefix_quotient_norm_seq_mem_reference_tube_of_dist_le_typeclass N
    u n M ε (hM n M hn le_rfl)

/-- Bundled completion handoff: a metric-tail-controlled quotient sequence has
both norm-tail control and reference-tube control. -/
theorem r2m_prefix_quotient_metric_tail_controlled_completion_handoff
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (h : r2mPrefixQuotientMetricTailControlled N u) :
    r2mPrefixQuotientNormTailControlled N u ∧
    r2mPrefixQuotientNormReferenceTubeControlled N u := by
  exact ⟨
    r2m_prefix_quotient_metric_tail_controlled_to_norm_tail_controlled N u h,
    r2m_prefix_quotient_metric_tail_controlled_to_norm_reference_tube_controlled N u h⟩

/-- Completion handoff surface: metric Cauchy-tail information has been
transported into scalar norm controls suitable for the later completion and
closed-graph lanes. -/
def r2mPrefixQuotientCompletionHandoffReady : Prop :=
  r2mPrefixQuotientNormTailTubeControlReady ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientMetricTailControlled N u →
    r2mPrefixQuotientNormTailControlled N u) ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientMetricTailControlled N u →
    r2mPrefixQuotientNormReferenceTubeControlled N u) ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientMetricTailControlled N u →
    r2mPrefixQuotientNormTailControlled N u ∧
    r2mPrefixQuotientNormReferenceTubeControlled N u)

/-- The quotient completion handoff surface is ready. -/
theorem r2m_prefix_quotient_completion_handoff_ready :
    r2mPrefixQuotientCompletionHandoffReady := by
  exact ⟨
    r2m_prefix_quotient_norm_tail_tube_control_ready,
    r2m_prefix_quotient_metric_tail_controlled_to_norm_tail_controlled,
    r2m_prefix_quotient_metric_tail_controlled_to_norm_reference_tube_controlled,
    r2m_prefix_quotient_metric_tail_controlled_completion_handoff⟩

/-- Boundary marker: quotient metric-tail data is now ready to be consumed by
completion and closed-graph proof lanes. -/
def r2mPrefixQuotientCompletionHandoffBoundaryHeld : Prop :=
  r2mPrefixQuotientCompletionHandoffReady ∧
  True

theorem r2m_prefix_quotient_completion_handoff_boundary_held :
    r2mPrefixQuotientCompletionHandoffBoundaryHeld := by
  exact ⟨r2m_prefix_quotient_completion_handoff_ready, trivial⟩

end

end MathlibAnalytic
end MGAP4D
