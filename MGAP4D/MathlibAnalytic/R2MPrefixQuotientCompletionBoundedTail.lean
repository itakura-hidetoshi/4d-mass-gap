import MGAP4D.MathlibAnalytic.R2MPrefixQuotientCompletionHandoff

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Eventual scalar norm boundedness for quotient sequences.  This is the
minimal bounded-tail surface needed before passing from elementary ε-tail
control to completion/closed-graph arguments. -/
def r2mPrefixQuotientNormEventuallyBounded
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) : Prop :=
  ∃ M : ℕ, ∃ C : ℝ,
    0 ≤ C ∧ ∀ n : ℕ, M ≤ n → ‖u n‖ ≤ C

/-- A metric-tail-controlled quotient sequence is eventually norm-bounded.  The
proof chooses the unit tube around the first tail reference point. -/
theorem r2m_prefix_quotient_metric_tail_controlled_to_norm_eventually_bounded
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (h : r2mPrefixQuotientMetricTailControlled N u) :
    r2mPrefixQuotientNormEventuallyBounded N u := by
  rcases h 1 zero_lt_one with ⟨M, hM⟩
  refine ⟨M, ‖u M‖ + 1, ?_, ?_⟩
  · exact add_nonneg (r2m_prefix_quotient_norm_nonneg N (u M)) zero_le_one
  · intro n hn
    exact (r2m_prefix_quotient_norm_seq_mem_reference_tube_of_dist_le_typeclass N
      u n M 1 (hM n M hn le_rfl)).2

/-- Eventual boundedness also follows from the bundled completion handoff. -/
theorem r2m_prefix_quotient_completion_handoff_to_norm_eventually_bounded
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (h : r2mPrefixQuotientMetricTailControlled N u) :
    r2mPrefixQuotientNormEventuallyBounded N u := by
  exact r2m_prefix_quotient_metric_tail_controlled_to_norm_eventually_bounded N u h

/-- Completion bounded-tail surface: metric-tail control now yields scalar norm
Cauchy control, reference-tube control, and eventual norm boundedness. -/
def r2mPrefixQuotientCompletionBoundedTailReady : Prop :=
  r2mPrefixQuotientCompletionHandoffReady ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientMetricTailControlled N u →
    r2mPrefixQuotientNormEventuallyBounded N u) ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientMetricTailControlled N u →
    r2mPrefixQuotientNormTailControlled N u ∧
    r2mPrefixQuotientNormReferenceTubeControlled N u ∧
    r2mPrefixQuotientNormEventuallyBounded N u)

/-- The quotient completion bounded-tail surface is ready. -/
theorem r2m_prefix_quotient_completion_bounded_tail_ready :
    r2mPrefixQuotientCompletionBoundedTailReady := by
  refine ⟨
    r2m_prefix_quotient_completion_handoff_ready,
    r2m_prefix_quotient_metric_tail_controlled_to_norm_eventually_bounded,
    ?_⟩
  intro N u h
  exact ⟨
    r2m_prefix_quotient_metric_tail_controlled_to_norm_tail_controlled N u h,
    r2m_prefix_quotient_metric_tail_controlled_to_norm_reference_tube_controlled N u h,
    r2m_prefix_quotient_metric_tail_controlled_to_norm_eventually_bounded N u h⟩

/-- Boundary marker: the quotient completion lane now has an elementary bounded
norm tail available for later Cauchy/completion realizations. -/
def r2mPrefixQuotientCompletionBoundedTailBoundaryHeld : Prop :=
  r2mPrefixQuotientCompletionBoundedTailReady ∧
  True

theorem r2m_prefix_quotient_completion_bounded_tail_boundary_held :
    r2mPrefixQuotientCompletionBoundedTailBoundaryHeld := by
  exact ⟨r2m_prefix_quotient_completion_bounded_tail_ready, trivial⟩

end

end MathlibAnalytic
end MGAP4D
