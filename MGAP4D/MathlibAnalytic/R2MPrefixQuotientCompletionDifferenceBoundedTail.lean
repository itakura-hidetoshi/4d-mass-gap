import MGAP4D.MathlibAnalytic.R2MPrefixQuotientCompletionBoundedTail

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Eventual boundedness of the tail differences from the first tail reference
point.  This is the elementary difference-control form used by later
closed-graph and completion handoff layers. -/
def r2mPrefixQuotientDifferenceFromReferenceEventuallyBounded
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) : Prop :=
  ∃ M : ℕ, ∃ C : ℝ,
    0 ≤ C ∧ ∀ n : ℕ, M ≤ n → ‖u n - u M‖ ≤ C

/-- Metric-tail control gives eventual boundedness of all differences from the
first tail reference point.  We use the unit tail tube and the already installed
quotient identity `dist = norm(sub)`. -/
theorem r2m_prefix_quotient_metric_tail_controlled_to_difference_from_reference_eventually_bounded
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (h : r2mPrefixQuotientMetricTailControlled N u) :
    r2mPrefixQuotientDifferenceFromReferenceEventuallyBounded N u := by
  rcases h 1 zero_lt_one with ⟨M, hM⟩
  refine ⟨M, 1, zero_le_one, ?_⟩
  intro n hn
  have hdist : dist (u n) (u M) ≤ 1 := hM n M hn le_rfl
  simpa [r2m_prefix_quotient_dist_eq_norm_sub_typeclass N (u n) (u M)] using hdist

/-- The same metric-tail hypothesis simultaneously provides eventual
boundedness of the sequence and of its tail differences from a reference point. -/
theorem r2m_prefix_quotient_metric_tail_controlled_to_bounded_and_difference_bounded
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (h : r2mPrefixQuotientMetricTailControlled N u) :
    r2mPrefixQuotientNormEventuallyBounded N u ∧
    r2mPrefixQuotientDifferenceFromReferenceEventuallyBounded N u := by
  exact ⟨
    r2m_prefix_quotient_metric_tail_controlled_to_norm_eventually_bounded N u h,
    r2m_prefix_quotient_metric_tail_controlled_to_difference_from_reference_eventually_bounded N u h⟩

/-- Completion difference-bounded-tail surface: metric tail data now gives both
bounded quotient tails and bounded reference-difference tails. -/
def r2mPrefixQuotientCompletionDifferenceBoundedTailReady : Prop :=
  r2mPrefixQuotientCompletionBoundedTailReady ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientMetricTailControlled N u →
    r2mPrefixQuotientDifferenceFromReferenceEventuallyBounded N u) ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientMetricTailControlled N u →
    r2mPrefixQuotientNormEventuallyBounded N u ∧
    r2mPrefixQuotientDifferenceFromReferenceEventuallyBounded N u)

/-- The quotient completion difference-bounded-tail surface is ready. -/
theorem r2m_prefix_quotient_completion_difference_bounded_tail_ready :
    r2mPrefixQuotientCompletionDifferenceBoundedTailReady := by
  exact ⟨
    r2m_prefix_quotient_completion_bounded_tail_ready,
    r2m_prefix_quotient_metric_tail_controlled_to_difference_from_reference_eventually_bounded,
    r2m_prefix_quotient_metric_tail_controlled_to_bounded_and_difference_bounded⟩

/-- Boundary marker: the quotient completion lane has reference-difference
boundedness available for later closed-graph arguments. -/
def r2mPrefixQuotientCompletionDifferenceBoundedTailBoundaryHeld : Prop :=
  r2mPrefixQuotientCompletionDifferenceBoundedTailReady ∧
  True

theorem r2m_prefix_quotient_completion_difference_bounded_tail_boundary_held :
    r2mPrefixQuotientCompletionDifferenceBoundedTailBoundaryHeld := by
  exact ⟨r2m_prefix_quotient_completion_difference_bounded_tail_ready, trivial⟩

end

end MathlibAnalytic
end MGAP4D
