import MGAP4D.MathlibAnalytic.R2MPrefixQuotientCompletionZeroCenteredTube

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Metric-only zero-centered tube control for reference differences. -/
def r2mPrefixQuotientZeroCenteredMetricTubeControlled
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ M : ℕ,
    ∀ n : ℕ, M ≤ n → dist (u n - u M) 0 ≤ ε

/-- Norm-only zero-centered tube control for reference differences. -/
def r2mPrefixQuotientZeroCenteredNormTubeControlled
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ M : ℕ,
    ∀ n : ℕ, M ≤ n → ‖u n - u M‖ ≤ ε

/-- Norm-only zero-centered tube control transports to metric-only tube control
through the installed identity `dist q 0 = ‖q - 0‖`. -/
theorem r2m_prefix_quotient_zero_centered_norm_tube_controlled_to_metric_tube_controlled
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (h : r2mPrefixQuotientZeroCenteredNormTubeControlled N u) :
    r2mPrefixQuotientZeroCenteredMetricTubeControlled N u := by
  intro ε hε
  rcases h ε hε with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro n hn
  have hnorm : ‖u n - u M‖ ≤ ε := hM n hn
  rw [r2m_prefix_quotient_dist_eq_norm_sub_typeclass N (u n - u M) 0]
  simpa using hnorm

/-- Metric-only zero-centered tube control transports back to norm-only tube
control. -/
theorem r2m_prefix_quotient_zero_centered_metric_tube_controlled_to_norm_tube_controlled
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (h : r2mPrefixQuotientZeroCenteredMetricTubeControlled N u) :
    r2mPrefixQuotientZeroCenteredNormTubeControlled N u := by
  intro ε hε
  rcases h ε hε with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro n hn
  have hdist : dist (u n - u M) 0 ≤ ε := hM n hn
  rw [r2m_prefix_quotient_dist_eq_norm_sub_typeclass N (u n - u M) 0] at hdist
  simpa using hdist

/-- The paired zero-centered tube is equivalent to either one of the two
projections, but we expose it as `metric ∧ norm` so downstream code can consume
both views.  In the reverse direction, a single norm reference point is chosen
and the metric estimate is reconstructed at that same point; this preserves the
center `u M`. -/
theorem r2m_prefix_quotient_zero_centered_tube_controlled_iff_metric_and_norm
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) :
    r2mPrefixQuotientZeroCenteredTubeControlled N u ↔
      r2mPrefixQuotientZeroCenteredMetricTubeControlled N u ∧
      r2mPrefixQuotientZeroCenteredNormTubeControlled N u := by
  constructor
  · intro h
    constructor
    · intro ε hε
      rcases h ε hε with ⟨M, hM⟩
      refine ⟨M, ?_⟩
      intro n hn
      exact (hM n hn).1
    · intro ε hε
      rcases h ε hε with ⟨M, hM⟩
      refine ⟨M, ?_⟩
      intro n hn
      exact (hM n hn).2
  · intro h
    intro ε hε
    rcases h.2 ε hε with ⟨M, hM⟩
    refine ⟨M, ?_⟩
    intro n hn
    have hnorm : ‖u n - u M‖ ≤ ε := hM n hn
    have hdist : dist (u n - u M) 0 ≤ ε := by
      rw [r2m_prefix_quotient_dist_eq_norm_sub_typeclass N (u n - u M) 0]
      simpa using hnorm
    exact ⟨hdist, hnorm⟩

/-- Metric-tail control gives the norm-only zero-centered tube. -/
theorem r2m_prefix_quotient_metric_tail_controlled_to_zero_centered_norm_tube_controlled
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (h : r2mPrefixQuotientMetricTailControlled N u) :
    r2mPrefixQuotientZeroCenteredNormTubeControlled N u := by
  exact r2m_prefix_quotient_zero_centered_tube_controlled_to_reference_difference_norm_tube_controlled N u
    (r2m_prefix_quotient_metric_tail_controlled_to_zero_centered_tube_controlled N u h)

/-- Metric-tail control gives the metric-only zero-centered tube. -/
theorem r2m_prefix_quotient_metric_tail_controlled_to_zero_centered_metric_tube_controlled
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (h : r2mPrefixQuotientMetricTailControlled N u) :
    r2mPrefixQuotientZeroCenteredMetricTubeControlled N u := by
  exact r2m_prefix_quotient_zero_centered_norm_tube_controlled_to_metric_tube_controlled N u
    (r2m_prefix_quotient_metric_tail_controlled_to_zero_centered_norm_tube_controlled N u h)

/-- Completion zero-centered equivalence surface: zero-centered metric and norm
controls are interchangeable, and metric-tail data supplies both. -/
def r2mPrefixQuotientCompletionZeroCenteredEquivalenceReady : Prop :=
  r2mPrefixQuotientCompletionZeroCenteredTubeReady ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientZeroCenteredNormTubeControlled N u →
    r2mPrefixQuotientZeroCenteredMetricTubeControlled N u) ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientZeroCenteredMetricTubeControlled N u →
    r2mPrefixQuotientZeroCenteredNormTubeControlled N u) ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientZeroCenteredTubeControlled N u ↔
      r2mPrefixQuotientZeroCenteredMetricTubeControlled N u ∧
      r2mPrefixQuotientZeroCenteredNormTubeControlled N u) ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientMetricTailControlled N u →
    r2mPrefixQuotientZeroCenteredNormTubeControlled N u ∧
    r2mPrefixQuotientZeroCenteredMetricTubeControlled N u)

/-- The quotient completion zero-centered equivalence surface is ready. -/
theorem r2m_prefix_quotient_completion_zero_centered_equivalence_ready :
    r2mPrefixQuotientCompletionZeroCenteredEquivalenceReady := by
  refine ⟨
    r2m_prefix_quotient_completion_zero_centered_tube_ready,
    r2m_prefix_quotient_zero_centered_norm_tube_controlled_to_metric_tube_controlled,
    r2m_prefix_quotient_zero_centered_metric_tube_controlled_to_norm_tube_controlled,
    r2m_prefix_quotient_zero_centered_tube_controlled_iff_metric_and_norm,
    ?_⟩
  intro N u h
  exact ⟨
    r2m_prefix_quotient_metric_tail_controlled_to_zero_centered_norm_tube_controlled N u h,
    r2m_prefix_quotient_metric_tail_controlled_to_zero_centered_metric_tube_controlled N u h⟩

/-- Boundary marker: zero-centered completion control has a metric/norm
equivalence surface. -/
def r2mPrefixQuotientCompletionZeroCenteredEquivalenceBoundaryHeld : Prop :=
  r2mPrefixQuotientCompletionZeroCenteredEquivalenceReady ∧
  True

theorem r2m_prefix_quotient_completion_zero_centered_equivalence_boundary_held :
    r2mPrefixQuotientCompletionZeroCenteredEquivalenceBoundaryHeld := by
  exact ⟨r2m_prefix_quotient_completion_zero_centered_equivalence_ready, trivial⟩

end

end MathlibAnalytic
end MGAP4D
