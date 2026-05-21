import MGAP4D.MathlibAnalytic.R2MPrefixQuotientCompletionReferenceTubeHandoff

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Zero-centered tube control for quotient sequences: after choosing a tail
reference point `u M`, every tail difference `u n - u M` lies within `ε` of zero
both in the installed metric and in the installed quotient norm. -/
def r2mPrefixQuotientZeroCenteredTubeControlled
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ M : ℕ,
    ∀ n : ℕ, M ≤ n →
      dist (u n - u M) 0 ≤ ε ∧ ‖u n - u M‖ ≤ ε

/-- A paired reference metric/norm tube gives the zero-centered version for the
reference differences. -/
theorem r2m_prefix_quotient_reference_metric_norm_tube_controlled_to_zero_centered_tube_controlled
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (h : r2mPrefixQuotientReferenceMetricNormTubeControlled N u) :
    r2mPrefixQuotientZeroCenteredTubeControlled N u := by
  intro ε hε
  rcases h ε hε with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro n hn
  have hnorm : ‖u n - u M‖ ≤ ε := (hM n hn).2
  have hdist0 : dist (u n - u M) 0 ≤ ε := by
    rw [r2m_prefix_quotient_dist_eq_norm_sub_typeclass N (u n - u M) 0]
    simpa using hnorm
  exact ⟨hdist0, hnorm⟩

/-- Metric-tail control gives the zero-centered tube around the first tail
reference point. -/
theorem r2m_prefix_quotient_metric_tail_controlled_to_zero_centered_tube_controlled
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (h : r2mPrefixQuotientMetricTailControlled N u) :
    r2mPrefixQuotientZeroCenteredTubeControlled N u := by
  exact r2m_prefix_quotient_reference_metric_norm_tube_controlled_to_zero_centered_tube_controlled N u
    (r2m_prefix_quotient_metric_tail_controlled_to_reference_metric_norm_tube_controlled N u h)

/-- The zero-centered tube immediately recovers the reference-difference norm
tube by projection. -/
theorem r2m_prefix_quotient_zero_centered_tube_controlled_to_reference_difference_norm_tube_controlled
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (h : r2mPrefixQuotientZeroCenteredTubeControlled N u) :
    r2mPrefixQuotientReferenceDifferenceNormTubeControlled N u := by
  intro ε hε
  rcases h ε hε with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro n hn
  exact (hM n hn).2

/-- Completion zero-centered-tube surface: metric Cauchy tail data can now be
centered at a tail reference point and read as convergence of the difference
sequence to zero in both metric and norm form. -/
def r2mPrefixQuotientCompletionZeroCenteredTubeReady : Prop :=
  r2mPrefixQuotientCompletionReferenceTubeHandoffReady ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientReferenceMetricNormTubeControlled N u →
    r2mPrefixQuotientZeroCenteredTubeControlled N u) ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientMetricTailControlled N u →
    r2mPrefixQuotientZeroCenteredTubeControlled N u) ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientZeroCenteredTubeControlled N u →
    r2mPrefixQuotientReferenceDifferenceNormTubeControlled N u)

/-- The quotient completion zero-centered-tube surface is ready. -/
theorem r2m_prefix_quotient_completion_zero_centered_tube_ready :
    r2mPrefixQuotientCompletionZeroCenteredTubeReady := by
  exact ⟨
    r2m_prefix_quotient_completion_reference_tube_handoff_ready,
    r2m_prefix_quotient_reference_metric_norm_tube_controlled_to_zero_centered_tube_controlled,
    r2m_prefix_quotient_metric_tail_controlled_to_zero_centered_tube_controlled,
    r2m_prefix_quotient_zero_centered_tube_controlled_to_reference_difference_norm_tube_controlled⟩

/-- Boundary marker: the quotient completion lane now has zero-centered tube
control for tail reference differences. -/
def r2mPrefixQuotientCompletionZeroCenteredTubeBoundaryHeld : Prop :=
  r2mPrefixQuotientCompletionZeroCenteredTubeReady ∧
  True

theorem r2m_prefix_quotient_completion_zero_centered_tube_boundary_held :
    r2mPrefixQuotientCompletionZeroCenteredTubeBoundaryHeld := by
  exact ⟨r2m_prefix_quotient_completion_zero_centered_tube_ready, trivial⟩

end

end MathlibAnalytic
end MGAP4D
