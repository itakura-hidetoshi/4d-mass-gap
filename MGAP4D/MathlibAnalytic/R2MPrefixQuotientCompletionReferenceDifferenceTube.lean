import MGAP4D.MathlibAnalytic.R2MPrefixQuotientCompletionDifferenceBoundedTail

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Reference-difference norm tube control for quotient sequences: after a
suitable tail index `M`, every tail point differs from the reference point `u M`
by at most `ε` in quotient norm.  This is the direct norm form of the metric
Cauchy tail, and is the elementary handoff shape used before completion or
closed-graph limit arguments. -/
def r2mPrefixQuotientReferenceDifferenceNormTubeControlled
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ M : ℕ,
    ∀ n : ℕ, M ≤ n → ‖u n - u M‖ ≤ ε

/-- Metric-tail control gives reference-difference norm tube control.  The proof
is just the mathlib-style bridge `dist q r = ‖q - r‖` applied to the reference
point `u M`. -/
theorem r2m_prefix_quotient_metric_tail_controlled_to_reference_difference_norm_tube_controlled
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (h : r2mPrefixQuotientMetricTailControlled N u) :
    r2mPrefixQuotientReferenceDifferenceNormTubeControlled N u := by
  intro ε hε
  rcases h ε hε with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro n hn
  have hdist : dist (u n) (u M) ≤ ε := hM n M hn le_rfl
  rw [r2m_prefix_quotient_dist_eq_norm_sub_typeclass N (u n) (u M)] at hdist
  exact hdist

/-- Reference-difference tube control implies the coarser eventual boundedness
of reference differences by choosing the unit tube. -/
theorem r2m_prefix_quotient_reference_difference_norm_tube_controlled_to_eventually_bounded
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (h : r2mPrefixQuotientReferenceDifferenceNormTubeControlled N u) :
    r2mPrefixQuotientDifferenceFromReferenceEventuallyBounded N u := by
  rcases h 1 zero_lt_one with ⟨M, hM⟩
  exact ⟨M, 1, zero_le_one, hM⟩

/-- Metric-tail control now supplies both the ε-reference-difference tube and
the bounded reference-difference tail. -/
theorem r2m_prefix_quotient_metric_tail_controlled_to_reference_difference_tube_and_bounded
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (h : r2mPrefixQuotientMetricTailControlled N u) :
    r2mPrefixQuotientReferenceDifferenceNormTubeControlled N u ∧
    r2mPrefixQuotientDifferenceFromReferenceEventuallyBounded N u := by
  have htube : r2mPrefixQuotientReferenceDifferenceNormTubeControlled N u :=
    r2m_prefix_quotient_metric_tail_controlled_to_reference_difference_norm_tube_controlled N u h
  exact ⟨htube,
    r2m_prefix_quotient_reference_difference_norm_tube_controlled_to_eventually_bounded N u htube⟩

/-- Completion reference-difference-tube surface: metric Cauchy tails have been
converted into direct quotient-norm tubes around the first tail reference point. -/
def r2mPrefixQuotientCompletionReferenceDifferenceTubeReady : Prop :=
  r2mPrefixQuotientCompletionDifferenceBoundedTailReady ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientMetricTailControlled N u →
    r2mPrefixQuotientReferenceDifferenceNormTubeControlled N u) ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientReferenceDifferenceNormTubeControlled N u →
    r2mPrefixQuotientDifferenceFromReferenceEventuallyBounded N u) ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientMetricTailControlled N u →
    r2mPrefixQuotientReferenceDifferenceNormTubeControlled N u ∧
    r2mPrefixQuotientDifferenceFromReferenceEventuallyBounded N u)

/-- The quotient completion reference-difference-tube surface is ready. -/
theorem r2m_prefix_quotient_completion_reference_difference_tube_ready :
    r2mPrefixQuotientCompletionReferenceDifferenceTubeReady := by
  exact ⟨
    r2m_prefix_quotient_completion_difference_bounded_tail_ready,
    r2m_prefix_quotient_metric_tail_controlled_to_reference_difference_norm_tube_controlled,
    r2m_prefix_quotient_reference_difference_norm_tube_controlled_to_eventually_bounded,
    r2m_prefix_quotient_metric_tail_controlled_to_reference_difference_tube_and_bounded⟩

/-- Boundary marker: the quotient completion lane now has a direct norm tube
around tail reference points. -/
def r2mPrefixQuotientCompletionReferenceDifferenceTubeBoundaryHeld : Prop :=
  r2mPrefixQuotientCompletionReferenceDifferenceTubeReady ∧
  True

theorem r2m_prefix_quotient_completion_reference_difference_tube_boundary_held :
    r2mPrefixQuotientCompletionReferenceDifferenceTubeBoundaryHeld := by
  exact ⟨r2m_prefix_quotient_completion_reference_difference_tube_ready, trivial⟩

end

end MathlibAnalytic
end MGAP4D
