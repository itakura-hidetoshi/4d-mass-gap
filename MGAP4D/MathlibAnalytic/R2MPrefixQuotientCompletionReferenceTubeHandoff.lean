import MGAP4D.MathlibAnalytic.R2MPrefixQuotientCompletionReferenceDifferenceTube

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Reference metric tube control for quotient sequences: after a suitable tail
index `M`, every tail point lies within `ε` of the reference point `u M` in the
installed quotient metric. -/
def r2mPrefixQuotientReferenceMetricTubeControlled
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ M : ℕ,
    ∀ n : ℕ, M ≤ n → dist (u n) (u M) ≤ ε

/-- Paired metric/norm reference tube control.  This packages the two equivalent
handoff views used by completion and closed-graph arguments: metric proximity to
the reference point and direct quotient-norm control of the reference difference. -/
def r2mPrefixQuotientReferenceMetricNormTubeControlled
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ M : ℕ,
    ∀ n : ℕ, M ≤ n →
      dist (u n) (u M) ≤ ε ∧ ‖u n - u M‖ ≤ ε

/-- Reference-difference norm tubes can be read back as reference metric tubes
through the installed identity `dist q r = ‖q - r‖`. -/
theorem r2m_prefix_quotient_reference_difference_norm_tube_controlled_to_reference_metric_tube_controlled
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (h : r2mPrefixQuotientReferenceDifferenceNormTubeControlled N u) :
    r2mPrefixQuotientReferenceMetricTubeControlled N u := by
  intro ε hε
  rcases h ε hε with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro n hn
  have hnorm : ‖u n - u M‖ ≤ ε := hM n hn
  rwa [r2m_prefix_quotient_dist_eq_norm_sub_typeclass N (u n) (u M)]

/-- Metric-tail control gives the paired reference metric/norm tube. -/
theorem r2m_prefix_quotient_metric_tail_controlled_to_reference_metric_norm_tube_controlled
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (h : r2mPrefixQuotientMetricTailControlled N u) :
    r2mPrefixQuotientReferenceMetricNormTubeControlled N u := by
  intro ε hε
  rcases h ε hε with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro n hn
  have hdist : dist (u n) (u M) ≤ ε := hM n M hn le_rfl
  have hnorm : ‖u n - u M‖ ≤ ε := by
    rwa [← r2m_prefix_quotient_dist_eq_norm_sub_typeclass N (u n) (u M)]
  exact ⟨hdist, hnorm⟩

/-- The paired reference tube immediately yields its metric projection. -/
theorem r2m_prefix_quotient_reference_metric_norm_tube_controlled_to_reference_metric_tube_controlled
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (h : r2mPrefixQuotientReferenceMetricNormTubeControlled N u) :
    r2mPrefixQuotientReferenceMetricTubeControlled N u := by
  intro ε hε
  rcases h ε hε with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro n hn
  exact (hM n hn).1

/-- The paired reference tube immediately yields its norm-difference projection. -/
theorem r2m_prefix_quotient_reference_metric_norm_tube_controlled_to_reference_difference_norm_tube_controlled
    (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N)
    (h : r2mPrefixQuotientReferenceMetricNormTubeControlled N u) :
    r2mPrefixQuotientReferenceDifferenceNormTubeControlled N u := by
  intro ε hε
  rcases h ε hε with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro n hn
  exact (hM n hn).2

/-- Completion reference-tube handoff surface: tail control is available both as
metric reference tubes and as direct norm-difference reference tubes, with a
paired package for downstream completion and closed-graph layers. -/
def r2mPrefixQuotientCompletionReferenceTubeHandoffReady : Prop :=
  r2mPrefixQuotientCompletionReferenceDifferenceTubeReady ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientReferenceDifferenceNormTubeControlled N u →
    r2mPrefixQuotientReferenceMetricTubeControlled N u) ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientMetricTailControlled N u →
    r2mPrefixQuotientReferenceMetricNormTubeControlled N u) ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientReferenceMetricNormTubeControlled N u →
    r2mPrefixQuotientReferenceMetricTubeControlled N u) ∧
  (∀ (N : ℕ) (u : ℕ → R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientReferenceMetricNormTubeControlled N u →
    r2mPrefixQuotientReferenceDifferenceNormTubeControlled N u)

/-- The quotient completion reference-tube handoff surface is ready. -/
theorem r2m_prefix_quotient_completion_reference_tube_handoff_ready :
    r2mPrefixQuotientCompletionReferenceTubeHandoffReady := by
  exact ⟨
    r2m_prefix_quotient_completion_reference_difference_tube_ready,
    r2m_prefix_quotient_reference_difference_norm_tube_controlled_to_reference_metric_tube_controlled,
    r2m_prefix_quotient_metric_tail_controlled_to_reference_metric_norm_tube_controlled,
    r2m_prefix_quotient_reference_metric_norm_tube_controlled_to_reference_metric_tube_controlled,
    r2m_prefix_quotient_reference_metric_norm_tube_controlled_to_reference_difference_norm_tube_controlled⟩

/-- Boundary marker: the quotient completion lane now exposes a paired
metric/norm reference-tube handoff. -/
def r2mPrefixQuotientCompletionReferenceTubeHandoffBoundaryHeld : Prop :=
  r2mPrefixQuotientCompletionReferenceTubeHandoffReady ∧
  True

theorem r2m_prefix_quotient_completion_reference_tube_handoff_boundary_held :
    r2mPrefixQuotientCompletionReferenceTubeHandoffBoundaryHeld := by
  exact ⟨r2m_prefix_quotient_completion_reference_tube_handoff_ready, trivial⟩

end

end MathlibAnalytic
end MGAP4D
