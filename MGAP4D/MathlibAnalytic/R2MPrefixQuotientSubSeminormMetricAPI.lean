import MGAP4D.MathlibAnalytic.R2MPrefixQuotientSubSeminormAPI

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The quotient seminorm of the zero difference vanishes. -/
theorem r2m_prefix_quotient_seminorm_sub_self
    (N : ℕ)
    (q : R2MPrefixZeroDistanceQuotient N) :
    r2mPrefixQuotientSeminorm N (r2mPrefixQuotientSub N q q) = 0 := by
  rw [r2m_prefix_quotient_seminorm_sub_eq_distance]
  exact r2m_prefix_quotient_distance_self N q

/-- Symmetry of the quotient seminorm of subtraction. -/
theorem r2m_prefix_quotient_seminorm_sub_symm
    (N : ℕ)
    (q r : R2MPrefixZeroDistanceQuotient N) :
    r2mPrefixQuotientSeminorm N (r2mPrefixQuotientSub N q r) =
      r2mPrefixQuotientSeminorm N (r2mPrefixQuotientSub N r q) := by
  rw [r2m_prefix_quotient_seminorm_sub_eq_distance]
  rw [r2m_prefix_quotient_seminorm_sub_eq_distance]
  exact r2m_prefix_quotient_distance_symm N q r

/-- Triangle inequality in quotient-subtraction seminorm form. -/
theorem r2m_prefix_quotient_seminorm_sub_triangle
    (N : ℕ)
    (q r s : R2MPrefixZeroDistanceQuotient N) :
    r2mPrefixQuotientSeminorm N (r2mPrefixQuotientSub N q s) ≤
      r2mPrefixQuotientSeminorm N (r2mPrefixQuotientSub N q r) +
        r2mPrefixQuotientSeminorm N (r2mPrefixQuotientSub N r s) := by
  rw [r2m_prefix_quotient_seminorm_sub_eq_distance]
  rw [r2m_prefix_quotient_seminorm_sub_eq_distance]
  rw [r2m_prefix_quotient_seminorm_sub_eq_distance]
  exact r2m_prefix_quotient_distance_triangle N q r s

/-- Readiness package for the metric-style quotient subtraction seminorm API. -/
def r2mPrefixQuotientSubSeminormMetricAPIReady : Prop :=
  r2mPrefixQuotientSubSeminormAPIReady ∧
  (∀ (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientSeminorm N (r2mPrefixQuotientSub N q q) = 0) ∧
  (∀ (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientSeminorm N (r2mPrefixQuotientSub N q r) =
      r2mPrefixQuotientSeminorm N (r2mPrefixQuotientSub N r q)) ∧
  (∀ (N : ℕ) (q r s : R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientSeminorm N (r2mPrefixQuotientSub N q s) ≤
      r2mPrefixQuotientSeminorm N (r2mPrefixQuotientSub N q r) +
        r2mPrefixQuotientSeminorm N (r2mPrefixQuotientSub N r s))

/-- The metric-style quotient subtraction seminorm API is ready. -/
theorem r2m_prefix_quotient_sub_seminorm_metric_api_ready :
    r2mPrefixQuotientSubSeminormMetricAPIReady := by
  exact ⟨
    r2m_prefix_quotient_sub_seminorm_api_ready,
    r2m_prefix_quotient_seminorm_sub_self,
    r2m_prefix_quotient_seminorm_sub_symm,
    r2m_prefix_quotient_seminorm_sub_triangle⟩

/-- Boundary marker: quotient subtraction now carries the self-zero, symmetry,
and triangle laws in norm-like form.  Full Mathlib typeclass promotion remains
a separate explicit boundary. -/
def r2mPrefixQuotientSubSeminormMetricAPIBoundaryHeld : Prop :=
  r2mPrefixQuotientSubSeminormMetricAPIReady ∧
  True

theorem r2m_prefix_quotient_sub_seminorm_metric_api_boundary_held :
    r2mPrefixQuotientSubSeminormMetricAPIBoundaryHeld := by
  exact ⟨r2m_prefix_quotient_sub_seminorm_metric_api_ready, trivial⟩

end

end MathlibAnalytic
end MGAP4D
