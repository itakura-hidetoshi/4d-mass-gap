import MGAP4D.MathlibAnalytic.R2MPrefixQuotientMetricSeparation

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- The quotient seminorm candidate is the quotient distance from the zero
class.  This connects the norm-like and metric-like quotient surfaces. -/
theorem r2m_prefix_quotient_seminorm_eq_distance_zero_class
    (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N) :
    r2mPrefixQuotientSeminorm N q =
      r2mPrefixQuotientDistance N q (r2mPrefixQuotientZeroClass N) := by
  refine Quotient.inductionOn' q ?_
  intro x
  unfold r2mPrefixQuotientZeroClass
  rw [r2m_prefix_quotient_seminorm_mk]
  rw [r2m_prefix_quotient_distance_mk]

/-- The quotient distance from the zero class is the quotient seminorm
candidate. -/
theorem r2m_prefix_quotient_distance_zero_class_eq_seminorm
    (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N) :
    r2mPrefixQuotientDistance N q (r2mPrefixQuotientZeroClass N) =
      r2mPrefixQuotientSeminorm N q := by
  exact (r2m_prefix_quotient_seminorm_eq_distance_zero_class N q).symm

/-- Positive definiteness of the quotient seminorm candidate away from the zero
class. -/
theorem r2m_prefix_quotient_seminorm_pos_iff_ne_zero_class
    (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N) :
    0 < r2mPrefixQuotientSeminorm N q ↔
      q ≠ r2mPrefixQuotientZeroClass N := by
  constructor
  · intro hpos hq
    rw [hq, r2m_prefix_quotient_seminorm_zero_class'] at hpos
    exact (lt_irrefl (0 : ℝ)) hpos
  · intro hne
    have hnonneg := r2m_prefix_quotient_seminorm_nonneg N q
    have hne0 : r2mPrefixQuotientSeminorm N q ≠ 0 := by
      intro hzero
      exact hne ((r2m_prefix_quotient_seminorm_eq_zero_iff N q).mp hzero)
    exact lt_of_le_of_ne' hnonneg hne0

/-- Positive definiteness of the quotient distance away from equality. -/
theorem r2m_prefix_quotient_distance_pos_iff_ne
    (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N) :
    0 < r2mPrefixQuotientDistance N q r ↔ q ≠ r := by
  constructor
  · intro hpos hqr
    rw [hqr, r2m_prefix_quotient_distance_self] at hpos
    exact (lt_irrefl (0 : ℝ)) hpos
  · intro hne
    have hnonneg := r2m_prefix_quotient_distance_nonneg N q r
    have hne0 : r2mPrefixQuotientDistance N q r ≠ 0 := by
      intro hzero
      exact hne ((r2m_prefix_quotient_distance_eq_zero_iff N q r).mp hzero)
    exact lt_of_le_of_ne' hnonneg hne0

/-- Norm-distance bridge readiness: the quotient norm-like function is exactly
distance to zero, and both norm and distance are positive away from their
respective zero/equality loci. -/
def r2mPrefixQuotientNormDistanceBridgeReady : Prop :=
  r2mPrefixQuotientMetricSeparationReady ∧
  (∀ (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientSeminorm N q =
      r2mPrefixQuotientDistance N q (r2mPrefixQuotientZeroClass N)) ∧
  (∀ (N : ℕ) (q : R2MPrefixZeroDistanceQuotient N),
    0 < r2mPrefixQuotientSeminorm N q ↔
      q ≠ r2mPrefixQuotientZeroClass N) ∧
  (∀ (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N),
    0 < r2mPrefixQuotientDistance N q r ↔ q ≠ r)

/-- The quotient norm-distance bridge is ready. -/
theorem r2m_prefix_quotient_norm_distance_bridge_ready :
    r2mPrefixQuotientNormDistanceBridgeReady := by
  exact ⟨
    r2m_prefix_quotient_metric_separation_ready,
    r2m_prefix_quotient_seminorm_eq_distance_zero_class,
    r2m_prefix_quotient_seminorm_pos_iff_ne_zero_class,
    r2m_prefix_quotient_distance_pos_iff_ne⟩

/-- Boundary marker: metric/norm compatibility is closed at the quotient
surface, while quotient add/smul and typeclass promotion remain later layers. -/
def r2mPrefixQuotientAlgebraicStructureBoundaryHeld : Prop :=
  r2mPrefixQuotientNormDistanceBridgeReady ∧
  True

theorem r2m_prefix_quotient_algebraic_structure_boundary_held :
    r2mPrefixQuotientAlgebraicStructureBoundaryHeld := by
  exact ⟨r2m_prefix_quotient_norm_distance_bridge_ready, trivial⟩

end

end MathlibAnalytic
end MGAP4D
