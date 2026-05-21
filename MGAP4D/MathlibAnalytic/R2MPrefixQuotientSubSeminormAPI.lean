import MGAP4D.MathlibAnalytic.R2MPrefixQuotientDistanceSubBridge
import MGAP4D.MathlibAnalytic.R2MPrefixQuotientNormDistanceBridge

namespace MGAP4D
namespace MathlibAnalytic

noncomputable section

/-- Symmetric API form of the distance/subtraction bridge: the quotient
seminorm of a quotient difference is the quotient distance. -/
theorem r2m_prefix_quotient_seminorm_sub_eq_distance
    (N : ℕ)
    (q r : R2MPrefixZeroDistanceQuotient N) :
    r2mPrefixQuotientSeminorm N (r2mPrefixQuotientSub N q r) =
      r2mPrefixQuotientDistance N q r := by
  exact (r2m_prefix_quotient_distance_eq_seminorm_sub N q r).symm

/-- Nonnegativity of the quotient seminorm of a quotient difference. -/
theorem r2m_prefix_quotient_seminorm_sub_nonneg
    (N : ℕ)
    (q r : R2MPrefixZeroDistanceQuotient N) :
    0 ≤ r2mPrefixQuotientSeminorm N (r2mPrefixQuotientSub N q r) := by
  rw [r2m_prefix_quotient_seminorm_sub_eq_distance]
  exact r2m_prefix_quotient_distance_nonneg N q r

/-- Separation API for quotient subtraction: the quotient seminorm of `q-r`
vanishes exactly when `q = r`. -/
theorem r2m_prefix_quotient_seminorm_sub_eq_zero_iff
    (N : ℕ)
    (q r : R2MPrefixZeroDistanceQuotient N) :
    r2mPrefixQuotientSeminorm N (r2mPrefixQuotientSub N q r) = 0 ↔
      q = r := by
  rw [r2m_prefix_quotient_seminorm_sub_eq_distance]
  exact r2m_prefix_quotient_distance_eq_zero_iff N q r

/-- Strict positivity API for quotient subtraction: the quotient seminorm of
`q-r` is positive exactly away from equality. -/
theorem r2m_prefix_quotient_seminorm_sub_pos_iff_ne
    (N : ℕ)
    (q r : R2MPrefixZeroDistanceQuotient N) :
    0 < r2mPrefixQuotientSeminorm N (r2mPrefixQuotientSub N q r) ↔
      q ≠ r := by
  rw [r2m_prefix_quotient_seminorm_sub_eq_distance]
  exact r2m_prefix_quotient_distance_pos_iff_ne N q r

/-- Readiness package for the quotient subtraction seminorm API. -/
def r2mPrefixQuotientSubSeminormAPIReady : Prop :=
  r2mPrefixQuotientDistanceSubBridgeReady ∧
  r2mPrefixQuotientNormDistanceBridgeReady ∧
  (∀ (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientSeminorm N (r2mPrefixQuotientSub N q r) =
      r2mPrefixQuotientDistance N q r) ∧
  (∀ (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N),
    0 ≤ r2mPrefixQuotientSeminorm N (r2mPrefixQuotientSub N q r)) ∧
  (∀ (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N),
    r2mPrefixQuotientSeminorm N (r2mPrefixQuotientSub N q r) = 0 ↔
      q = r) ∧
  (∀ (N : ℕ) (q r : R2MPrefixZeroDistanceQuotient N),
    0 < r2mPrefixQuotientSeminorm N (r2mPrefixQuotientSub N q r) ↔
      q ≠ r)

/-- The quotient subtraction seminorm API is ready. -/
theorem r2m_prefix_quotient_sub_seminorm_api_ready :
    r2mPrefixQuotientSubSeminormAPIReady := by
  exact ⟨
    r2m_prefix_quotient_distance_sub_bridge_ready,
    r2m_prefix_quotient_norm_distance_bridge_ready,
    r2m_prefix_quotient_seminorm_sub_eq_distance,
    r2m_prefix_quotient_seminorm_sub_nonneg,
    r2m_prefix_quotient_seminorm_sub_eq_zero_iff,
    r2m_prefix_quotient_seminorm_sub_pos_iff_ne⟩

/-- Boundary marker: quotient subtraction is now compatible with the seminorm
as a separated norm-like API.  Promotion to Mathlib typeclasses is still kept
as a later, explicit boundary. -/
def r2mPrefixQuotientSubSeminormAPIBoundaryHeld : Prop :=
  r2mPrefixQuotientSubSeminormAPIReady ∧
  True

theorem r2m_prefix_quotient_sub_seminorm_api_boundary_held :
    r2mPrefixQuotientSubSeminormAPIBoundaryHeld := by
  exact ⟨r2m_prefix_quotient_sub_seminorm_api_ready, trivial⟩

end

end MathlibAnalytic
end MGAP4D
